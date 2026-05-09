//! MCP stdio server: exposes tools to run and parse the `soft65c02_tester` DSL.
//!
//! **Stateful session**: `dsl_session_*` tools share one [`ExecutorSession`] (registers, RAM/ROM,
//! symbols) across calls for investigative workflows. **`dsl_execute`** remains one-shot (cold
//! machine each time). Checkpoints use bincode [`SessionCheckpoint`] (format
//! [`SESSION_FORMAT_VERSION`]) for restart survival; rollbacks / per-instruction deltas are not
//! implemented yet.

use std::io::{BufRead, Cursor};
use std::sync::mpsc::channel;
use std::sync::{Arc, Mutex};

use base64::engine::general_purpose::STANDARD as B64;
use base64::Engine;
use rmcp::{
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    tool, tool_handler, tool_router,
    ServerHandler, ServiceExt,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use soft65c02_tester::{
    decode_session_checkpoint, encode_session_checkpoint, CommandIterator, Executor,
    ExecutorConfiguration, ExecutorSession, OutputToken, SESSION_FORMAT_VERSION,
};

const MEMORY_ROM_HINT: &str = r#"ROM overlay (read-only for CPU and memory write/fill):
  memory load rom #0xE000 "/path/to.bin"
  memory map show
Normal file load into RAM (writable):
  memory load #0x1000 "prog.bin"
Reset (drops ROM regions):
  memory flush
See soft65c02_tester/documentation.md for the full command set."#;

fn default_session_configuration() -> ExecutorConfiguration {
    ExecutorConfiguration {
        stop_on_failed_assertion: false,
        allow_commands_after_terminated_run: true,
        ..Default::default()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
/// Body for `dsl_execute` / `dsl_parse`.
pub struct DslScript {
    /// One or more DSL lines (newline-separated), same syntax as the tester CLI.
    pub dsl: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct CheckpointBlob {
    /// Standard base64 (padding optional) of bincode [`SessionCheckpoint`] bytes.
    pub checkpoint_base64: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct CheckpointPath {
    /// Absolute or workspace path to read/write the checkpoint file (raw bincode bytes).
    pub path: String,
}

#[derive(Debug, Clone)]
pub struct Soft65Mcp {
    tool_router: ToolRouter<Self>,
    session: Arc<Mutex<ExecutorSession>>,
}

impl Soft65Mcp {
    pub fn new() -> Self {
        Self {
            tool_router: Self::tool_router(),
            session: Arc::new(Mutex::new(ExecutorSession::new(
                default_session_configuration(),
            ))),
        }
    }
}

#[tool_router]
impl Soft65Mcp {
    #[tool(
        description = "Execute tester DSL lines on a FRESH machine each call (stateless). Collects OutputToken results; STATUS is \"error\" if the executor returned an error."
    )]
    async fn dsl_execute(&self, body: Parameters<DslScript>) -> String {
        let cfg = ExecutorConfiguration {
            stop_on_failed_assertion: false,
            ..ExecutorConfiguration::default()
        };
        run_dsl(&body.0.dsl, cfg)
    }

    #[tool(
        description = "Execute DSL against the PERSISTENT MCP session (same CPU/memory/symbols as prior dsl_session_execute calls). Designed for halted-emulator investigation; uses allow_commands_after_terminated_run. Does not affect dsl_execute."
    )]
    async fn dsl_session_execute(&self, body: Parameters<DslScript>) -> String {
        let mut session = self.session.lock().unwrap();
        run_session_chunk(&mut session, &body.0.dsl)
    }

    #[tool(description = "Reset the persistent session to a fresh machine (same defaults as server start).")]
    async fn dsl_session_reset(&self) -> String {
        let mut session = self.session.lock().unwrap();
        *session = ExecutorSession::new(default_session_configuration());
        "STATUS ok\nsession reset".to_string()
    }

    #[tool(
        description = "Serialize the current session to base64 bincode (format SESSION_FORMAT_VERSION). Use for restart survival or passing state across MCP reconnects when combined with dsl_session_checkpoint_import."
    )]
    async fn dsl_session_checkpoint_export(&self) -> String {
        let session = self.session.lock().unwrap();
        let cp = session.to_checkpoint();
        drop(session);
        match encode_session_checkpoint(&cp) {
            Ok(bytes) => {
                let b64 = B64.encode(bytes);
                format!(
                    "STATUS ok\nformat_version={SESSION_FORMAT_VERSION}\n{b64}"
                )
            }
            Err(e) => format!("STATUS error: {e:#}"),
        }
    }

    #[tool(
        description = "Replace the persistent session from base64 bincode produced by dsl_session_checkpoint_export."
    )]
    async fn dsl_session_checkpoint_import(&self, body: Parameters<CheckpointBlob>) -> String {
        let bytes = match B64.decode(body.0.checkpoint_base64.trim()) {
            Ok(b) => b,
            Err(e) => return format!("STATUS error: base64 decode: {e}"),
        };
        let cp = match decode_session_checkpoint(&bytes) {
            Ok(c) => c,
            Err(e) => return format!("STATUS error: checkpoint decode: {e:#}"),
        };
        let restored = match ExecutorSession::from_checkpoint(cp) {
            Ok(s) => s,
            Err(e) => return format!("STATUS error: restore session: {e:#}"),
        };
        *self.session.lock().unwrap() = restored;
        "STATUS ok\nsession replaced from checkpoint".to_string()
    }

    #[tool(description = "Write the current session checkpoint to a file (raw bincode bytes).")]
    async fn dsl_session_checkpoint_write_file(&self, body: Parameters<CheckpointPath>) -> String {
        let session = self.session.lock().unwrap();
        let cp = session.to_checkpoint();
        drop(session);
        match encode_session_checkpoint(&cp) {
            Ok(bytes) => match std::fs::write(&body.0.path, bytes) {
                Ok(()) => format!(
                    "STATUS ok\nwrote {} bytes to {}",
                    std::fs::metadata(&body.0.path)
                        .map(|m| m.len())
                        .unwrap_or(0),
                    body.0.path
                ),
                Err(e) => format!("STATUS error: write: {e}"),
            },
            Err(e) => format!("STATUS error: encode: {e:#}"),
        }
    }

    #[tool(description = "Load a session checkpoint from a file (raw bincode) into the persistent session.")]
    async fn dsl_session_checkpoint_read_file(&self, body: Parameters<CheckpointPath>) -> String {
        let bytes = match std::fs::read(&body.0.path) {
            Ok(b) => b,
            Err(e) => return format!("STATUS error: read: {e}"),
        };
        let cp = match decode_session_checkpoint(&bytes) {
            Ok(c) => c,
            Err(e) => return format!("STATUS error: checkpoint decode: {e:#}"),
        };
        let restored = match ExecutorSession::from_checkpoint(cp) {
            Ok(s) => s,
            Err(e) => return format!("STATUS error: restore session: {e:#}"),
        };
        *self.session.lock().unwrap() = restored;
        format!("STATUS ok\nsession loaded from {}", body.0.path)
    }

    #[tool(
        description = "Parse DSL only (no execution). Fails with the first parse error line."
    )]
    async fn dsl_parse(&self, body: Parameters<DslScript>) -> String {
        match parse_dsl_line_count(&body.0.dsl) {
            Ok(n) => format!("ok: parsed {n} command(s)"),
            Err(e) => format!("parse error: {e:#}"),
        }
    }

    #[tool(description = "Built-in hint for ROM-related memory commands.")]
    async fn dsl_memory_rom_reference(&self) -> String {
        MEMORY_ROM_HINT.to_string()
    }
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for Soft65Mcp {}

fn format_token(t: &OutputToken) -> String {
    match t {
        OutputToken::None => "(none)".to_string(),
        OutputToken::Marker { description } => format!("marker: {description}"),
        OutputToken::ParseError { message } => format!("PARSE ERROR: {message}"),
        OutputToken::ExecutionError { message } => format!("EXECUTION ERROR: {message}"),
        OutputToken::Setup(lines) => lines.join("\n"),
        OutputToken::View(lines) => lines.join("\n"),
        OutputToken::Help(lines) => lines.join("\n"),
        OutputToken::Assertion { failure, description } => {
            if let Some(msg) = failure {
                format!("ASSERT FAIL {description}: {msg}")
            } else {
                format!("ASSERT OK {description}")
            }
        }
        OutputToken::Run {
            loglines,
            symbols: _,
        } => {
            format!("run: {} instruction log line(s)", loglines.len())
        }
        OutputToken::TerminatedRun {
            loglines,
            symbols: _,
            reason,
        } => {
            format!(
                "run terminated ({reason}): {} log line(s)",
                loglines.len()
            )
        }
        OutputToken::ControlAction { function, enabled } => {
            format!("control: {function} enabled={enabled}")
        }
    }
}

fn run_dsl(dsl: &str, cfg: ExecutorConfiguration) -> String {
    let (tx, rx) = channel::<OutputToken>();
    let executor = Executor::new(cfg);
    let res = executor.run(Cursor::new(dsl.as_bytes()), tx);
    collect_run_output(res, rx)
}

fn run_session_chunk(session: &mut ExecutorSession, dsl: &str) -> String {
    let (tx, rx) = channel::<OutputToken>();
    let res = session.run_chunk(Cursor::new(dsl.as_bytes()), &tx);
    collect_run_output(res, rx)
}

fn collect_run_output(
    res: soft65c02_tester::AppResult<()>,
    rx: std::sync::mpsc::Receiver<OutputToken>,
) -> String {
    let mut blocks = Vec::new();
    while let Ok(tok) = rx.recv() {
        blocks.push(format_token(&tok));
    }
    let body = blocks.join("\n---\n");
    match res {
        Ok(_) => format!("STATUS ok\n{body}"),
        Err(e) => format!("STATUS error: {e:#}\n{body}"),
    }
}

fn parse_dsl_line_count(dsl: &str) -> soft65c02_tester::AppResult<usize> {
    let mut count = 0usize;
    for item in CommandIterator::new(Cursor::new(dsl.as_bytes()).lines()) {
        let _cmd = item?;
        count += 1;
    }
    Ok(count)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let service = Soft65Mcp::new();
    let transport = rmcp::transport::stdio();
    let _running = service.serve(transport).await?;
    Ok(())
}
