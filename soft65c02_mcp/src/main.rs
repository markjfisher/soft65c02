//! MCP stdio server: exposes tools to run and parse the `soft65c02_tester` DSL.

use std::io::{BufRead, Cursor};
use std::sync::mpsc::channel;

use rmcp::{
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    tool, tool_handler, tool_router,
    ServerHandler, ServiceExt,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use soft65c02_tester::{
    CommandIterator, Executor, ExecutorConfiguration, OutputToken,
};

const MEMORY_ROM_HINT: &str = r#"ROM overlay (read-only for CPU and memory write/fill):
  memory load rom #0xE000 "/path/to.bin"
  memory map show
Normal file load into RAM (writable):
  memory load #0x1000 "prog.bin"
Reset (drops ROM regions):
  memory flush
See soft65c02_tester/documentation.md for the full command set."#;

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
/// Body for `dsl_execute` / `dsl_parse`.
pub struct DslScript {
    /// One or more DSL lines (newline-separated), same syntax as the tester CLI.
    pub dsl: String,
}

#[derive(Debug, Clone)]
pub struct Soft65Mcp {
    tool_router: ToolRouter<Self>,
}

impl Soft65Mcp {
    pub fn new() -> Self {
        Self {
            tool_router: Self::tool_router(),
        }
    }
}

#[tool_router]
impl Soft65Mcp {
    #[tool(
        description = "Execute tester DSL lines (memory, registers, run, assert). Collects all OutputToken results; STATUS is \"error\" if the executor returned an error (e.g. failed assertions counted at end)."
    )]
    async fn dsl_execute(&self, body: Parameters<DslScript>) -> String {
        let cfg = ExecutorConfiguration {
            stop_on_failed_assertion: false,
            ..ExecutorConfiguration::default()
        };
        run_dsl(&body.0.dsl, cfg)
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
