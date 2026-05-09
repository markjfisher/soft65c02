//! Spawns the real `soft65c02_mcp` binary and verifies a minimal MCP conversation over stdio.
//! Regression: `main` must await [`RunningService::waiting`](rmcp::RunningService::waiting); if the
//! handle is dropped immediately after `serve().await`, the background IO task is cancelled and only
//! `initialize` completes.

use std::process::Stdio;
use std::time::Duration;

use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::Command;

#[tokio::test]
async fn initialize_then_ping_returns_second_response() {
    let exe = env!("CARGO_BIN_EXE_soft65c02_mcp");
    let mut child = Command::new(exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn soft65c02_mcp");

    let mut stdin = child.stdin.take().expect("stdin");
    let stdout = child.stdout.take().expect("stdout");
    let mut reader = BufReader::new(stdout);
    let mut line = String::new();

    let init = concat!(
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":"#,
        r#"{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"t","version":"1"}}}"#,
        "\n",
    );
    stdin.write_all(init.as_bytes()).await.unwrap();
    stdin.flush().await.unwrap();

    line.clear();
    reader.read_line(&mut line).await.unwrap();
    assert!(
        line.contains("\"id\":1"),
        "expected initialize response, got: {line:?}"
    );

    let ping = "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"ping\"}\n";
    stdin.write_all(ping.as_bytes()).await.unwrap();
    stdin.flush().await.unwrap();

    line.clear();
    let read2 = tokio::time::timeout(Duration::from_secs(3), reader.read_line(&mut line))
        .await
        .expect("timeout waiting for ping response")
        .expect("read_line io");

    assert!(
        read2 > 0 && line.contains("\"id\":2"),
        "expected ping response on second line, read={read2} line={line:?}"
    );

    drop(stdin);
    let _ = child.wait().await;
}
