# Agent & MCP setup snippets for Soft65C02

This folder holds **optional** files you can copy into **your own** project so coding agents know how to drive the **`soft65c02_mcp`** server and the tester DSL—without you writing raw DSL by hand.

## What to install first

1. **Build the MCP binary** from the Soft65C02 repo (or use `cargo run`—see examples below):

   ```bash
   cd /path/to/soft65c02
   cargo build -p soft65c02_mcp --release
   ```

   The binary is typically:

   - **Linux / macOS:** `target/release/soft65c02_mcp`
   - **Windows:** `target\release\soft65c02_mcp.exe`

2. **Keep tester documentation available** to the agent. Easiest options:
   - Work inside a checkout that contains `soft65c02_tester/documentation.md`, or  
   - Copy or symlink `documentation.md` into your project and `@`-mention it in chat, or  
   - Add a rule (below) that points at the doc path on your machine.

## Files in this folder

| File | Purpose |
|------|---------|
| [`AGENTS.md`](AGENTS.md) | Copy to **your project root** (or merge into existing `AGENTS.md`). Tells agents to derive DSL from docs and when to use session vs one-shot tools. |
| [`cursor-mcp.json.example`](cursor-mcp.json.example) | Copy to **`.cursor/mcp.json`** (release **binary** `command`). |
| [`cursor-mcp.cargo-run.json.example`](cursor-mcp.cargo-run.json.example) | Alternative: **`cargo run`** with **`cwd`** set to the Soft65C02 repo. |
| [`rules-soft65c02-mcp.example.mdc`](rules-soft65c02-mcp.example.mdc) | Copy to **`.cursor/rules/`** (e.g. `soft65c02-mcp.mdc`). |
| [`claude_desktop_config.fragment.json`](claude_desktop_config.fragment.json) | Merge into **Claude Desktop** MCP config (see below). |
| [`CLAUDE.md.example`](CLAUDE.md.example) | Optional: copy/rename to **`CLAUDE.md`** at project root for **Claude Code**-style workflows. |

---

## Cursor

### MCP (`mcp.json`)

1. Create `.cursor/` in your project if it does not exist.
2. Copy **`cursor-mcp.json.example`** (binary) or **`cursor-mcp.cargo-run.json.example`** (Cargo) to **`.cursor/mcp.json`**.
3. Replace **`/absolute/path/to/soft65c02`** with your real checkout path.
4. **Restart Cursor** so MCP reloads.

**Alternative:** Cursor **Settings → MCP → Add server** and enter the same `command` / `args` / `cwd` as in the JSON.

### Agent instructions

- Copy **`AGENTS.md`** to your repo root (Cursor and many tools pick it up).
- Optionally add **`rules-soft65c02-mcp.example.mdc`** as `.cursor/rules/soft65c02-mcp.mdc` and edit the `description`, `globs`, and paths.

### Note on `call_mcp_tool` / server id

In some Cursor builds, programmatic MCP calls require the internal **`serverIdentifier`**, not the display name `soft65c02`. If a tool call fails with “server does not exist”, check `~/.cursor/projects/<workspace-slug>/mcps/*/SERVER_METADATA.json` for the correct `serverIdentifier`. The example rule file mentions this.

---

## Claude Desktop (Anthropic app)

Config file location:

| OS | Path |
|----|------|
| **macOS** | `~/Library/Application Support/Claude/claude_desktop_config.json` |
| **Windows** | `%APPDATA%\Claude\claude_desktop_config.json` |
| **Linux** | `~/.config/Anthropic/claude_desktop_config.json` |

1. Open the file (create it if missing). Valid JSON is required.
2. Merge the contents of **`claude_desktop_config.fragment.json`** into the top-level object: ensure you have an **`mcpServers`** key; if it already exists, add the **`soft65c02`** entry alongside existing servers.
3. Use an **absolute path** to `soft65c02_mcp` (or `cargo` + `args` + `cwd` as in the Cursor example).
4. **Fully quit and restart** Claude Desktop.

Security: MCP runs a local process with the privileges of the app; only add servers you trust.

---

## Claude Code (CLI) / other MCP clients

- Many clients use the same **stdio** pattern: **`command`** + optional **`args`** + optional **`cwd`**.
- Copy the structure from `cursor-mcp.json.example` or `claude_desktop_config.fragment.json` into your client’s MCP settings.
- For **Claude Code**, if your version supports MCP via project config, mirror the same `mcpServers` entry; also copy **`CLAUDE.md.example`** to **`CLAUDE.md`** and adjust paths.

---

## Trying it in an agent chat

After MCP shows as connected:

1. Ask in **natural language** (you do not need to paste DSL): e.g. “Load this binary at `#0x2000`, map ROM at `#0x8000`, then run from `#0x200`.”
2. Ask the agent to **read** `soft65c02_tester/documentation.md` (or your copy) and **compose** the DSL for `dsl_session_execute` or `dsl_execute`.
3. Prefer **`dsl_session_execute`** for multi-step debugging (state persists). Use **`dsl_execute`** for isolated one-shot scripts.
4. Use **`dsl_session_checkpoint_export`** / **`_import`** or the file variants when you need to survive restarts.

---

## Platform path hints

- **Windows:** In JSON, escape backslashes (`"C:\\Users\\you\\soft65c02\\..."`) or use forward slashes where your shell accepts them.
- **Spaces in paths:** Quote correctly in the outer shell; inside JSON, a single string is enough: `"/path/with spaces/soft65c02_mcp"`.

---

## License

Same as the parent Soft65C02 repository (see repo root).
