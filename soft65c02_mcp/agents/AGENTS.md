# Soft65C02 MCP — agent instructions

When the user wants to **exercise the 65C02 emulator** via MCP (load memory, ROM, run, assert, inspect), **you** compose the tester **DSL**; the user should not have to spell out `memory load`, `run`, etc. unless they choose to.

## Ground truth for DSL syntax

Prefer the Soft65C02 **`soft65c02_tester/documentation.md`** (in this repo or a path the user points you to). Use **`rules.pest`** only if you need grammar-level detail.

Derive commands from docs: `memory load`, `memory load rom`, `run`, `registers`, `memory show`, `disassemble`, `assert`, `symbols`, `marker`, `help`, etc.

## Which MCP tool to call

- **`dsl_session_execute`** — **Persistent** machine state across calls. Use for multi-step investigation (halted CPU, then `registers show`, `memory show`, another `run`, …). Matches interactive “keep going after `TerminatedRun`” behavior.
- **`dsl_execute`** — **Stateless**: fresh RAM/registers every call. Use for one-off scripts or reproducible snippets.
- **`dsl_session_reset`** — Start a new session (clear persistent state).
- **Checkpoints** — `dsl_session_checkpoint_export` / `_import` (base64) or `_write_file` / `_read_file` (raw bytes) for **restart survival** or handoff between sessions.
- **`dsl_parse`** — Validate DSL without running.
- **`dsl_memory_rom_reference`** — Short ROM vs RAM hint text.

Pass DSL as a **single string**; separate lines with **newlines** inside that string.

## Natural language → DSL

When the user says things like “load this file at 0x2000”, “put the ROM at 0x8000”, “run the binary from 0x200”:

1. Infer **format** (raw vs Atari vs Apple Single) from path, extension, or ask one clarifying question if ambiguous—**documentation.md** describes `memory load atari`, `memory load apple`, and `memory load #addr "file"`.
2. Use **`memory load rom #0x.... "path"`** for read-only ROM images.
3. Use **`run #0x....`** or **`run init`** with **`until` / `while`** when they specify stop conditions.
4. Prefer **forward slashes** in quoted paths when possible (Windows accepts them in the tester’s quoted filenames).

## Session discipline

- For long investigations, prefer **`dsl_session_execute`** and occasional **checkpoints** so state is not lost if the MCP host restarts.
- After **`dsl_session_checkpoint_import`**, continue with **`dsl_session_execute`** unless the user asks for a cold run.

## On failure

If a tool returns **`STATUS error`**, read the body (assertion counts, parse errors, execution errors). Suggest the next DSL step (e.g. `memory map show`, `disassemble`, fix address) rather than asking the user to write DSL verbatim.
