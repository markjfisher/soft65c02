# Soft65C02 Tester DSL Quick Reference

## Comments
```
// C-style comment
; Assembly-style comment
```

## Markers (Test Plans)
```
marker $$test description$$
```
Starts a new test plan with fresh state.

---

## Memory Commands

### Memory Flush
```
memory flush
```
Reset to default flat 64 KiB RAM (all `0x00`). Removes any ROM overlays from `memory load rom`.

### Memory Load
```
memory load #0x1234 "file.bin"          // Load at specific address (writable RAM)
memory load atari "program.xex"         // Load Atari binary (honors segments)
memory load apple "program.com"         // Load Apple Single format
memory load $symbol "file.bin"          // Load at symbol address
```

### Memory Load ROM (read-only)
```
memory load rom #0xE000 "bios.bin"     // Mount file as ROM — reads use ROM, writes fail
```
Use after `memory load`/writes for mutable RAM. ROM must fit in 16-bit space (`addr` + file size ≤ `#0x10000`).

### Memory Map Show
```
memory map show                         // Subsystems (RAM, ROM_#0x…) and address ranges
```

### Memory Write
```
memory write #0x1234 0x(01,02,03)       // Write bytes
memory write $symbol 0x(a9,c0)          // Write to symbol
memory write #0x1000 "hello\0"          // Write string
memory write #0x2000 "data:\xFF\x00"    // String with hex escapes
memory write $dest $src_address         // Write address as 2 bytes (little-endian)
memory write #0x1000 "\                 // Multi-line string
+-------+\
| Hello |\
+-------+"
```

### Memory Fill
```
memory fill #0x1000~#0x1FFF             // Fill with 0x00 (default)
memory fill #0x1000~#0x1FFF 0x42        // Fill with specific value
memory fill $array~$array+0xFF 0x00     // Fill using symbols
memory fill $data+2~$data+5 0xFF        // Fill with offsets
```

### Memory Show
```
memory show #0x1000 0x10                // Show 16 bytes
memory show $data 0x100                 // Show 256 bytes from symbol
memory show $array+2 0x08               // Show with offset
memory show #0x2000 0x20 $$cache$$      // Show with description
memory show #0x1000 0x20 8              // Show with custom width (8 bytes/line)
memory show $data 0x40 4 $$table$$      // Show with width and description
```

---

## Register Commands

### Register Flush
```
registers flush
```
Reset all registers to default state.

### Register Set
```
registers set A = 0x42                  // Set 8-bit register (hex)
registers set X = 192                   // Set 8-bit register (decimal)
registers set Y = 0b11110000            // Set 8-bit register (binary)
registers set CP = 0x1234               // Set 16-bit register
registers set cycle_count = 0           // Reset cycle counter
registers set A = $symbol               // Set from symbol (must be ≤ 0xFF)
registers set A = <$symbol              // Set to low byte of symbol
registers set X = >$symbol              // Set to high byte of symbol
```

**8-bit registers:** `A`, `X`, `Y`, `SP`, `S`  
**16-bit registers:** `CP`  
**Special:** `cycle_count`

### Register Show
```
registers show                          // Show all registers
registers show A                        // Show accumulator only
registers show cycle_count              // Show cycle count only
```

---

## Symbol Commands

### Symbol Load
```
symbols load "symbols.txt"              // Load VICE format symbols
```

### Symbol Add
```
symbols add my_var = 0x1234             // Add 16-bit symbol
symbols add flag = 0x42                 // Add 8-bit symbol
symbols add alias = $other_symbol       // Add symbol referencing another
```

### Symbol Remove
```
symbols remove my_var                   // Remove symbol from table
```

### Symbol References
```
$symbol                                 // Full symbol address
<$symbol                                // Low byte (LSB) of symbol
>$symbol                                // High byte (MSB) of symbol
```

---

## Run Commands

### Basic Run
```
run                                     // Execute one instruction at CP
run #0x1234                             // Execute at specific address
run $symbol                             // Execute at symbol address
run init                                // Execute at init vector (0xFFFC-D)
```

Unimplemented / invalid opcode (or running into **data** as code): run ends with **TerminatedRun** and **PC unchanged**. **Interactive TTY:** inspect / **`run`** again without **`marker`**. **Scripts:** further commands wait until **`marker`** (or use interactive stdin for debugging).

### Run Until Condition
```
run until A = 0x42                      // Run until condition is true
run until X != 0                        // Run until X is non-zero
run until cycle_count > 0x100           // Run until cycle limit
run until $counter = 0xFF               // Run until memory matches
run #0x1000 until A = 0x42              // Run from address until condition
```

### Run While Condition
```
run while X < 0x80                      // Run while condition is true
run while A = 0x42                      // Run while A equals value
run while cycle_count < 256             // Run while under cycle limit
run #0x1000 while X != 0                // Run from address while condition
```

---

## Assert Commands

### Basic Assertions
```
assert A = 0x42 $$description$$          // Assert register value
assert X >= 0x10 $$description$$         // Assert with comparison
assert #0x1234 = 0xFF $$description$$    // Assert memory value
assert $symbol != 0 $$description$$      // Assert symbol memory
assert cycle_count < 300 $$description$$ // Assert cycle count
```

### Memory Sequence Assertions
```
assert #0x1000 ~ 0x(01,02,03) $$description$$           // Assert byte sequence
assert $data ~ "hello\0" $$description$$                // Assert string
assert $array+2 ~ 0x(04,05) $$description$$             // Assert with offset
assert #0x1000 ~ "data:\xFF\x00" $$description$$        // String with hex escapes
```

### Pointer Assertions
```
assert $ptr -> $target $$description$$                  // Assert pointer points to target
assert $ptr -> $target + 0x20 $$description$$           // Assert with offset
assert $entry -> $cache - 32 $$description$$            // Assert with negative offset
```

### Symbol Byte Assertions
```
assert A = <$symbol $$description$$                     // Assert low byte
assert X = >$symbol $$description$$                     // Assert high byte
assert $mem_lo = <$address $$description$$              // Memory contains low byte
assert $mem_hi = >$address $$description$$              // Memory contains high byte
```

### Logical Operators
```
assert A = 0x42 AND X = 0x10 $$description$$            // Both must be true
assert A = 0x42 OR X = 0x10 $$description$$             // At least one true
assert NOT A = 0x42 $$description$$                     // Negation
assert (A = 0x42 AND X < 0x10) OR Y > 0x20 $$desc$$     // Complex with parentheses
```

---

## Disassemble Command
```
disassemble #0x1000 0x20                // Disassemble 32 bytes from address
disassemble $main 0x1D                  // Disassemble from symbol
```

---

## Control Commands

### Enable/Disable Trace Logging
```
enable trace_logging                    // Enable verbose trace output
disable trace_logging                   // Disable verbose trace output
```

---

## Value Formats

### Hexadecimal
```
0x42        // 8-bit hex
0xF         // Short form (single digit)
0x1234      // 16-bit hex
```

### Decimal
```
42          // Decimal value
256         // Works for any size
```

### Binary
```
0b11110000  // 8-bit binary (only for 8-bit values)
```

---

## Address Syntax

### Direct Addresses
```
#0x1234     // Hex address
#0xF        // Short form allowed
```

### Symbol Addresses
```
$symbol                 // Symbol address
$symbol + 0x10          // Symbol with positive offset
$symbol - 32            // Symbol with negative offset (decimal)
<$symbol                // Low byte of symbol address
>$symbol                // High byte of symbol address
```

---

## Operators

### Comparison Operators
```
=           // Equal
!=          // Not equal
>           // Greater than
<           // Less than
>=          // Greater or equal
<=          // Less or equal
```

### Logical Operators
```
AND         // Logical AND
OR          // Logical OR
NOT         // Logical NOT
```

### Memory Operators
```
~           // Memory sequence match
->          // Pointer assertion
```

---

## String Escape Sequences

### Standard Escapes
```
\n          // Newline
\r          // Carriage return
\t          // Tab
\0          // Null terminator
\"          // Quote
\\          // Backslash
\           // Line continuation (at end of line)
```

### Hex Escapes
```
\xFF        // Hex byte value (two digits required)
\x0A        // Newline as hex
\x00        // Null as hex
```

---

## Tester binary (CLI)

```
soft65c02_tester [OPTIONS]              // default: read script from stdin (-)
soft65c02_tester -i script.txt             // shorthand for --input-filepath
```

| Option | Effect |
|--------|--------|
| **`-c`** / `--continue-on-failure` | Keep running after failed **assertions**, and **skip bad lines** instead of exiting (each parse error prints `Parse error (line skipped): …`). |
| **`-v`** / `--verbose` | Print setup / disassembly-style output, not only assertions. |
| **`-p`** / `--parse` | Parse script only, no execution. |

**Parse errors:** With **`-c`**, or when input is **stdin** and it is an **interactive terminal** (you typed into the tester directly), malformed lines are skipped with a warning — the process keeps running. **Piped stdin** or **`-i` file** stop on the first bad line unless you pass **`-c`**.

**Memory errors** (e.g. `memory write` into **ROM**): the line is skipped with `Command error (line skipped): …`; the session keeps going (unlike a bare `Error:` exit).

**TerminatedRun** (bad opcode, cycle cap, etc.): With **interactive stdin + TTY**, you can keep issuing **`registers show`**, **`memory show`**, **`run`** — no **`marker`** needed. With **piped stdin** or **`-i` file** input, commands still freeze until **`marker`** (scripted test isolation).

---

## Quick Examples

### Setup and Test Pattern
```
marker $$test my function$$
symbols load "symbols.txt"
memory load atari "program.xex"
registers flush
registers set CP = $main
run until A = 0x42
assert X = 0x00 $$X should be zero$$
```

### Testing Pointer Setup
```
symbols add buffer = 0x2000
registers set A = <$buffer
registers set X = >$buffer
run $setup_pointer
assert $ptr_lo = <$buffer $$low byte stored$$
assert $ptr_hi = >$buffer $$high byte stored$$
```

### Memory Pattern Testing
```
memory fill $array~$array+0xFF 0x00
memory write $array 0x(01,02,03)
assert $array ~ 0x(01,02,03) $$first 3 bytes$$
assert $array+3 = 0x00 $$rest is zero$$
```

### Cycle Count Testing
```
registers set cycle_count = 0
run $function
assert cycle_count < 300 $$under cycle budget$$
```

### ROM overlay
```
memory flush
memory load #0x0000 "ram_image.bin"
memory load rom #0xE000 "rom.bin"
memory map show                         // sanity-check regions
run #0x0800                             // ROM range is not writable via memory write
```