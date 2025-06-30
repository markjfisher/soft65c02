# Soft65C02 Graphics Module

Graphics display backends for the Soft65C02 processor emulator.

## Overview

The `soft65c02_graphics` crate provides display backends for the Soft65C02 processor emulator. It implements memory-mapped graphics that emulate how real 8-bit computers handled video output - by treating display memory as addressable I/O.

This crate was separated from the core `soft65c02_lib` to maintain clean architecture and allow multiple graphics backends away from the core emulation library.

## Memory Layout

The graphics system uses a memory-mapped approach with the following layout:

```
0x0000 → 0x002F    Palette (16 colors × 3 RGB bytes = 48 bytes)
0x0030 → 0x003F    Keyboard input buffer (16 bytes) 
0x0040 → 0x00FF    Unused/available for data storage
0x0100 → 0x1900    Video buffer (128×96 pixels, 4-bit indexed color)
```

### Palette Format
Each color in the palette consists of 3 bytes (RGB):
- Byte 0: Red component (0-255)
- Byte 1: Green component (0-255) 
- Byte 2: Blue component (0-255)

### Video Buffer Format
The video buffer stores 4-bit indexed color values:
- Each byte contains 2 pixels (4 bits each)
- Lower 4 bits = left pixel, upper 4 bits = right pixel
- Values 0-15 index into the palette

## Available Backends

### MiniFB Backend (`MiniFBDisplay`)

The default backend using the `minifb` crate for cross-platform window management.

**Features:**
- 128×96 base resolution with 4x scaling
- Real-time palette-based rendering
- Keyboard input support
- Cross-platform (Windows, macOS, Linux)

**Known Issues:**
- May have compatibility issues with Wayland on Linux

## Usage

### Basic Usage

```rust
use soft65c02_graphics::MiniFBDisplay;
use soft65c02_lib::{Memory, AddressableIO};

// Create memory system with graphics
let mut memory = Memory::new_with_ram();
memory.add_subsystem("VIDEO", 0x0200, MiniFBDisplay::new());

// Set up a basic palette (16 colors)
let palette = vec![
    // Black, Dark Blue, Dark Green, Dark Cyan, etc.
    0x00, 0x00, 0x00,  0x00, 0x00, 0x80,  0x00, 0x80, 0x00,  0x00, 0x80, 0x80,
    0x80, 0x00, 0x00,  0x80, 0x00, 0x80,  0x80, 0x80, 0x00,  0xC0, 0xC0, 0xC0,
    0x80, 0x80, 0x80,  0x00, 0x00, 0xFF,  0x00, 0xFF, 0x00,  0x00, 0xFF, 0xFF,
    0xFF, 0x00, 0x00,  0xFF, 0x00, 0xFF,  0xFF, 0xFF, 0x00,  0xFF, 0xFF, 0xFF,
];
memory.write(0x0200, &palette).unwrap();

// Draw a pixel at position (10, 10) with color index 15 (white)
let pixel_addr = 0x0300 + (10 * 64 + 10 / 2); // 64 bytes per row, 2 pixels per byte
let pixel_data = if 10 % 2 == 0 { 0x0F } else { 0xF0 }; // Choose nibble
memory.write(pixel_addr, &[pixel_data]).unwrap();
```

### Running the Example

```bash
# From the project root
cd soft65c02_graphics
cargo run --example minifb
```

The example demonstrates:
- Setting up a display with a default 16-color palette
- Running a 65C02 program that generates animated patterns
- Real-time memory-mapped graphics rendering

### Custom Graphics Backends

You can create custom graphics backends by implementing the `DisplayBackend` trait:

```rust
use soft65c02_lib::{DisplayBackend, AddressableIO, memory::MemoryError};

pub struct MyCustomDisplay {
    // Your implementation
}

impl AddressableIO for MyCustomDisplay {
    fn get_size(&self) -> usize {
        // Return total addressable size
    }
    
    fn read(&self, addr: usize, len: usize) -> Result<Vec<u8>, MemoryError> {
        // Handle memory reads
    }
    
    fn write(&mut self, addr: usize, data: &[u8]) -> Result<(), MemoryError> {
        // Handle memory writes and trigger display updates
    }
}

impl DisplayBackend for MyCustomDisplay {
    fn get_dimensions(&self) -> (usize, usize) {
        (128, 96) // width, height
    }
    
    fn is_active(&self) -> bool {
        // Return whether the display window is still open
    }
    
    fn get_input_events(&mut self) -> Vec<u32> {
        // Return any keyboard events
    }
}
```

## Future Backends

Planned backends for better compatibility:

- **Pixels Backend**: Using `pixels` + `winit` for better Wayland support
- **Softbuffer Backend**: Pure software rendering for maximum compatibility  
- **Headless Backend**: For automated testing and CI environments
- **Web Backend**: WASM support for browser-based emulation

## Dependencies

- `soft65c02_lib`: Core emulator library (required)
- `minifb`: Window management and rendering (MiniFB backend only)

## Technical Details

### Thread Safety
Graphics backends run in their own threads to maintain smooth rendering without blocking the CPU emulation. Communication happens through atomic operations and mutex-protected buffers.

### Performance
The memory-mapped approach allows for efficient bulk updates while maintaining the authentic feel of 8-bit computer graphics programming.

### Compatibility
This design maintains full compatibility with existing `soft65c02_lib` code while providing a clean separation of concerns.

## License

Same as the parent project (GPL v3).

## Contributing

When adding new graphics backends:

1. Implement both `AddressableIO` and `DisplayBackend` traits
2. Add appropriate feature flags in `Cargo.toml`
3. Include examples demonstrating the backend
4. Update this README with backend-specific documentation
5. Ensure thread safety and proper resource cleanup 