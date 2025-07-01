# Graphics Demo - Multi-Game 65C02 System

A sophisticated graphics demonstration showcasing the soft65c02 emulator's capabilities with multiple interactive games and visualizations. This system combines 6502 assembly code for real-time input handling with Rust acceleration for computationally intensive graphics generation.

## 🎮 Games & Visualizations

### 1. Conway's Game of Life (Mode 1)
- **Colorful cellular automaton** with neighbor-count based coloring
- **Random pattern generation** with 30% initial life probability
- **Real-time evolution** at 600 updates per second
- **Interactive controls**: Reset (R) for new random patterns
- **Optimized algorithm** based on Rokicki's brute-force optimization paper

### 2. Mandelbrot Set Explorer (Mode 2) 
- **Interactive fractal exploration** with real-time parameter adjustment
- **Beautiful gradient palette** (blue→purple→red→orange→yellow→white)
- **Navigation**: Arrow keys for panning, +/- for zoom, I/D for iterations
- **Reset function**: R key returns to default view
- **High-performance computation** with configurable iteration limits

### 3. Hilbert Curve Explorer (Mode 3) ⭐ **NEW**
- **Interactive space-filling curve** with animated construction
- **Multiple iteration levels** (1-7, perfect 128×128 fit at level 7)
- **Four color modes**: Construction order, depth gradient, rainbow spiral, distance gradient
- **Real-time animation** with adjustable speed (slow/medium/fast/instant)
- **Navigation**: Pan, zoom, and pause controls for detailed exploration

### 4. Extensible Architecture (Modes 4-9)
- Framework ready for additional games and visualizations
- Each mode gets its own dedicated processor and state management
- Easy to add new interactive graphics applications

## 🎯 Controls

### Universal Controls
- **Number Keys (1-9)**: Switch between game modes
  - `1` = Game of Life
  - `2` = Mandelbrot Set Explorer
  - `3` = Hilbert Curve Explorer  
  - `4-9` = Reserved for future games
- **0 Key**: No-op mode (system idle)
- **P Key**: Toggle pause (stops generation, allows mode switching)

### Game of Life (Mode 1)
- **R**: Generate new random pattern

### Mandelbrot Explorer (Mode 2)
- **Arrow Keys**: Pan view (↑↓←→)
- **+ Key**: Zoom in
- **- Key**: Zoom out
- **= Key**: Alternative zoom in (for keyboards where + requires Shift)
- **I Key**: Increase iteration limit (more detail)
- **D Key**: Decrease iteration limit (faster computation)
- **R Key**: Reset to default view

### Hilbert Curve Explorer (Mode 3)
- **Arrow Keys**: Pan view (when zoomed in)
- **+ Key**: Zoom in for detail viewing
- **- Key**: Zoom out
- **= Key**: Alternative zoom in
- **I Key**: Increase iteration level (more complex curve)
- **D Key**: Decrease iteration level (simpler curve)
- **S Key**: Toggle animation speed (slow/medium/fast/instant)
- **C Key**: Cycle through color modes
- **Space Key**: Pause/resume animation
- **R Key**: Reset to default view

## 🌍 International Keyboard Support

The system uses a **hybrid input approach** for maximum compatibility across keyboard layouts:

### Layout-Aware Characters
- **Symbols** (+, -, =): Work on any layout
  - German QWERTZ: `Shift+*` produces "+"
  - US QWERTY: `Shift+=` produces "+"
  - UK QWERTY: `Shift+=` produces "+"
  - French AZERTY: `Shift+=` produces "+"

### Layout-Independent Keys
- **Numbers (0-9)**: Physical position consistent
- **Arrows**: Always work the same
- **Letters**: Accept both uppercase and lowercase

### Tested Layouts
✅ US QWERTY  
✅ UK QWERTY  
✅ German QWERTZ  
✅ French AZERTY  
✅ And many others!

## 🏗️ Architecture

### Memory-Mapped System
```
0x8000-0x802F : Color palette (16 colors × 3 bytes RGB)
0x8030        : Keyboard input buffer
0x8040        : Command register (0=no-op, 1=generate, 2=process-input, 3=debug)
0x8041        : Mode register (0=no-op, 1=GoL, 2=Mandelbrot, 3=Hilbert, 4-9=future)
0x8100-0x18FF : Video buffer (128×96 pixels, 4-bit color, 2 pixels/byte)
```

### Hybrid Processing Model
- **6502 Assembly**: Real-time input polling, mode switching, system control
- **Rust Acceleration**: Heavy computation (cellular automata, fractal generation)
- **DMA-style Communication**: Memory-mapped commands trigger Rust processing

### State Preservation
- Each game maintains its own **internal state**
- **Mode switching preserves progress** - switch away and back without losing your place
- **Video buffer is output-only** - games never read their state back from display
- **Solved state corruption bug** where switching modes would corrupt game progress

## 🛠️ Building & Running

### Prerequisites
- Rust toolchain with soft65c02 libraries
- CC65 assembler for 6502 code compilation

### Build Process
```bash
# Compile 6502 assembly to binary
./compile.sh

# Run the graphics demo
cargo run --example gfx_demo --features pixels-backend
```

### Files Structure
- `game.rs` - Main Rust application with game manager and memory-mapped interface
- `game.s` - 6502 assembly for input handling and system control
- `gol.rs` - Game of Life implementation with colorful visualization
- `mandlebrot.rs` - Mandelbrot set explorer with real-time parameter adjustment
- `compile.sh` - Build script for 6502 assembly compilation
- `game.cfg` - CC65 linker configuration

## 🔧 Technical Details

### Display Specifications
- **Resolution**: 128×96 pixels
- **Color Depth**: 4-bit (16 colors)
- **Pixel Packing**: 2 pixels per byte (nibble each)
- **Frame Rate**: 600 Hz update rate
- **Backend**: Pixels + winit for cross-platform compatibility

### Performance Optimizations
- **Reusable buffers** to minimize allocations
- **Brute-force cellular automata** (often faster than complex algorithms)
- **Static lookup tables** for Game of Life rules
- **Inline functions** for hot paths
- **Memory-mapped DMA** to avoid polling overhead

### Game State Management
- Each game processor implements the `GameProcessor` trait
- Games maintain separate internal state (never read from video buffer)
- Lazy initialization - games created only when first accessed
- State preserved across mode switches

## 🎨 Color Palettes

### Game of Life Palette
- **Color 0**: Black (dead cells)
- **Colors 1-8**: Blue gradient representing neighbor counts
- Creates beautiful flowing patterns as life evolves

### Mandelbrot Palette  
- **Color 0**: Black (points in the set)
- **Colors 1-15**: Gradient from blue→purple→red→orange→yellow→white
- Iteration count determines color, creating stunning fractal boundaries

### Hilbert Curve Palette
- **Color 0**: Black (background)
- **Colors 1-15**: Smooth spectrum from deep purple→blue→cyan→green→yellow→red→white
- Color usage depends on selected mode: construction order, recursion depth, rainbow spiral, or distance gradient

## 🚀 Future Extensions

The architecture supports easy addition of new games and visualizations:

1. **Implement GameProcessor trait** for your new game
2. **Add mode constant** and case in GameManager
3. **Update assembly** to recognize new mode number
4. **Create color palette** for your visualization
5. **Handle game-specific controls** in process_keyboard_input

Potential future modes:
- Flocking simulation (boids)
- Reaction-diffusion systems  
- Neural network visualization
- Audio spectrum analyzer
- Digital art generators
- Educational math visualizations

## 📜 License

Part of the soft65c02 emulator project. See LICENSE.txt for details. 