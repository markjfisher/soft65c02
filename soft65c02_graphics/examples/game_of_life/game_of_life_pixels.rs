use std::io::prelude::*;
use std::fs::File;
use std::time::{Duration, Instant};
use std::sync::mpsc::channel;
use rand::Rng;

use soft65c02_graphics::PixelsDisplay;
use soft65c02_lib::{AddressableIO, Memory, Registers, execute_step};
use soft65c02_tester::{SymbolTable, CliDisplayer, Displayer};

// this can go up to 16000 in release mode on my PC
const UPDATES_PER_SECOND: u64 = 600;
const FRAME_TIME: Duration = Duration::from_micros(1_000_000 / UPDATES_PER_SECOND);

// Memory-mapped locations (relative to display start at 0x8000)
const DISPLAY_START: usize = 0x8000;
const PAUSE_FLAG_ADDR: usize = DISPLAY_START + 0x40;      // 0x8040 - pause toggle flag
const VIDEO_BUFFER_START: usize = DISPLAY_START + 0x100;  // 0x8100
const SCREEN_WIDTH: usize = 128;
const SCREEN_HEIGHT: usize = 96;
const BYTES_PER_ROW: usize = SCREEN_WIDTH / 2;  // 2 pixels per byte
const APPLICATION_LOAD_START: usize = 0x1000;

// Game of Life lookup table - static constant to avoid recreating every call
const LIFE_RULES: [[u8; 9]; 2] = [
    // Dead cell (index 0): becomes alive only with exactly 3 neighbors
    [0, 0, 0, 1, 0, 0, 0, 0, 0],  // Birth with 3 neighbors -> alive (will be colored later)
    // Live cell (index 1): stays alive with 2 or 3 neighbors  
    [0, 0, 1, 1, 0, 0, 0, 0, 0],  // Survival with 2 or 3 neighbors -> alive
];

// Game of Life state using optimized brute force approach (per Rokicki paper)
// Now stores neighbor counts for colorful visualization
struct GameOfLifeState {
    current_generation: Vec<Vec<u8>>,  // 0 = dead, 1-8 = alive with N neighbors
    next_generation: Vec<Vec<u8>>,
    write_buffer: Vec<u8>,  // Reusable buffer for memory writes
    color_counts: [u32; 9],  // Reusable color counting array
    generation_count: u32,
}

impl GameOfLifeState {
    fn new() -> Self {
        Self {
            current_generation: vec![vec![0u8; SCREEN_WIDTH]; SCREEN_HEIGHT],
            next_generation: vec![vec![0u8; SCREEN_WIDTH]; SCREEN_HEIGHT],
            write_buffer: vec![0u8; BYTES_PER_ROW * SCREEN_HEIGHT],
            color_counts: [0u32; 9],
            generation_count: 0,
        }
    }
    
    fn reset_to_random(&mut self, memory: &mut Memory) {
        println!("🎲 Generating new random pattern...");
        
        // Generate new random pattern
        let mut rng = rand::rng();
        let mut buffer = vec![0u8; BYTES_PER_ROW * SCREEN_HEIGHT];
        let mut live_cells = 0;
        
        // Fill buffer with random bits (30% chance of life)
        for byte in buffer.iter_mut() {
            let pixel1 = if rng.random_bool(0.3) { 1 } else { 0 };
            let pixel2 = if rng.random_bool(0.3) { 1 } else { 0 };
            *byte = (pixel1 << 4) | pixel2;
            if pixel1 == 1 { live_cells += 1; }
            if pixel2 == 1 { live_cells += 1; }
        }
        
        println!("Generated pattern: {} live cells out of {} total ({:.1}%)", 
                 live_cells, SCREEN_WIDTH * SCREEN_HEIGHT,
                 (live_cells as f64 / (SCREEN_WIDTH * SCREEN_HEIGHT) as f64) * 100.0);
        
        // Write to video buffer
        memory.write(VIDEO_BUFFER_START, &buffer).unwrap();
        
        // Verify the write worked
        let read_back = memory.read(VIDEO_BUFFER_START, buffer.len()).unwrap();
        assert_eq!(buffer, read_back, "Buffer write verification failed!");
        
        // Load the new pattern into our state
        self.load_from_memory(memory);
        
        // Reset generation counter
        self.generation_count = 0;
    }
    

    
    fn load_from_memory(&mut self, memory: &Memory) {
        // Read current state from video buffer directly into 2D array
        for y in 0..SCREEN_HEIGHT {
            let row_offset = y * BYTES_PER_ROW;
            if let Ok(row_data) = memory.read(VIDEO_BUFFER_START + row_offset, BYTES_PER_ROW) {
                for x in 0..SCREEN_WIDTH {
                    let byte_index = x / 2;
                    let is_upper_nibble = (x % 2) == 1;
                    
                    if byte_index < row_data.len() {
                        let pixel_value = if is_upper_nibble {
                            (row_data[byte_index] >> 4) & 0x0F
                        } else {
                            row_data[byte_index] & 0x0F
                        };
                        
                        // Convert color back to alive/dead (non-zero = alive as color 1 initially)
                        self.current_generation[y][x] = if pixel_value != 0 { 1 } else { 0 };
                    }
                }
            }
        }
    }
    
    fn compute_next_generation(&mut self) {
        // Based on Rokicki's paper: simple optimized brute force is often faster 
        // than complex algorithms for this type of pattern
        self.compute_brute_force_optimized();
        self.generation_count += 1;
    }
    
    fn compute_brute_force_optimized(&mut self) {
        // Reset color counts (reusing array instead of allocating)
        self.color_counts.fill(0);
        
        // PASS 1: Apply Game of Life rules to determine which cells live/die
        for y in 0..SCREEN_HEIGHT {
            for x in 0..SCREEN_WIDTH {
                let neighbors = self.count_neighbors_brute_force(x, y);
                let is_alive = if self.current_generation[y][x] > 0 { 1 } else { 0 };
                
                // Apply Game of Life rules using static lookup table
                let will_live = LIFE_RULES[is_alive][neighbors as usize] > 0;
                
                // Store just alive/dead for now
                self.next_generation[y][x] = if will_live { 1 } else { 0 };
            }
        }
        
        // PASS 2: Color the living cells based on their neighbor count in the NEW generation
        for y in 0..SCREEN_HEIGHT {
            for x in 0..SCREEN_WIDTH {
                if self.next_generation[y][x] > 0 {  // If cell is alive
                    // Count neighbors in the NEW generation
                    let neighbors = self.count_neighbors_in_next_generation(x, y);
                    let color = neighbors.max(1);  // Use neighbor count as color (min 1 for visibility)
                    self.next_generation[y][x] = color;
                    
                    if (color as usize) < self.color_counts.len() {
                        self.color_counts[color as usize] += 1;
                    }
                } else {
                    // Dead cells remain black (0)
                    self.color_counts[0] += 1;
                }
            }
        }
        
        // if self.generation_count % 100 == 0 {
        //     println!("Gen {}: Colors - Black:{} Blue:{} Green:{} Cyan:{} Yellow:{} Orange:{} Red:{} Purple:{} Magenta:{}", 
        //         self.generation_count,
        //         self.color_counts[0], self.color_counts[1], self.color_counts[2], self.color_counts[3], 
        //         self.color_counts[4], self.color_counts[5], self.color_counts[6], self.color_counts[7], self.color_counts[8]);
        // }
        
        std::mem::swap(&mut self.current_generation, &mut self.next_generation);
    }
    
    #[inline]
    fn count_neighbors(&self, grid: &[Vec<u8>], x: usize, y: usize) -> u8 {
        let mut count = 0;
        
        // Pre-calculate coordinates with wrapping for better performance
        let x_prev = if x == 0 { SCREEN_WIDTH - 1 } else { x - 1 };
        let x_next = if x == SCREEN_WIDTH - 1 { 0 } else { x + 1 };
        let y_prev = if y == 0 { SCREEN_HEIGHT - 1 } else { y - 1 };
        let y_next = if y == SCREEN_HEIGHT - 1 { 0 } else { y + 1 };
        
        // Check all 8 neighbors - unrolled for maximum performance
        if grid[y_prev][x_prev] > 0 { count += 1; }  // Top-left
        if grid[y_prev][x] > 0      { count += 1; }  // Top
        if grid[y_prev][x_next] > 0 { count += 1; }  // Top-right
        if grid[y][x_prev] > 0      { count += 1; }  // Left
        if grid[y][x_next] > 0      { count += 1; }  // Right
        if grid[y_next][x_prev] > 0 { count += 1; }  // Bottom-left
        if grid[y_next][x] > 0      { count += 1; }  // Bottom
        if grid[y_next][x_next] > 0 { count += 1; }  // Bottom-right
        
        count
    }
    
    #[inline]
    fn count_neighbors_brute_force(&self, x: usize, y: usize) -> u8 {
        self.count_neighbors(&self.current_generation, x, y)
    }
    
    #[inline]
    fn count_neighbors_in_next_generation(&self, x: usize, y: usize) -> u8 {
        self.count_neighbors(&self.next_generation, x, y)
    }
    
    fn write_to_memory(&mut self, memory: &mut Memory) {
        // Clear reusable buffer instead of allocating new one
        self.write_buffer.fill(0);
        
        // Write all pixels from 2D array using color values directly
        for y in 0..SCREEN_HEIGHT {
            let row_offset = y * BYTES_PER_ROW;
            for x in 0..SCREEN_WIDTH {
                let byte_index = row_offset + (x / 2);
                let is_upper_nibble = (x % 2) == 1;
                let pixel_value = self.current_generation[y][x]; // Already contains color index
                
                if byte_index < self.write_buffer.len() {
                    if is_upper_nibble {
                        self.write_buffer[byte_index] |= pixel_value << 4;
                    } else {
                        self.write_buffer[byte_index] |= pixel_value;
                    }
                }
            }
        }
        
        // Write directly to video buffer
        memory.write(VIDEO_BUFFER_START, &self.write_buffer).unwrap();
        }
}

fn main() {
    let init_vector: usize = APPLICATION_LOAD_START;  // Start program in low memory
    let mut memory = Memory::new_with_ram();
    let display = PixelsDisplay::new();
    memory.add_subsystem("VIDEO DISPLAY", DISPLAY_START, display);
    
    // Set up a colorful palette for Game of Life based on neighbor density
    // Color 0: Black (dead cells)
    // Colors 1-8: Different colors for live cells based on neighbor count
    // Colors 9-15: Extra colors for visual variety
    let palette: Vec<u8> = vec![
        // 0: Black (dead cells)
        0x00, 0x00, 0x00,
        // 1: Bright Blue (1 neighbor - very lonely)
        0x00, 0x00, 0xFF,
        // 2: Green (2 neighbors - stable, survival)
        0x00, 0xFF, 0x00,
        // 3: Bright Cyan (3 neighbors - birth/survival, optimal)
        0x00, 0xFF, 0xFF,
        // 4: Yellow (4 neighbors - getting crowded)
        0xFF, 0xFF, 0x00,
        // 5: Orange (5 neighbors - quite crowded)
        0xFF, 0x80, 0x00,
        // 6: Red (6 neighbors - very crowded)
        0xFF, 0x00, 0x00,
        // 7: Purple (7 neighbors - extremely crowded)
        0x80, 0x00, 0xFF,
        // 8: Bright Magenta (8 neighbors - maximum crowding)
        0xFF, 0x00, 0xFF,
        // 9-15: Extra gradient colors for visual effects
        // 9: Dark Green
        0x00, 0x80, 0x00,
        // 10: Pink
        0xFF, 0x80, 0x80,
        // 11: Light Green
        0x80, 0xFF, 0x80,
        // 12: Light Blue
        0x80, 0x80, 0xFF,
        // 13: Light Yellow
        0xFF, 0xFF, 0x80,
        // 14: Gray
        0x80, 0x80, 0x80,
        // 15: White
        0xFF, 0xFF, 0xFF,
    ];
    memory.write(DISPLAY_START, &palette).unwrap();
    
    // Initialize Game of Life state for fast computation
    let mut gol_state = GameOfLifeState::new();
    // Initialize with random pattern first
    gol_state.reset_to_random(&mut memory);
    
    // Try to load compiled Game of Life binary
    let program = match load_program_binary("build/gol.bin") {
        Ok(data) => {
            println!("Loaded Game of Life binary ({} bytes)", data.len());
            data
        }
        Err(_) => {
            println!("Binary not found, using built-in demo program");
            create_demo_program()
        }
    };
    
    // Load program after initializing display
    memory.write(init_vector, &program).unwrap();
    
    // Load symbols for debugging and trapping
    let mut symbols = SymbolTable::new();
    let mut debug_addr = None;
    let mut process_generation_addr = None;
    let mut reset_gol_addr = None;
    let mut start_addr = APPLICATION_LOAD_START;  // Default if symbols not found
    if let Ok(_) = symbols.load_vice_labels("build/gol.lbl") {
        println!("Loaded symbol table");
        debug_addr = symbols.get_address("_debug");
        if let Some(addr) = debug_addr {
            println!("Found debug breakpoint at 0x{:04X}", addr);
        }
        process_generation_addr = symbols.get_address("_process_generation");
        if let Some(addr) = process_generation_addr {
            println!("Found process_generation trap at 0x{:04X}", addr);
        }
        reset_gol_addr = symbols.get_address("_reset_gol");
        if let Some(addr) = reset_gol_addr {
            println!("Found reset_gol trap at 0x{:04X}", addr);
        }
        if let Some(addr) = symbols.get_address("start") {
            start_addr = addr as usize;
            println!("Found start address at 0x{:04X}", addr);
        }
    }

    let (sender, receiver) = channel();
    let mut displayer = CliDisplayer::new(std::io::stdout(), true);
    let display_thread = std::thread::spawn(move || {
        displayer.display(receiver).unwrap();
    });

    let mut registers = Registers::new(start_addr);
    let mut cycle = 0;

    println!("Starting Game of Life simulation...");
    println!("Running at {} updates per second", UPDATES_PER_SECOND);
    println!("Close the window to exit.");
    println!("Using Rust DMA acceleration for Game of Life computation");
    println!("🎮 Controls:");
    println!("  'R' = Reset to new random pattern");
    println!("  'P' = Pause/Resume simulation");
    println!("Colors represent neighbor density:");
    println!("  Black(0) = Dead, Blue(1) = 1 neighbor, Green(2) = 2 neighbors (survival)");
    println!("  Cyan(3) = 3 neighbors (birth/survival), Yellow(4+) = crowded areas");
    println!("  Orange/Red/Purple = very crowded areas about to die");

    loop {
        let frame_start = Instant::now();
        
        // Check for function traps
        let current_pc = registers.command_pointer;
        
        // Check if we've hit the process_generation trap
        if let Some(addr) = process_generation_addr {
            if current_pc == addr as usize {
                // Check pause flag before processing
                if let Ok(pause_data) = memory.read(PAUSE_FLAG_ADDR, 1) {
                    let is_paused = pause_data.len() > 0 && pause_data[0] != 0;
                    
                    if !is_paused {
                        // Load current state from video memory
                        gol_state.load_from_memory(&memory);
                        
                        // Compute next generation in Rust (much faster!)
                        let _start_time = Instant::now();
                        gol_state.compute_next_generation();
                        let _computation_time = _start_time.elapsed();
                        
                        // Write result back to video memory
                        gol_state.write_to_memory(&mut memory);
                        
                        // println!("Generation computed in {:?}", _computation_time);
                    }
                }
            }
        }
        
        // Check if we've hit the reset_gol trap
        if let Some(addr) = reset_gol_addr {
            if current_pc == addr as usize {
                gol_state.reset_to_random(&mut memory);
            }
        }
        
        // Check if we've hit the debug breakpoint
        if let Some(addr) = debug_addr {
            if current_pc == addr as usize {
                println!("Hit debug breakpoint - press Enter to continue...");
                let mut input = String::new();
                std::io::stdin().read_line(&mut input).unwrap();
            }
        }

        if let Ok(_instruction) = execute_step(&mut registers, &mut memory) {
            cycle += 1;
        } else {
            println!("Game of Life simulation ended after {} cycles", cycle);
            break;
        }
        
        // Frame rate limiting
        let frame_time = frame_start.elapsed();
        if frame_time < FRAME_TIME {
            std::thread::sleep(FRAME_TIME - frame_time);
        }
    }
    
    // Drop the sender to signal the display thread to exit
    drop(sender);
    display_thread.join().unwrap();
    
    println!("Game of Life simulation ended after {} cycles", cycle);
}

fn load_program_binary(filename: &str) -> Result<Vec<u8>, std::io::Error> {
    let mut file = File::open(filename)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    Ok(buffer)
}

fn create_demo_program() -> Vec<u8> {
    // Simple demo that creates a blinking pattern if no compiled binary is available
    // This just fills the screen with a checkerboard pattern that changes over time
    vec![
        // Initialize pattern
        0xa9, 0x01,       // lda #$01        ; Load pattern value
        0xa2, 0x00,       // ldx #$00        ; X = 0 (column counter)
        0xa0, 0x00,       // ldy #$00        ; Y = 0 (row counter)
        
        // Pattern loop
        0x8a,             // txa             ; A = X
        0x18,             // clc
        0x69, 0x01,       // adc #$01        ; A = X + 1
        0x4a,             // lsr             ; A = (X + 1) / 2
        0x29, 0x01,       // and #$01        ; A = ((X + 1) / 2) & 1
        0x9d, 0x00, 0x01, // sta $0100,X     ; Store to video buffer
        
        0xe8,             // inx             ; X++
        0xe0, 0x00,       // cpx #$00        ; Compare X with 0 (will wrap at 256)
        0xd0, 0xf1,       // bne pattern_loop; Continue if not zero
        
        // Increment pattern and delay
        0xa9, 0xff,       // lda #$ff        ; Load delay counter
        0x38,             // sec
        0xe9, 0x01,       // sbc #$01        ; Decrement
        0xd0, 0xfc,       // bne delay_loop  ; Continue delay
        
        0x4c, 0x04, 0x10, // jmp $1004       ; Jump back to start
    ]
}
