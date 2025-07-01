/*
 * Interactive Hilbert Curve Explorer
 * 
 * Features:
 * - Space-filling curve visualization with recursive construction
 * - Multiple iteration levels (1-7, perfect fit at level 7 for 128×96)
 * - Animated construction showing the curve building step by step
 * - Multiple color modes: construction order, depth-based, rainbow gradient
 * - Real-time parameter adjustment for exploration
 * 
 * Controls:
 * - Arrow keys: Pan view (when zoomed in)
 * - +/- keys: Zoom in/out for detail viewing
 * - I/D keys: Increase/decrease iteration level (1-7)
 * - S key: Toggle animation speed (slow/medium/fast/instant)
 * - C key: Cycle through color modes
 * - F key: Refresh/redraw current settings (restart animation)
 * - R key: Reset to default view (level, zoom, position)
 * - Space key: Toggle animation pause/resume
 * 
 * Technical Notes:
 * - Uses recursive Hilbert curve algorithm with 4 orientations
 * - Caches curve points to avoid recalculation
 * - Supports up to 16,384 points (128×128 grid at level 7)
 * - Beautiful color gradients show construction order and curve depth
 */

use soft65c02_lib::{Memory, AddressableIO};

// ASCII key codes from ReceivedCharacter events (layout-aware)
const KEY_R: u8 = b'R';      // R key for reset to defaults
const KEY_F: u8 = b'F';      // F key for refresh/redraw current
const KEY_I: u8 = b'I';      // I key - increase iteration level
const KEY_D: u8 = b'D';      // D key - decrease iteration level  
const KEY_S: u8 = b'S';      // S key - animation speed
const KEY_C: u8 = b'C';      // C key - color mode
const KEY_SPACE: u8 = b' ';  // Space key - pause/resume

// Navigation key codes (special codes from get_special_key_code - layout-independent)
const KEY_UP: u8 = 0x80;     // Up arrow
const KEY_DOWN: u8 = 0x81;   // Down arrow
const KEY_LEFT: u8 = 0x82;   // Left arrow
const KEY_RIGHT: u8 = 0x83;  // Right arrow

// Symbol character codes (from ReceivedCharacter events - ASCII values, layout-aware)
const CHAR_PLUS: u8 = b'+';     // '+' character
const CHAR_MINUS: u8 = b'-';    // '-' character
const CHAR_EQUALS: u8 = b'=';   // '=' character

// Constants for Hilbert curve computation
const SCREEN_WIDTH: usize = 128;
const SCREEN_HEIGHT: usize = 96;
const BYTES_PER_ROW: usize = SCREEN_WIDTH / 2;  // 2 pixels per byte
const VIDEO_BUFFER_START: usize = 0x8100;

// Default parameters
const DEFAULT_LEVEL: u32 = 5;        // 32×32 grid - good starting point
const DEFAULT_ZOOM: f64 = 1.0;       // Fit to screen
const DEFAULT_OFFSET_X: f64 = 0.0;   // Centered
const DEFAULT_OFFSET_Y: f64 = 0.0;   // Centered
const MAX_LEVEL: u32 = 7;            // 128×128 grid - perfect fit

// Animation parameters
const ANIMATION_SPEEDS: [u32; 4] = [1, 5, 20, u32::MAX]; // Points per frame: slow, medium, fast, instant  
const SPEED_NAMES: [&str; 4] = ["Slow", "Medium", "Fast", "Instant"];

// Color modes
#[derive(Clone, Copy, PartialEq)]
enum ColorMode {
    ConstructionOrder,  // Colors based on when points are drawn
    DepthGradient,      // Colors based on recursion depth
    RainbowSpiral,      // Rainbow colors following the curve
    DistanceFromCenter, // Colors based on distance from center
}

impl ColorMode {
    fn next(self) -> Self {
        match self {
            ColorMode::ConstructionOrder => ColorMode::DepthGradient,
            ColorMode::DepthGradient => ColorMode::RainbowSpiral,
            ColorMode::RainbowSpiral => ColorMode::DistanceFromCenter,
            ColorMode::DistanceFromCenter => ColorMode::ConstructionOrder,
        }
    }
    
    fn name(self) -> &'static str {
        match self {
            ColorMode::ConstructionOrder => "Construction Order",
            ColorMode::DepthGradient => "Depth Gradient", 
            ColorMode::RainbowSpiral => "Rainbow Spiral",
            ColorMode::DistanceFromCenter => "Distance Gradient",
        }
    }
}

// Point in the Hilbert curve with metadata
#[derive(Clone, Copy)]
struct HilbertPoint {
    x: i32,
    y: i32,
    order: u32,    // Construction order (0 to n-1)
    depth: u32,    // Recursion depth when this point was created
}

pub struct HilbertCurveState {
    level: u32,
    zoom: f64,
    offset_x: f64,
    offset_y: f64,
    color_mode: ColorMode,
    animation_speed_index: usize,
    animation_paused: bool,
    
    // Curve data
    curve_points: Vec<HilbertPoint>,
    animation_position: usize,  // How many points to draw (for animation)
    needs_recompute: bool,
    
    // Buffers
    frame_buffer: Vec<u8>,  // Cached computation result  
    write_buffer: Vec<u8>,  // Reusable buffer for memory writes
}

impl HilbertCurveState {
    pub fn new() -> Self {
        Self {
            level: DEFAULT_LEVEL,
            zoom: DEFAULT_ZOOM,
            offset_x: DEFAULT_OFFSET_X,
            offset_y: DEFAULT_OFFSET_Y,
            color_mode: ColorMode::ConstructionOrder,
            animation_speed_index: 1,
            animation_paused: false,
            
            curve_points: Vec::new(),
            animation_position: 0,
            needs_recompute: true,
            
            frame_buffer: vec![0u8; SCREEN_WIDTH * SCREEN_HEIGHT],
            write_buffer: vec![0u8; BYTES_PER_ROW * SCREEN_HEIGHT],
        }
    }
    
    pub fn redraw_current(&mut self, memory: &mut Memory) {
        println!("🔄 Redrawing Hilbert curve with current settings...");
        self.needs_recompute = true;
        self.animation_position = 0;
        
        self.compute_hilbert_curve();
        self.write_to_memory(memory);
        
        println!("Redrawn at level {}, zoom {:.2}, speed: {}, color mode: {}", 
                 self.level, self.zoom, SPEED_NAMES[self.animation_speed_index], self.color_mode.name());
    }
    
    pub fn reset_to_default(&mut self, memory: &mut Memory) {
        println!("🌀 Initializing Hilbert curve with default settings...");
        self.level = DEFAULT_LEVEL;
        self.zoom = DEFAULT_ZOOM;
        self.offset_x = DEFAULT_OFFSET_X;
        self.offset_y = DEFAULT_OFFSET_Y;
        self.color_mode = ColorMode::ConstructionOrder;
        self.animation_speed_index = 1;
        self.animation_paused = false;
        self.needs_recompute = true;
        self.animation_position = 0;
        
        self.compute_hilbert_curve();
        self.write_to_memory(memory);
        
        println!("Initialized at level {}, zoom {:.2}, speed: {}, color mode: {}", 
                 self.level, self.zoom, SPEED_NAMES[self.animation_speed_index], self.color_mode.name());
    }
    
    pub fn compute_next_generation(&mut self) {
        // For Hilbert curve, "next generation" means advance the animation
        if self.needs_recompute {
            self.compute_hilbert_curve();
            self.needs_recompute = false;
        }
        
        if !self.animation_paused && self.animation_position < self.curve_points.len() {
            let speed = ANIMATION_SPEEDS[self.animation_speed_index];
            self.animation_position = (self.animation_position + speed as usize).min(self.curve_points.len());
            self.render_curve();
        }
    }
    
    fn compute_hilbert_curve(&mut self) {
        println!("🌀 Computing Hilbert curve at level {}...", self.level);
        let start_time = std::time::Instant::now();
        
        self.curve_points.clear();
        self.animation_position = 0;
        
        let size = 1 << self.level; // 2^level
        let total_points = size * size;
        
        // Generate all points using the proven mathematical algorithm
        for i in 0..total_points {
            let (x, y) = self.d2xy(self.level, i as u32);
            let order = i as u32;
            let depth = self.level;
            
            self.curve_points.push(HilbertPoint { x, y, order, depth });
        }
        
        let elapsed = start_time.elapsed();
        println!("Hilbert curve computed: {} points in {:.2}ms", 
                 self.curve_points.len(), elapsed.as_secs_f64() * 1000.0);
        
        self.render_curve();
    }
    
    // Convert distance along Hilbert curve to (x,y) coordinates
    // This is the standard algorithm from "Hacker's Delight" and Wikipedia
    fn d2xy(&self, n: u32, d: u32) -> (i32, i32) {
        let mut x = 0i32;
        let mut y = 0i32;
        let mut t = d;
        
        let mut s = 1;
        while s < (1 << n) {
            let rx = ((t / 2) & 1) != 0;
            let ry = ((t ^ (if rx { 1 } else { 0 })) & 1) != 0;
            
            if !ry {
                if rx {
                    x = s - 1 - x;
                    y = s - 1 - y;
                }
                
                // Swap x and y
                let temp = x;
                x = y;
                y = temp;
            }
            
            if rx { x += s; }
            if ry { y += s; }
            
            t /= 4;
            s *= 2;
        }
        
        (x, y)
    }
    
    fn render_curve(&mut self) {
        // Clear frame buffer
        self.frame_buffer.fill(0);
        
        if self.curve_points.is_empty() {
            return;
        }
        
        let grid_size = 1 << self.level;
        let points_to_draw = self.animation_position.min(self.curve_points.len());
        
        // Calculate transformation from curve coordinates to screen coordinates
        let scale = (SCREEN_WIDTH.min(SCREEN_HEIGHT) as f64 * self.zoom) / grid_size as f64;
        let center_x = SCREEN_WIDTH as f64 / 2.0 + self.offset_x;
        let center_y = SCREEN_HEIGHT as f64 / 2.0 + self.offset_y;
        let half_size = (grid_size as f64 * scale) / 2.0;
        
        // Adjust center_y to move the curve down slightly for better centering
        let center_y = center_y + half_size / 64.0;
        
        // Draw the curve points up to animation position
        for i in 0..points_to_draw {
            let point = self.curve_points[i];
            
            // Transform to screen coordinates
            let screen_x = (center_x - half_size + point.x as f64 * scale) as i32;
            let screen_y = (center_y - half_size + point.y as f64 * scale) as i32;
            
            // Calculate color based on current color mode
            let mut color = self.calculate_point_color(&point, points_to_draw);
            
            // Highlight the most recent point in bright white for visibility during animation
            if i == points_to_draw - 1 && points_to_draw > 0 && points_to_draw < self.curve_points.len() {
                color = 15; // Bright white cursor during animation
            }
            
            // Draw point if within screen bounds
            if screen_x >= 0 && screen_x < SCREEN_WIDTH as i32 && 
               screen_y >= 0 && screen_y < SCREEN_HEIGHT as i32 {
                let pixel_index = screen_y as usize * SCREEN_WIDTH + screen_x as usize;
                if pixel_index < self.frame_buffer.len() {
                    self.frame_buffer[pixel_index] = color;
                }
            }
            
            // Always draw connecting lines (even for off-screen points) 
            // This ensures partial line rendering when zoomed in
            if i > 0 {
                let prev_point = self.curve_points[i - 1];
                let prev_x = (center_x - half_size + prev_point.x as f64 * scale) as i32;
                let prev_y = (center_y - half_size + prev_point.y as f64 * scale) as i32;
                
                self.draw_line(prev_x, prev_y, screen_x, screen_y, color);
            }
        }
    }
    
    fn calculate_point_color(&self, point: &HilbertPoint, total_drawn: usize) -> u8 {
        match self.color_mode {
            ColorMode::ConstructionOrder => {
                // Color based on construction order (0 to total_drawn)
                if total_drawn <= 1 { return 1; }
                let ratio = point.order as f64 / (total_drawn - 1) as f64;
                let color = (ratio * 14.0 + 1.0) as u8;
                if color >= 15 { 14 } else { color }  // Special case: cap final point to avoid bright white
            }
            ColorMode::DepthGradient => {
                // Color based on recursion depth
                let depth_ratio = point.depth as f64 / self.level as f64;
                let color = (depth_ratio * 14.0 + 1.0) as u8;
                if color >= 15 { 14 } else { color }  // Special case: cap to avoid bright white
            }
            ColorMode::RainbowSpiral => {
                // Rainbow colors cycling through the curve
                let cycle_length = 128; // Points per color cycle
                let position_in_cycle = point.order % cycle_length;
                let hue_ratio = position_in_cycle as f64 / cycle_length as f64;
                let color = ((hue_ratio * 14.0).sin().abs() * 14.0 + 1.0) as u8;
                if color >= 15 { 14 } else { color }  // Special case: cap to avoid bright white
            }
            ColorMode::DistanceFromCenter => {
                // Color based on distance from center of grid
                let grid_size = 1 << self.level;
                let center = grid_size as f64 / 2.0;
                let dx = point.x as f64 - center;
                let dy = point.y as f64 - center;
                let distance = (dx * dx + dy * dy).sqrt();
                let max_distance = center * 1.414; // Diagonal
                let ratio = (distance / max_distance).min(1.0);
                let color = (ratio * 14.0 + 1.0) as u8;
                if color >= 15 { 14 } else { color }  // Special case: cap to avoid bright white
            }
        }
    }
    
    // Line drawing using Bresenham's algorithm with proper clipping
    // Draws partial lines even when endpoints are off-screen
    fn draw_line(&mut self, x0: i32, y0: i32, x1: i32, y1: i32, color: u8) {
        let dx = (x1 - x0).abs();
        let dy = (y1 - y0).abs();
        let sx = if x0 < x1 { 1 } else { -1 };
        let sy = if y0 < y1 { 1 } else { -1 };
        let mut err = dx - dy;
        let mut x = x0;
        let mut y = y0;
        
        // Always draw the line, clipping individual pixels to screen bounds
        loop {
            // Draw pixel if within screen bounds (allows partial line rendering)
            if x >= 0 && x < SCREEN_WIDTH as i32 && y >= 0 && y < SCREEN_HEIGHT as i32 {
                let pixel_index = y as usize * SCREEN_WIDTH + x as usize;
                if pixel_index < self.frame_buffer.len() {
                    self.frame_buffer[pixel_index] = color;
                }
            }
            
            // Continue until we reach the endpoint, regardless of screen bounds
            if x == x1 && y == y1 { break; }
            
            let e2 = 2 * err;
            if e2 > -dy {
                err -= dy;
                x += sx;
            }
            if e2 < dx {
                err += dx;
                y += sy;
            }
        }
    }
    
    pub fn write_to_memory(&mut self, memory: &mut Memory) {
        // Clear reusable buffer
        self.write_buffer.fill(0);
        
        // Pack pixels into nibbles (2 pixels per byte)
        for y in 0..SCREEN_HEIGHT {
            let row_offset = y * BYTES_PER_ROW;
            for x in 0..SCREEN_WIDTH {
                let byte_index = row_offset + (x / 2);
                let is_upper_nibble = (x % 2) == 1;
                let pixel_value = self.frame_buffer[y * SCREEN_WIDTH + x];
                
                if byte_index < self.write_buffer.len() {
                    if is_upper_nibble {
                        self.write_buffer[byte_index] |= pixel_value << 4;
                    } else {
                        self.write_buffer[byte_index] |= pixel_value;
                    }
                }
            }
        }
        
        // Write to video buffer
        memory.write(VIDEO_BUFFER_START, &self.write_buffer).unwrap();
    }
    
    pub fn process_keyboard_input(&mut self, key_code: u8, memory: &mut Memory) -> bool {
        let needs_update = match key_code {
            // Navigation (when zoomed in) - matches Mandelbrot behavior
            KEY_UP => {
                self.offset_y += 10.0 / self.zoom;
                println!("⬆️  View up, offset: ({:.1}, {:.1})", self.offset_x, self.offset_y);
                true
            }
            KEY_DOWN => {
                self.offset_y -= 10.0 / self.zoom;
                println!("⬇️  View down, offset: ({:.1}, {:.1})", self.offset_x, self.offset_y);
                true
            }
            KEY_LEFT => {
                self.offset_x += 10.0 / self.zoom;
                println!("⬅️  View left, offset: ({:.1}, {:.1})", self.offset_x, self.offset_y);
                true
            }
            KEY_RIGHT => {
                self.offset_x -= 10.0 / self.zoom;
                println!("➡️  View right, offset: ({:.1}, {:.1})", self.offset_x, self.offset_y);
                true
            }
            
            // Zoom controls
            CHAR_PLUS | CHAR_EQUALS => {
                self.zoom *= 1.5;
                let symbol = if key_code == CHAR_PLUS { "+" } else { "=" };
                println!("🔍 Zooming in ({}), new zoom level: {:.2}", symbol, self.zoom);
                true
            }
            CHAR_MINUS => {
                self.zoom /= 1.5;
                println!("🔍 Zooming out (-), new zoom level: {:.2}", self.zoom);
                true
            }
            
            // Level controls
            KEY_I | b'i' => {
                if self.level < MAX_LEVEL {
                    self.level += 1;
                    let points = 1 << (2 * self.level); // 4^level points
                    println!("🔄 Increased level to {} ({} points)", self.level, points);
                    self.needs_recompute = true;
                    self.animation_position = 0;
                }
                true
            }
            KEY_D | b'd' => {
                if self.level > 1 {
                    self.level -= 1;
                    let points = 1 << (2 * self.level); // 4^level points
                    println!("🔄 Decreased level to {} ({} points)", self.level, points);
                    self.needs_recompute = true;
                    self.animation_position = 0;
                }
                true
            }
            
            // Animation speed
            KEY_S | b's' => {
                self.animation_speed_index = (self.animation_speed_index + 1) % ANIMATION_SPEEDS.len();
                println!("⚡ Animation speed: {}", SPEED_NAMES[self.animation_speed_index]);
                false // No visual update needed
            }
            
            // Color mode
            KEY_C | b'c' => {
                self.color_mode = self.color_mode.next();
                println!("🎨 Color mode: {}", self.color_mode.name());
                true
            }
            
            // Pause/resume animation
            KEY_SPACE => {
                self.animation_paused = !self.animation_paused;
                let state = if self.animation_paused { "Paused" } else { "Resumed" };
                println!("⏯️  Animation: {}", state);
                false // No immediate visual update needed
            }
            
            // Refresh (redraw with current settings)
            KEY_F | b'f' => {
                println!("🔄 Refresh key pressed - restarting animation with current settings");
                self.redraw_current(memory);
                return true;  // Already updated memory
            }
            
            // Reset to defaults
            KEY_R | b'r' => {
                println!("🌀 Reset key pressed - returning to default view");
                self.reset_to_default(memory);
                return true;  // Already updated memory
            }
            
            _ => {
                println!("Unknown key pressed: 0x{:02X} ('{}')", key_code, key_code as char);
                return false;
            }
        };
        
        if needs_update {
            self.render_curve();
        }
        
        needs_update
    }
}

pub fn get_hilbert_palette() -> Vec<u8> {
    // Create a beautiful palette for Hilbert curve visualization
    // Color 0: Black (background)
    // Colors 1-15: Smooth gradient for the curve progression
    vec![
        // 0: Black (background)
        0x00, 0x00, 0x00,
        // 1: Deep Purple
        0x40, 0x00, 0x80,
        // 2: Purple  
        0x60, 0x00, 0xA0,
        // 3: Blue-Purple
        0x80, 0x00, 0xC0,
        // 4: Blue
        0x00, 0x00, 0xFF,
        // 5: Blue-Cyan
        0x00, 0x40, 0xFF,
        // 6: Cyan
        0x00, 0x80, 0xFF,
        // 7: Light Cyan
        0x00, 0xC0, 0xFF,
        // 8: Cyan-Green
        0x00, 0xFF, 0xC0,
        // 9: Green
        0x00, 0xFF, 0x00,
        // 10: Yellow-Green
        0x80, 0xFF, 0x00,
        // 11: Yellow
        0xFF, 0xFF, 0x00,
        // 12: Orange
        0xFF, 0x80, 0x00,
        // 13: Red-Orange
        0xFF, 0x40, 0x00,
        // 14: Red
        0xFF, 0x00, 0x00,
        // 15: Bright White
        0xFF, 0xFF, 0xFF,
    ]
}