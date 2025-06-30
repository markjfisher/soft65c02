/*
 * Pixels Display Backend for Soft65C02
 *
 * Modern graphics backend using pixels + winit for better cross-platform support,
 * particularly improved Wayland compatibility.
 *
 * Memory layout (same as MiniFB backend):
 * #0x0000 → #0x002F    palette (16 × 3 bytes for RGB)
 * #0x0030 → #0x003F    keyboard keys pressed
 * #0x0040 → #0x00FF    unused¹
 * #0x0100 → #0x1900    video buffer
 */
use soft65c02_lib::{AddressableIO, DisplayBackend, memory::MemoryError};
use pixels::{Pixels, SurfaceTexture};
use winit::{
    dpi::LogicalSize,
    event::{Event, WindowEvent, ElementState, VirtualKeyCode, KeyboardInput},
    event_loop::ControlFlow,
    window::{Window, WindowBuilder},
};

// Import EventLoop and EventLoopBuilder conditionally
#[cfg(any(target_os = "linux", target_os = "dragonfly", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd"))]
use winit::event_loop::EventLoopBuilder;

#[cfg(not(any(target_os = "linux", target_os = "dragonfly", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd")))]
use winit::event_loop::EventLoop;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

// Platform-specific imports for Linux
#[cfg(any(target_os = "linux", target_os = "dragonfly", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd"))]
use winit::platform::x11::EventLoopBuilderExtX11;

pub const DISPLAY_WIDTH: usize = 128;
pub const DISPLAY_HEIGHT: usize = 96;
pub const BUFFER_VIDEO_START_ADDR: usize = 256;

pub struct CommunicationToken {
    is_calling: AtomicBool,
    address: AtomicUsize,
    len: AtomicUsize,
    is_active: AtomicBool,
}

struct WindowState {
    pixels: Pixels,
    token: Arc<CommunicationToken>,
    buffer: Arc<Mutex<Vec<u8>>>,
    input_tx: mpsc::Sender<u32>,
}

impl WindowState {
    fn new(
        window: &Window,
        token: Arc<CommunicationToken>,
        buffer: Arc<Mutex<Vec<u8>>>,
        input_tx: mpsc::Sender<u32>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let window_size = window.inner_size();
        let surface_texture = SurfaceTexture::new(window_size.width, window_size.height, window);
        let mut pixels = Pixels::new(DISPLAY_WIDTH as u32, DISPLAY_HEIGHT as u32, surface_texture)?;
        
        // Initialize with black background
        Self::clear_frame(pixels.frame_mut());
        pixels.render()?;
        
        Ok(Self {
            pixels,
            token,
            buffer,
            input_tx,
        })
    }
    
    fn clear_frame(frame: &mut [u8]) {
        for pixel in frame.chunks_exact_mut(4) {
            pixel[0] = 0;   // R
            pixel[1] = 0;   // G  
            pixel[2] = 0;   // B
            pixel[3] = 255; // A
        }
    }
    
    fn handle_window_event(&mut self, event: WindowEvent, control_flow: &mut ControlFlow) {
        match event {
            WindowEvent::CloseRequested => {
                self.token.is_active.store(false, Ordering::SeqCst);
                *control_flow = ControlFlow::Exit;
            }
            WindowEvent::KeyboardInput {
                input: KeyboardInput {
                    virtual_keycode: Some(key_code),
                    state: ElementState::Pressed,
                    ..
                },
                ..
            } => {
                let code = get_key_code(key_code);
                let _ = self.input_tx.send(code as u32);
            }
            WindowEvent::Resized(size) => {
                if let Err(err) = self.pixels.resize_surface(size.width, size.height) {
                    eprintln!("pixels.resize_surface() failed: {err}");
                    *control_flow = ControlFlow::Exit;
                }
            }
            _ => {}
        }
    }
    
    fn update_display(&mut self) {
        if !self.token.is_calling.load(Ordering::Acquire) {
            return;
        }
        
        let addr = self.token.address.load(Ordering::SeqCst);
        let len = self.token.len.load(Ordering::SeqCst);
        let buffer = self.buffer.lock().unwrap();
        let frame = self.pixels.frame_mut();
        
        Self::render_video_buffer(&buffer, addr, len, frame);
        self.token.is_calling.store(false, Ordering::SeqCst);
    }
    
    fn render_video_buffer(buffer: &[u8], addr: usize, len: usize, frame: &mut [u8]) {
        for (index, byte) in buffer[addr..addr + len].iter().enumerate() {
            let addr_index = addr + index;
            if addr_index < BUFFER_VIDEO_START_ADDR {
                continue;
            }
            
            let video_offset = addr_index - BUFFER_VIDEO_START_ADDR;
            let pixel_x = (video_offset % 64) * 2; // 64 bytes per row, 2 pixels per byte
            let pixel_y = video_offset / 64;
            
            if pixel_y >= DISPLAY_HEIGHT || pixel_x >= DISPLAY_WIDTH - 1 {
                continue;
            }
            
            let (loval, hival) = (byte & 0x0F, byte >> 4);
            
            // Render left pixel (lower nibble)
            Self::render_pixel(buffer, frame, loval, pixel_x, pixel_y);
            
            // Render right pixel (upper nibble)  
            Self::render_pixel(buffer, frame, hival, pixel_x + 1, pixel_y);
        }
    }
    
    fn render_pixel(buffer: &[u8], frame: &mut [u8], color_index: u8, x: usize, y: usize) {
        if color_index >= 16 {
            return;
        }
        
        let palette_offset = (color_index as usize) * 3;
        if palette_offset + 2 >= buffer.len() {
            return;
        }
        
        let rgba_offset = (y * DISPLAY_WIDTH + x) * 4;
        if rgba_offset + 3 >= frame.len() {
            return;
        }
        
        frame[rgba_offset] = buffer[palette_offset];     // R
        frame[rgba_offset + 1] = buffer[palette_offset + 1]; // G
        frame[rgba_offset + 2] = buffer[palette_offset + 2]; // B
        frame[rgba_offset + 3] = 255; // A
    }
    
    fn render(&mut self) -> Result<(), pixels::Error> {
        self.pixels.render()
    }
}

pub struct PixelsDisplay {
    token: Arc<CommunicationToken>,
    buffer: Arc<Mutex<Vec<u8>>>,
    input_receiver: Option<mpsc::Receiver<u32>>,
}

fn create_event_loop() -> Result<winit::event_loop::EventLoop<()>, Box<dyn std::error::Error>> {
    #[cfg(any(target_os = "linux", target_os = "dragonfly", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd"))]
    {
        Ok(EventLoopBuilder::new().with_any_thread(true).build())
    }
    #[cfg(not(any(target_os = "linux", target_os = "dragonfly", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd")))]
    {
        Ok(EventLoop::new())
    }
}

fn create_window(event_loop: &winit::event_loop::EventLoop<()>) -> Result<Window, Box<dyn std::error::Error>> {
    let size = LogicalSize::new(DISPLAY_WIDTH as f64 * 4.0, DISPLAY_HEIGHT as f64 * 4.0);
    let window = WindowBuilder::new()
        .with_title("Soft-65C02 Display (Pixels)")
        .with_inner_size(size)
        .with_min_inner_size(size)
        .build(event_loop)?;
    Ok(window)
}

fn run_event_loop(
    event_loop: winit::event_loop::EventLoop<()>,
    window: Window,
    token: Arc<CommunicationToken>,
    buffer: Arc<Mutex<Vec<u8>>>,
    input_tx: mpsc::Sender<u32>,
) {
    let mut window_state = match WindowState::new(&window, token, buffer, input_tx) {
        Ok(state) => state,
        Err(e) => {
            eprintln!("Failed to create window state: {}", e);
            return;
        }
    };
    
    event_loop.run(move |event, _, control_flow| {
        *control_flow = ControlFlow::Wait;
        
        match event {
            Event::WindowEvent { event, .. } => {
                window_state.handle_window_event(event, control_flow);
            }
            Event::MainEventsCleared => {
                window_state.update_display();
                window.request_redraw();
            }
            Event::RedrawRequested(_) => {
                if window_state.render().is_err() {
                    *control_flow = ControlFlow::Exit;
                }
            }
            _ => {}
        }
    });
}

#[allow(dead_code)]
fn get_key_code(key: VirtualKeyCode) -> u8 {
    match key {
        VirtualKeyCode::Key1 => 0x01,
        VirtualKeyCode::Key2 => 0x02,
        VirtualKeyCode::Key3 => 0x03,
        VirtualKeyCode::Key4 => 0x04,
        VirtualKeyCode::Key5 => 0x05,
        VirtualKeyCode::Key6 => 0x06,
        VirtualKeyCode::Key7 => 0x07,
        VirtualKeyCode::Key8 => 0x08,
        VirtualKeyCode::Key9 => 0x09,
        VirtualKeyCode::Key0 => 0x0a,
        VirtualKeyCode::A => 0x0b,
        VirtualKeyCode::B => 0x0c,
        VirtualKeyCode::C => 0x0d,
        VirtualKeyCode::D => 0x0e,
        VirtualKeyCode::E => 0x0f,
        VirtualKeyCode::F => 0x10,
        VirtualKeyCode::G => 0x11,
        VirtualKeyCode::H => 0x12,
        VirtualKeyCode::I => 0x13,
        VirtualKeyCode::J => 0x14,
        VirtualKeyCode::K => 0x15,
        VirtualKeyCode::L => 0x16,
        VirtualKeyCode::M => 0x17,
        VirtualKeyCode::N => 0x18,
        VirtualKeyCode::O => 0x19,
        VirtualKeyCode::P => 0x1a,
        VirtualKeyCode::Q => 0x1b,
        VirtualKeyCode::R => 0x1c,
        VirtualKeyCode::S => 0x1d,
        VirtualKeyCode::T => 0x1e,
        VirtualKeyCode::U => 0x1f,
        VirtualKeyCode::V => 0x20,
        VirtualKeyCode::W => 0x21,
        VirtualKeyCode::X => 0x22,
        VirtualKeyCode::Y => 0x23,
        VirtualKeyCode::Z => 0x24,
        VirtualKeyCode::F1 => 0x25,
        VirtualKeyCode::F2 => 0x26,
        VirtualKeyCode::F3 => 0x27,
        VirtualKeyCode::F4 => 0x28,
        VirtualKeyCode::F5 => 0x29,
        VirtualKeyCode::F6 => 0x2a,
        VirtualKeyCode::F7 => 0x2b,
        VirtualKeyCode::F8 => 0x2c,
        VirtualKeyCode::F9 => 0x2d,
        VirtualKeyCode::F10 => 0x2e,
        VirtualKeyCode::F11 => 0x2f,
        VirtualKeyCode::F12 => 0x30,
        VirtualKeyCode::Down => 0x34,
        VirtualKeyCode::Left => 0x35,
        VirtualKeyCode::Right => 0x36,
        VirtualKeyCode::Up => 0x37,
        VirtualKeyCode::Apostrophe => 0x38,
        VirtualKeyCode::Grave => 0x39,
        VirtualKeyCode::Backslash => 0x3a,
        VirtualKeyCode::Comma => 0x3b,
        VirtualKeyCode::Equals => 0x3c,
        VirtualKeyCode::LBracket => 0x3d,
        VirtualKeyCode::Minus => 0x3e,
        VirtualKeyCode::Period => 0x3f,
        VirtualKeyCode::RBracket => 0x40,
        VirtualKeyCode::Semicolon => 0x41,
        VirtualKeyCode::Slash => 0x42,
        VirtualKeyCode::Back => 0x43,
        VirtualKeyCode::Delete => 0x44,
        VirtualKeyCode::End => 0x45,
        VirtualKeyCode::Return => 0x46,
        VirtualKeyCode::Escape => 0x47,
        VirtualKeyCode::Home => 0x48,
        VirtualKeyCode::Insert => 0x49,
        VirtualKeyCode::PageDown => 0x4b,
        VirtualKeyCode::PageUp => 0x4c,
        VirtualKeyCode::Pause => 0x4d,
        VirtualKeyCode::Space => 0x4e,
        VirtualKeyCode::Tab => 0x4f,
        VirtualKeyCode::Numlock => 0x50,
        VirtualKeyCode::Capital => 0x51,
        VirtualKeyCode::Scroll => 0x52,
        VirtualKeyCode::LShift => 0x53,
        VirtualKeyCode::RShift => 0x54,
        VirtualKeyCode::LControl => 0x55,
        VirtualKeyCode::RControl => 0x56,
        VirtualKeyCode::Numpad0 => 0x57,
        VirtualKeyCode::Numpad1 => 0x58,
        VirtualKeyCode::Numpad2 => 0x59,
        VirtualKeyCode::Numpad3 => 0x5a,
        VirtualKeyCode::Numpad4 => 0x5b,
        VirtualKeyCode::Numpad5 => 0x5c,
        VirtualKeyCode::Numpad6 => 0x5d,
        VirtualKeyCode::Numpad7 => 0x5e,
        VirtualKeyCode::Numpad8 => 0x5f,
        VirtualKeyCode::Numpad9 => 0x60,
        VirtualKeyCode::NumpadDecimal => 0x61,
        VirtualKeyCode::NumpadDivide => 0x62,
        VirtualKeyCode::NumpadMultiply => 0x63,
        VirtualKeyCode::NumpadSubtract => 0x64,
        VirtualKeyCode::NumpadAdd => 0x65,
        VirtualKeyCode::NumpadEnter => 0x66,
        VirtualKeyCode::LAlt => 0x67,
        VirtualKeyCode::RAlt => 0x68,
        VirtualKeyCode::LWin => 0x69,
        VirtualKeyCode::RWin => 0x6a,
        _ => 0x6b, // Unknown
    }
}

impl PixelsDisplay {
    pub fn new() -> PixelsDisplay {
        let buffer: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(vec![
            0;
            DISPLAY_WIDTH * DISPLAY_HEIGHT / 2 + BUFFER_VIDEO_START_ADDR
        ]));
        let token = Arc::new(CommunicationToken {
            is_calling: AtomicBool::new(false),
            address: AtomicUsize::new(0),
            len: AtomicUsize::new(0),
            is_active: AtomicBool::new(true),
        });
        
        let (input_tx, input_rx) = mpsc::channel();
        let rtoken = token.clone();
        let rbuffer = buffer.clone();

        thread::spawn(move || {
            let event_loop = match create_event_loop() {
                Ok(el) => el,
                Err(e) => {
                    eprintln!("Failed to create event loop: {}", e);
                    return;
                }
            };
            
            let window = match create_window(&event_loop) {
                Ok(w) => w,
                Err(e) => {
                    eprintln!("Failed to create window: {}", e);
                    return;
                }
            };
            
            run_event_loop(event_loop, window, rtoken, rbuffer, input_tx);
        });

        PixelsDisplay { 
            token, 
            buffer,
            input_receiver: Some(input_rx),
        }
    }
}

impl AddressableIO for PixelsDisplay {
    fn get_size(&self) -> usize {
        DISPLAY_WIDTH * DISPLAY_HEIGHT / 2 + BUFFER_VIDEO_START_ADDR
    }

    fn read(&self, addr: usize, len: usize) -> Result<Vec<u8>, MemoryError> {
        let buffer = self.buffer.lock().unwrap();
        if buffer.len() >= addr + len {
            Ok(buffer[addr..addr + len].to_vec())
        } else {
            Err(MemoryError::ReadOverflow(len, addr))
        }
    }

    fn write(&mut self, addr: usize, data: &[u8]) -> Result<(), MemoryError> {
        let mut buffer = self.buffer.lock().unwrap();
        for (offset, byte) in data.iter().enumerate() {
            if addr + offset < buffer.len() {
                buffer[addr + offset] = *byte;
            }
        }
        self.token.is_calling.store(true, Ordering::Release);
        self.token.address.store(addr, Ordering::SeqCst);
        self.token.len.store(data.len(), Ordering::SeqCst);
        Ok(())
    }
}

impl DisplayBackend for PixelsDisplay {
    fn get_dimensions(&self) -> (usize, usize) {
        (DISPLAY_WIDTH, DISPLAY_HEIGHT)
    }
    
    fn is_active(&self) -> bool {
        self.token.is_active.load(Ordering::SeqCst)
    }
    
    fn get_input_events(&mut self) -> Vec<u32> {
        let mut events = Vec::new();
        if let Some(ref receiver) = self.input_receiver {
            while let Ok(event) = receiver.try_recv() {
                events.push(event);
            }
        }
        events
    }
} 