#!/bin/bash -e

# Simple compilation script for Game of Life using cc65
# You may need to adjust paths and options for your cc65 installation

echo "Compiling Conway's Game of Life for 65C02..."

if [ ! -d build ]; then
  mkdir build
fi

rm -f build/* >/dev/null

cl65 -t none -c --create-dep build/min_crt0.d --listing build/min_crt0.lst -o build/min_crt0.o min_crt0.s
cl65 -t none -c --create-dep build/gol.d --listing build/gol.lst -o build/gol.o gol.s
cl65 -t none -C gol.cfg --mapfile build/gol.map -Ln build/gol.lbl -o build/gol.bin build/gol.o build/min_crt0.o

if [ $? -eq 0 ]; then
    echo "Compilation successful! Binary: gol.bin"
    ls -la build/gol.bin
else
    echo "Compilation failed!"
    exit 1
fi

echo "Done. You can now run:"
echo "cargo run --example game_of_life_pixels --features pixels-backend" 