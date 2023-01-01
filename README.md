# nes-emulator

My implementation of an emulator capable of running and playing first-gen NES (Nintendo Entertainment System) games in Rust! I created this project following this guide: https://bugzmanov.github.io/nes_ebook/chapter_1.html

## Running the application
Cargo will handle most of the dependencies for you, but you need to have `sdl2` installed to have the game render on the screen. If you have Homebrew installed, simply run `brew install sdl2`. If you're not on Mac or don't use HomeBrew, check out the repo for installation instructions: https://github.com/Rust-SDL2/rust-sdl2

## Testing
To run all of the unit tests, run `cargo test` from any directory. The CPU module has extensive unit testing, so if you just want to run selected tests use `cargo test --test [test_name]`. 


