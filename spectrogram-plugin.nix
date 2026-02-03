{ pkgs ? import <nixpkgs> {} }:

pkgs.mkDerivation {
  pname = "spectrogram-plugin";
  version = "0.1.0";
  
  src = ./.;
  
  buildInputs = with pkgs; [
    rustc
    cargo
    lean4
    minizinc
  ];
  
  buildPhase = ''
    # Build Rust plugin
    cd rust_tools
    cargo build --release --bin spectrogram_plugin
    cd ..
    
    # Check Lean4
    lean Spectrogram.lean
    
    # Run MiniZinc optimization
    minizinc spectrogram_optimization.mzn > spectrogram_params.txt
  '';
  
  installPhase = ''
    mkdir -p $out/bin
    mkdir -p $out/lib
    mkdir -p $out/share/lean
    mkdir -p $out/share/minizinc
    
    # Install Rust binary
    cp rust_tools/target/release/spectrogram_plugin $out/bin/
    
    # Install Lean4 module
    cp Spectrogram.lean $out/share/lean/
    
    # Install MiniZinc model
    cp spectrogram_optimization.mzn $out/share/minizinc/
    cp spectrogram_params.txt $out/share/
  '';
  
  meta = with pkgs.lib; {
    description = "Spectrogram plugin for Monster group system";
    license = licenses.agpl3Plus;
    platforms = platforms.all;
  };
}
