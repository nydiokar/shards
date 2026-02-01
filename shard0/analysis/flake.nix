{
  description = "71-level deep analysis framework";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    pipelight.url = "github:meta-introspector/pipelight";
  };

  outputs = { self, nixpkgs, pipelight }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      analysisLevels = builtins.genList (i: i) 71;
      
      mkAnalysisMode = level: {
        name = "level${toString level}";
        tools = with pkgs; [
          # Core build tools
          rustc cargo gcc llvm
          # Binary analysis
          binutils elfutils file
          # Runtime analysis  
          gdb strace ltrace
          # Performance
          perf valgrind
          # Advanced
          (if level >= 10 then qemu else null)
          (if level >= 20 then goblin else null)
          (if level >= 30 then radare2 else null)
          (if level >= 40 then ghidra else null)
        ] ++ (if level >= 50 then [ systemtap bpftrace ] else []);
      };
      
      analysisModes = builtins.listToAttrs (
        map (level: {
          name = "level${toString level}";
          value = mkAnalysisMode level;
        }) analysisLevels
      );
      
    in {
      packages.${system} = {
        analyzer = pkgs.writeShellScriptBin "analyze" ''
          LEVEL=''${1:-0}
          TARGET=''${2:-.}
          
          echo "Analysis Level: $LEVEL"
          echo "Target: $TARGET"
          
          mkdir -p analysis/level$LEVEL/{deps,build,logs,perf,debug,elf,trace,core}
          
          # Dependency analysis
          if [ $LEVEL -ge 0 ]; then
            find $TARGET -name "*.d" -o -name "Cargo.lock" -o -name "flake.lock" > analysis/level$LEVEL/deps/manifest.txt
          fi
          
          # Build artifacts
          if [ $LEVEL -ge 5 ]; then
            find $TARGET -name "*.o" -o -name "*.rlib" -o -name "*.a" > analysis/level$LEVEL/build/artifacts.txt
          fi
          
          # ELF analysis
          if [ $LEVEL -ge 10 ]; then
            find $TARGET -type f -executable -exec file {} \; | grep ELF > analysis/level$LEVEL/elf/binaries.txt
          fi
          
          # Symbol extraction
          if [ $LEVEL -ge 15 ]; then
            while read bin; do
              ${pkgs.binutils}/bin/nm "$bin" > "analysis/level$LEVEL/elf/$(basename $bin).symbols" 2>/dev/null || true
            done < <(find $TARGET -type f -executable)
          fi
          
          # Performance profiling
          if [ $LEVEL -ge 20 ]; then
            echo "perf record -g -o analysis/level$LEVEL/perf/trace.data -- $TARGET" > analysis/level$LEVEL/perf/commands.sh
          fi
          
          # QEMU trace
          if [ $LEVEL -ge 30 ]; then
            echo "qemu-x86_64 -d in_asm,cpu,exec -D analysis/level$LEVEL/trace/qemu.log $TARGET" > analysis/level$LEVEL/trace/qemu.sh
          fi
          
          # Core dump analysis
          if [ $LEVEL -ge 40 ]; then
            echo "ulimit -c unlimited" > analysis/level$LEVEL/core/setup.sh
            echo "gdb -batch -ex 'bt full' $TARGET core" >> analysis/level$LEVEL/core/analyze.sh
          fi
          
          # LLVM IR
          if [ $LEVEL -ge 50 ]; then
            find $TARGET -name "*.bc" -o -name "*.ll" > analysis/level$LEVEL/build/llvm-ir.txt
          fi
          
          # BPF tracing
          if [ $LEVEL -ge 60 ]; then
            echo "bpftrace -e 'tracepoint:syscalls:sys_enter_* { @[probe] = count(); }'" > analysis/level$LEVEL/trace/bpf.sh
          fi
          
          # Full spectrum
          if [ $LEVEL -ge 70 ]; then
            ${pkgs.strace}/bin/strace -o analysis/level$LEVEL/trace/syscalls.log -f -e trace=all $TARGET 2>&1 || true
          fi
          
          echo "Analysis complete: analysis/level$LEVEL/"
        '';
      };
      
      devShells.${system} = builtins.listToAttrs (
        map (level: {
          name = "level${toString level}";
          value = pkgs.mkShell {
            buildInputs = (mkAnalysisMode level).tools ++ [
              self.packages.${system}.analyzer
              pipelight.packages.${system}.default or pipelight.defaultPackage.${system}
            ];
            shellHook = ''
              echo "Analysis Level ${toString level} environment"
              echo "Run: analyze ${toString level} <target>"
            '';
          };
        }) analysisLevels
      ) // {
        default = pkgs.mkShell {
          buildInputs = [ self.packages.${system}.analyzer ];
        };
      };
    };
}
