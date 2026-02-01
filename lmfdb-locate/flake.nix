{
  description = "LMFDB file locator - produces complete file list";

  outputs = { self, nixpkgs ? import <nixpkgs> {} }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system} or nixpkgs;
    in
    {
      packages.${system}.default = pkgs.runCommand "lmfdb-filelist" {
        buildInputs = [ pkgs.mlocate pkgs.findutils ];
      } ''
        mkdir -p $out
        
        echo "🔮 Running locate for LMFDB files..."
        
        # Use locate if available, fallback to find
        if command -v locate &> /dev/null; then
          locate lmfdb 2>/dev/null > $out/lmfdb_files.txt || true
        else
          find /home -name "*lmfdb*" 2>/dev/null > $out/lmfdb_files.txt || true
        fi
        
        # Count and summarize
        total=$(wc -l < $out/lmfdb_files.txt)
        
        cat > $out/summary.txt << EOF
🔮⚡ LMFDB File List
Generated: $(date)
Total files: $total

File list: $out/lmfdb_files.txt
EOF
        
        cat $out/summary.txt
      '';
      
      apps.${system}.default = {
        type = "app";
        program = "${pkgs.writeShellScript "locate-lmfdb" ''
          ${pkgs.mlocate}/bin/locate lmfdb 2>/dev/null || \
          ${pkgs.findutils}/bin/find /home -name "*lmfdb*" 2>/dev/null
        ''}";
      };
    };
}
