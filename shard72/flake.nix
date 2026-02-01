{
  description = "Shard 72 - The Impure Hole";

  outputs = { self, nixpkgs }: {
    packages.x86_64-linux = let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in {
      # IMPURE: IKEA price scraper
      ikea-scraper = pkgs.writeShellScriptBin "ikea-scraper" ''
        #!/usr/bin/env bash
        echo "🛋️ IMPURE: Fetching IKEA prices..."
        ${pkgs.curl}/bin/curl -s "https://www.ikea.com/us/en/cat/bookcases-10382/" | \
          ${pkgs.gnugrep}/bin/grep -oP 'price":\s*\K[0-9.]+' | \
          head -10
      '';
      
      # IMPURE: Timestamp generator
      timestamp = pkgs.writeShellScriptBin "timestamp" ''
        #!/usr/bin/env bash
        echo "⏰ IMPURE: Current time"
        date +%s
      '';
      
      # IMPURE: Random entropy
      entropy = pkgs.writeShellScriptBin "entropy" ''
        #!/usr/bin/env bash
        echo "🎲 IMPURE: Random bytes"
        head -c 32 /dev/urandom | base64
      '';
      
      # IMPURE: Network test
      network-test = pkgs.writeShellScriptBin "network-test" ''
        #!/usr/bin/env bash
        echo "🌐 IMPURE: Network access"
        ${pkgs.curl}/bin/curl -s https://api.github.com/zen
      '';
      
      # IMPURE: File mutation
      mutate = pkgs.writeShellScriptBin "mutate" ''
        #!/usr/bin/env bash
        echo "📝 IMPURE: Writing to /tmp/shard72.log"
        echo "$(date): $*" >> /tmp/shard72.log
        tail -5 /tmp/shard72.log
      '';
    };
  };
}
