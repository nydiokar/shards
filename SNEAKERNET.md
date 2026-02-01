# Wireless & Steganography Sneakernet for 71 Shards

## Overview

Extend Class 6 (Dead Drops) with wireless short-range and steganography methods for air-gapped, covert shard distribution.

## Wireless Methods

### Bluetooth Sneakernet (Shards 6, 13, 20)

**Mechanism**: Bluetooth Low Energy (BLE) GATT + OBEX file transfer

**Range**: 10-100m depending on class (Class 1: 100m, Class 2: 10m)

**Throughput**: ~1-3 Mbps (BLE 5.0: up to 2 Mbps)

**Linux Tools**:
```bash
# Scan for nearby shards
bluetoothctl scan on

# Pair with shard 6
bluetoothctl pair AA:BB:CC:DD:EE:06

# Send parquet file
obexftp -b AA:BB:CC:DD:EE:06 -p shard06.parquet

# Auto-exchange script
bluez-obex-agent --auto-accept /tmp/shard-exchange/
```

**Nix Derivation**:
```nix
{ pkgs, ... }:
pkgs.writeShellScriptBin "bluetooth-shard-exchange" ''
  ${pkgs.bluez}/bin/bluetoothctl << EOF
  power on
  agent on
  default-agent
  scan on
  EOF
  
  # Wait for shard devices
  sleep 5
  
  # Auto-pair and transfer
  for mac in $(bluetoothctl devices | grep "Shard-" | cut -d' ' -f2); do
    ${pkgs.bluez}/bin/bluetoothctl pair $mac
    ${pkgs.obexftp}/bin/obexftp -b $mac -p /var/lib/shard/proposals.parquet
  done
''
```

### WiFi Mesh (Shards 27, 34, 41)

**Mechanism**: 802.11s mesh + BATMAN-adv (Better Approach To Mobile Ad-hoc Networking)

**Range**: 100-300m per hop, multi-hop capable

**Throughput**: 10-100 Mbps depending on 802.11n/ac

**Linux Setup**:
```bash
# Create mesh interface
iw dev wlan0 interface add mesh0 type mp

# Join mesh network
iw dev mesh0 mesh join shard-mesh freq 2412

# Enable BATMAN-adv
modprobe batman-adv
batctl if add mesh0
ip link set up dev bat0

# Announce shard availability
batctl gw_mode server 10mbit/2mbit
```

**NixOS Configuration**:
```nix
{ config, pkgs, ... }:
{
  networking.wireless.enable = false;  # Disable wpa_supplicant
  
  systemd.services.mesh-shard = {
    description = "WiFi Mesh Shard Network";
    after = [ "network.target" ];
    wantedBy = [ "multi-user.target" ];
    
    serviceConfig = {
      ExecStart = pkgs.writeScript "mesh-start" ''
        #!${pkgs.bash}/bin/bash
        ${pkgs.iw}/bin/iw dev wlan0 interface add mesh0 type mp
        ${pkgs.iw}/bin/iw dev mesh0 mesh join shard-mesh freq 2412
        ${pkgs.kmod}/bin/modprobe batman-adv
        ${pkgs.batctl}/bin/batctl if add mesh0
        ${pkgs.iproute2}/bin/ip link set up dev bat0
        ${pkgs.iproute2}/bin/ip addr add 10.71.${SHARD_ID}.1/24 dev bat0
      '';
    };
  };
}
```

## Steganography Methods

### Image Steganography (Shards 48, 55)

**Mechanism**: LSB (Least Significant Bit) embedding in PNG/JPG

**Capacity**: ~1 byte per 8 pixels (12.5% of image size)

**Tools**:
```bash
# Embed parquet file in image
steghide embed -cf cover.jpg -ef shard48.parquet -p "monster71"

# Extract
steghide extract -sf cover.jpg -p "monster71"

# Alternative: outguess
outguess -k "monster71" -d shard48.parquet cover.jpg stego.jpg

# Verify
outguess -r stego.jpg extracted.parquet
```

**Nix Derivation**:
```nix
{ pkgs, shard, parquetFile }:
pkgs.runCommand "shard-${toString shard}-stego" {
  buildInputs = [ pkgs.steghide pkgs.imagemagick ];
} ''
  # Generate cover image if needed
  convert -size 1920x1080 xc:white cover.png
  
  # Embed shard data
  steghide embed -cf cover.png -ef ${parquetFile} -p "shard${toString shard}" -f
  
  cp cover.png $out
''
```

**Rust Integration**:
```rust
use steganography::encoder::Encoder;
use steganography::decoder::Decoder;
use steganography::util::file_as_image_buffer;

pub fn embed_shard(cover_path: &str, data: &[u8], output: &str) -> Result<()> {
    let cover = file_as_image_buffer(cover_path)?;
    let encoder = Encoder::new(data, cover);
    let result = encoder.encode_alpha();
    result.save(output)?;
    Ok(())
}

pub fn extract_shard(stego_path: &str) -> Result<Vec<u8>> {
    let stego = file_as_image_buffer(stego_path)?;
    let decoder = Decoder::new(stego);
    Ok(decoder.decode_alpha())
}
```

### QR Code Steganography (Shards 62, 69)

**Mechanism**: QR code encoding with error correction, print/scan

**Capacity**: 
- Version 40 (177×177): 2,953 bytes (binary mode)
- Split large files across multiple QR codes

**Tools**:
```bash
# Encode shard to QR
qrencode -o shard62.png -l H -s 10 < shard62.parquet

# For large files, split first
split -b 2000 shard62.parquet shard62_part_
for part in shard62_part_*; do
  qrencode -o "${part}.png" -l H -s 10 < "$part"
done

# Decode
zbarimg shard62.png > recovered.parquet

# Batch decode
for qr in shard62_part_*.png; do
  zbarimg "$qr" >> recovered.parquet
done
```

**Nix Flake**:
```nix
{ pkgs, ... }:
{
  packages.qr-shard-encoder = pkgs.writeShellScriptBin "qr-shard-encode" ''
    SHARD=$1
    INPUT=$2
    OUTPUT_DIR=$3
    
    mkdir -p "$OUTPUT_DIR"
    
    # Split into 2KB chunks (fits in QR v40)
    ${pkgs.coreutils}/bin/split -b 2000 "$INPUT" "$OUTPUT_DIR/shard${SHARD}_"
    
    # Generate QR codes
    for part in "$OUTPUT_DIR"/shard${SHARD}_*; do
      ${pkgs.qrencode}/bin/qrencode -o "''${part}.png" -l H -s 10 < "$part"
      rm "$part"  # Remove plaintext chunk
    done
    
    echo "Generated QR codes in $OUTPUT_DIR"
  '';
  
  packages.qr-shard-decoder = pkgs.writeShellScriptBin "qr-shard-decode" ''
    INPUT_DIR=$1
    OUTPUT=$2
    
    # Decode all QR codes in order
    for qr in "$INPUT_DIR"/*.png; do
      ${pkgs.zbar}/bin/zbarimg --raw "$qr"
    done > "$OUTPUT"
    
    echo "Decoded to $OUTPUT"
  '';
}
```

## Hybrid Workflows

### Bluetooth + Steganography
```bash
# Shard 6: Embed in image, transfer via Bluetooth
steghide embed -cf cover.jpg -ef shard06.parquet -p "monster71"
obexftp -b AA:BB:CC:DD:EE:06 -p cover.jpg

# Receiver extracts
steghide extract -sf cover.jpg -p "monster71"
```

### WiFi Mesh + QR Backup
```bash
# Primary: Mesh transfer
batctl tp AA:BB:CC:DD:EE:27 shard27.parquet

# Backup: QR code on paper
qrencode -o shard27_backup.png -l H -s 10 < shard27.parquet
lp shard27_backup.png  # Print
```

### Dead Drop + All Methods
```bash
# Shard 69: Maximum redundancy
# 1. File system
cp shard69.parquet /nix/store/shard69-deaddrop/

# 2. Bluetooth
obexftp -b AA:BB:CC:DD:EE:69 -p shard69.parquet

# 3. Mesh
batctl tp AA:BB:CC:DD:EE:69 shard69.parquet

# 4. Image stego
steghide embed -cf cover.jpg -ef shard69.parquet

# 5. QR code
qrencode -o shard69.png -l H < shard69.parquet
```

## Security Considerations

| Method | Encryption | Detectability | Deniability | Throughput |
|--------|-----------|---------------|-------------|------------|
| Bluetooth | Optional (pairing) | High (RF scan) | Low | 1-3 Mbps |
| WiFi Mesh | WPA3 optional | High (802.11 probe) | Low | 10-100 Mbps |
| Image Stego | Passphrase | Low (visual) | High | N/A (offline) |
| QR Code | None (add GPG) | Medium (camera) | Medium | N/A (offline) |

**Recommendations**:
- Bluetooth: Use BLE privacy features, rotate MAC addresses
- Mesh: Encrypt with WPA3-SAE, use hidden SSID
- Stego: Always use strong passphrase, verify with `stegdetect`
- QR: Encrypt data before encoding, use error correction level H

## Integration with Existing Framework

### Rust Implementation
```rust
pub enum SneakernetProtocol {
    Bluetooth { mac: String },
    WiFiMesh { ssid: String },
    ImageStego { cover: PathBuf, password: String },
    QRCode { version: u8 },
}

impl SneakernetProtocol {
    pub fn for_shard(shard: u8) -> Self {
        match shard {
            6 | 13 | 20 => Self::Bluetooth { mac: format!("AA:BB:CC:DD:EE:{:02X}", shard) },
            27 | 34 | 41 => Self::WiFiMesh { ssid: format!("shard-mesh-{}", shard) },
            48 | 55 => Self::ImageStego { 
                cover: PathBuf::from(format!("/tmp/cover{}.jpg", shard)),
                password: format!("monster{}", shard),
            },
            62 | 69 => Self::QRCode { version: 40 },
            _ => Self::Bluetooth { mac: "00:00:00:00:00:00".into() },
        }
    }
}
```

### Lean 4 Formalization
```lean
inductive SneakernetMethod : Type where
  | bluetooth : SneakernetMethod
  | wifiMesh : SneakernetMethod
  | imageStego : SneakernetMethod
  | qrCode : SneakernetMethod

def sneakernetForShard (s : ShardId) : SneakernetMethod :=
  if s.val % 14 = 6 then .bluetooth
  else if s.val % 14 = 13 then .bluetooth
  else if s.val % 27 = 0 then .wifiMesh
  else if s.val % 48 = 0 then .imageStego
  else .qrCode
```

This extends the P2P framework to 71+ permutations with wireless and covert channels!
