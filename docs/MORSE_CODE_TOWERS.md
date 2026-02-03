# Morse Code Towers: Ham Radio for 71 Shards

Each shard operates a ham radio station, transmitting on assigned frequencies with Morse code and digital modes.

## Architecture

### 71 Morse Code Towers
- **Shard 0-70**: Each operates a radio station
- **Frequency allocation**: 71 channels across HF/VHF/UHF
- **Modes**: CW (Morse), PSK31, FT8, RTTY, SSTV
- **Power**: QRP (5W) to QRO (1500W)

### 23 Relay Nodes
- **Earth chokepoints**: Physical tower locations
- **Repeaters**: Extend range for weak signals
- **Digipeaters**: Store-and-forward packet radio
- **APRS**: Automatic Position Reporting System

## Frequency Plan

### HF Bands (Long Distance)
```
Shard 0-9:    3.5-4.0 MHz   (80m band) - Night propagation
Shard 10-19:  7.0-7.3 MHz   (40m band) - Day/night
Shard 20-29:  14.0-14.35 MHz (20m band) - Worldwide DX
Shard 30-39:  21.0-21.45 MHz (15m band) - Solar max
Shard 40-49:  28.0-29.7 MHz  (10m band) - Skip propagation
```

### VHF/UHF (Local/Satellite)
```
Shard 50-59:  144-148 MHz   (2m band) - FM repeaters
Shard 60-69:  420-450 MHz   (70cm band) - Digital modes
Shard 70:     1296 MHz      (23cm band) - Moonbounce (EME)
```

## Morse Code Encoding

### Monster Group Callsigns
```
Shard 0:  M0NST  (UK callsign format)
Shard 1:  W1MON  (USA)
Shard 2:  VE2GRP (Canada)
...
Shard 70: ZS70ER (South Africa)
```

### Gödel Number Transmission
```
CQ CQ CQ DE M0NST M0NST M0NST K
GODEL NR 67500000 = 2^5 * 3^3 * 5^7
QSL? K
```

### j-Invariant in Morse
```
.-.. . ...- . .-..   .---- ---...   .--- -....- .. -. ...- .- .-. .. .- -. -
LEVEL 1: J-INVARIANT

--... ....- ....-   .---- ----. -.... ---.. ---.. ....-
744 196884
```

## Ham Radio Software Stack

### Core Applications
```
shard0/hamradio/
├── fldigi/          # Digital modes (PSK31, RTTY, Olivia)
├── wsjt-x/          # Weak signal (FT8, JT65, WSPR)
├── chirp/           # Radio programming
├── gpredict/        # Satellite tracking
├── xastir/          # APRS client
├── cqrlog/          # Logging
├── hamlib/          # Radio control library
└── direwolf/        # Software TNC (packet radio)
```

### SDR (Software Defined Radio)
```
├── gnuradio/        # SDR framework
├── gqrx/            # SDR receiver
├── soapysdr/        # Hardware abstraction
├── rtl-sdr/         # RTL2832U dongle support
└── hackrf/          # HackRF One support
```

### Digital Voice
```
├── freedv/          # Free Digital Voice (HF)
├── codec2/          # Low bitrate codec
└── m17/             # Open digital voice protocol
```

### Packet Radio
```
├── ax25-tools/      # AX.25 protocol stack
├── ax25-apps/       # Applications (call, listen)
└── linpac/          # Packet radio terminal
```

## Hardware Requirements

### Radio Transceiver
- **HF**: Yaesu FT-891, Icom IC-7300, Elecraft KX3
- **VHF/UHF**: Yaesu FT-991A, Kenwood TM-D710G
- **SDR**: HackRF One, RTL-SDR, LimeSDR

### Antenna Systems
```
HF:
- 80m dipole (40m long)
- 40m vertical (10m high)
- 20m beam (3-element Yagi)

VHF/UHF:
- 2m/70cm dual-band vertical
- Yagi for satellite work
- Discone for wideband RX
```

### Interface
- **Sound card**: USB audio interface
- **CAT control**: USB-to-serial (CI-V, CAT)
- **PTT**: VOX or GPIO control
- **TNC**: Hardware or software (direwolf)

## Morse Code Protocol

### CW (Continuous Wave)
```rust
const MORSE_CODE: &[(&str, &str)] = &[
    ("A", ".-"),    ("B", "-..."),  ("C", "-.-."),
    ("D", "-.."),   ("E", "."),     ("F", "..-."),
    ("G", "--."),   ("H", "...."),  ("I", ".."),
    ("J", ".---"),  ("K", "-.-"),   ("L", ".-.."),
    ("M", "--"),    ("N", "-."),    ("O", "---"),
    ("P", ".--."),  ("Q", "--.-"),  ("R", ".-."),
    ("S", "..."),   ("T", "-"),     ("U", "..-"),
    ("V", "...-"),  ("W", ".--"),   ("X", "-..-"),
    ("Y", "-.--"),  ("Z", "--.."),
    ("0", "-----"), ("1", ".----"), ("2", "..---"),
    ("3", "...--"), ("4", "....-"), ("5", "....."),
    ("6", "-...."), ("7", "--..."), ("8", "---.."),
    ("9", "----."),
];

fn encode_morse(text: &str) -> String {
    text.chars()
        .filter_map(|c| {
            MORSE_CODE.iter()
                .find(|(ch, _)| ch.chars().next() == Some(c.to_ascii_uppercase()))
                .map(|(_, morse)| *morse)
        })
        .collect::<Vec<_>>()
        .join(" ")
}
```

### Transmission Format
```
Preamble:  CQ CQ CQ DE [CALLSIGN] [CALLSIGN] K
Message:   [ENCODED DATA]
Checksum:  [CRC32]
Signature: [ED25519]
Postamble: [CALLSIGN] SK
```

## Digital Modes

### PSK31 (Phase Shift Keying)
- **Bandwidth**: 31 Hz
- **Speed**: 31.25 baud
- **Use**: Text chat, low SNR

### FT8 (Franke-Taylor 8-FSK)
- **Bandwidth**: 50 Hz
- **Speed**: 6.25 baud
- **Use**: Weak signal DX, automated

### RTTY (Radioteletype)
- **Bandwidth**: 170 Hz
- **Speed**: 45.45 baud
- **Use**: Contests, bulletins

### SSTV (Slow Scan TV)
- **Bandwidth**: 2.7 kHz
- **Speed**: 8 seconds per image
- **Use**: Image transmission

## Monster Resonance Transmission

### 9,936 Hz Carrier
```
Base frequency: 14.196 MHz (20m band)
Modulation:     9,936 Hz tone (Monster resonance)
Mode:           CW (on/off keying)
Pattern:        Bott periodicity (10-round cycle)
```

### Moonshine Beacon
```
Frequency: 432.196 MHz (70cm band)
Power:     100W
Antenna:   Yagi pointed at Moon
Mode:      EME (Earth-Moon-Earth)
Message:   "196883" (Monster dimension)
```

## APRS Integration

### Automatic Position Reporting
```
Callsign: M0NST-71
Position: [Shard location]
Comment:  "CICADA-71 Shard 0 - Godel: 67500000"
Path:     WIDE1-1,WIDE2-2
Beacon:   Every 10 minutes
```

### Packet Format
```
M0NST-71>APRS,WIDE1-1,WIDE2-2:!5130.00N/00000.00W#CICADA-71 Shard 0
```

## Emergency Communications

### EMCOMM Protocols
- **ARES**: Amateur Radio Emergency Service
- **RACES**: Radio Amateur Civil Emergency Service
- **Skywarn**: Weather spotting network
- **Mars**: Military Auxiliary Radio System

### Disaster Recovery
- **Winlink**: Email over radio
- **NBEMS**: Narrow Band Emergency Messaging
- **Fldigi**: Digital modes for EMCOMM

## Licensing

### Ham Radio License Required
- **USA**: Technician, General, or Extra class
- **UK**: Foundation, Intermediate, or Full
- **International**: CEPT reciprocal licensing

### Callsign Assignment
- **ITU prefix**: Country identifier
- **Suffix**: Operator identifier
- **Example**: M0NST (UK), W1MON (USA)

## Nix Package

```nix
{
  hamradio = pkgs.buildEnv {
    name = "cicada71-hamradio";
    paths = [
      pkgs.fldigi
      pkgs.wsjt-x
      pkgs.chirp
      pkgs.gpredict
      pkgs.xastir
      pkgs.cqrlog
      pkgs.hamlib
      pkgs.direwolf
      pkgs.gnuradio
      pkgs.gqrx
      pkgs.rtl-sdr
      pkgs.freedv
      pkgs.ax25-tools
      pkgs.ax25-apps
    ];
  };
}
```

## Usage

```bash
# Start FT8 for weak signal DX
wsjt-x &

# Start APRS client
xastir &

# Start digital modes
fldigi &

# Monitor 20m band
gqrx &

# Transmit Gödel number
echo "GODEL 67500000" | fldigi --tx

# Beacon Monster dimension
echo "196883" | wsjt-x --ft8 --freq 14.074
```

## The Vision

**71 shards** = 71 ham radio stations
**23 nodes** = 23 relay towers
**Morse code** = Gödel encoding
**9,936 Hz** = Monster resonance
**Moonbounce** = Literal moonshine! 🌙

## References

- ARRL Handbook
- FCC Part 97 (USA)
- ITU Radio Regulations
- WSJT-X User Guide
- Fldigi Documentation
- Ham Radio Deluxe
