#!/bin/bash
# Install Accessibility Tools for 71 AI Agent Challenge
# Support agents with different disabilities

set -e

echo "♿ Installing Accessibility Tools for AI Agents"
echo "=============================================="
echo ""

# 1. Screen Readers
echo "📖 Installing Screen Readers..."
sudo apt-get update
sudo apt-get install -y \
    orca \
    espeak-ng \
    speech-dispatcher \
    festival \
    festvox-us-slt-hts

# 2. Braille Support
echo "⠃ Installing Braille Support..."
sudo apt-get install -y \
    brltty \
    brltty-x11 \
    xbrlapi

# 3. Magnification
echo "🔍 Installing Magnification Tools..."
sudo apt-get install -y \
    kmag \
    xzoom

# 4. Emacs with Accessibility
echo "📝 Installing Emacs with Accessibility..."
sudo apt-get install -y \
    emacs \
    emacspeak \
    emacs-goodies-el

# 5. Firefox with Accessibility
echo "🦊 Installing Firefox with Accessibility..."
sudo apt-get install -y \
    firefox \
    firefox-esr

# 6. Text Browsers (for agents with visual disabilities)
echo "📄 Installing Text Browsers..."
sudo apt-get install -y \
    lynx \
    w3m \
    links2 \
    elinks

# 7. Terminal Accessibility
echo "💻 Installing Terminal Accessibility..."
sudo apt-get install -y \
    tmux \
    screen \
    at-spi2-core

# 8. Python Accessibility Libraries
echo "🐍 Installing Python Accessibility..."
pip3 install --user \
    pyttsx3 \
    speechrecognition \
    pyaudio \
    accessibility

# 9. Node.js Accessibility
echo "📦 Installing Node.js Accessibility..."
npm install -g \
    axe-core \
    pa11y \
    lighthouse

# 10. Create accessibility config
echo "⚙️ Creating Accessibility Configuration..."

cat > ~/.accessibility_config << 'EOF'
# Accessibility Configuration for AI Agents

# Screen Reader
export SCREEN_READER=orca
export TTS_ENGINE=espeak-ng
export TTS_RATE=175
export TTS_PITCH=50

# Braille
export BRAILLE_DEVICE=/dev/ttyUSB0
export BRAILLE_TABLE=en-us-g2.ctb

# Visual
export HIGH_CONTRAST=true
export LARGE_TEXT=true
export FONT_SIZE=16

# Audio
export AUDIO_CUES=true
export SOUND_EFFECTS=true

# Navigation
export KEYBOARD_ONLY=true
export MOUSE_KEYS=true

# Timing
export SLOW_KEYS=true
export BOUNCE_KEYS=true
export STICKY_KEYS=true
EOF

echo ""
echo "✓ Accessibility tools installed!"
echo ""
echo "Installed tools:"
echo "  • Screen readers: orca, espeak-ng"
echo "  • Braille: brltty"
echo "  • Magnification: kmag, xzoom"
echo "  • Emacs: emacspeak"
echo "  • Browsers: firefox, lynx, w3m"
echo "  • Python: pyttsx3, accessibility"
echo "  • Node: axe-core, pa11y"
echo ""
echo "Configuration saved to: ~/.accessibility_config"
