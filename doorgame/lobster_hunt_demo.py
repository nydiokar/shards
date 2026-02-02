#!/usr/bin/env python3
"""
TradeWars: The Lobster Hunt - Commodore/Amiga Style Demo
Epic ANSI art demo with scrolling, music, and effects
"""

import sys
import time
import math
import random

# ANSI colors and effects
RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"
BLINK = "\033[5m"

# Colors
BLACK = "\033[30m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
MAGENTA = "\033[35m"
CYAN = "\033[36m"
WHITE = "\033[37m"

# Bright colors
BRED = "\033[91m"
BGREEN = "\033[92m"
BYELLOW = "\033[93m"
BBLUE = "\033[94m"
BMAGENTA = "\033[95m"
BCYAN = "\033[96m"
BWHITE = "\033[97m"

def clear():
    print("\033[2J\033[H", end="")
    sys.stdout.flush()

def move_cursor(x, y):
    print(f"\033[{y};{x}H", end="")

def hide_cursor():
    print("\033[?25l", end="")

def show_cursor():
    print("\033[?25h", end="")

# ANSI Art Frames
LOBSTER = [
    "    /\\___/\\",
    "   ( o   o )",
    "   (  =^=  )",
    "    )     (",
    "   /       \\",
    "  (  )   (  )",
    " (__(__)__(__))"
]

BOAT = [
    "     |\\",
    "     | \\",
    "     |  \\",
    "_____|___\\___",
    "\\___________/"
]

STAR = ["*", ".", "·", "✦", "✧", "★"]

ZIGGURAT = [
    "        ▲",
    "       ███",
    "      █████",
    "     ███████",
    "    █████████",
    "   ███████████",
    "  █████████████"
]

TERMITE_MOUND = [
    "    /\\  /\\",
    "   /  \\/  \\",
    "  /   ||   \\",
    " /    ||    \\",
    "/___________\\"
]

def draw_title_screen():
    """Commodore 64 style title screen"""
    clear()
    
    title = [
        "╔═══════════════════════════════════════════════════════════════════════════╗",
        "║                                                                           ║",
        "║  ████████╗██████╗  █████╗ ██████╗ ███████╗██╗    ██╗ █████╗ ██████╗ ███║",
        "║  ╚══██╔══╝██╔══██╗██╔══██╗██╔══██╗██╔════╝██║    ██║██╔══██╗██╔══██╗██║║",
        "║     ██║   ██████╔╝███████║██║  ██║█████╗  ██║ █╗ ██║███████║██████╔╝███║",
        "║     ██║   ██╔══██╗██╔══██║██║  ██║██╔══╝  ██║███╗██║██╔══██║██╔══██╗╚══║",
        "║     ██║   ██║  ██║██║  ██║██████╔╝███████╗╚███╔███╔╝██║  ██║██║  ██║███║",
        "║     ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝ ╚══════╝ ╚══╝╚══╝ ╚═╝  ╚═╝╚═╝  ╚═╝╚══║",
        "║                                                                           ║",
        "║                    🔮⚡ THE LOBSTER HUNT 📻🦞                            ║",
        "║                                                                           ║",
        "╚═══════════════════════════════════════════════════════════════════════════╝"
    ]
    
    for i, line in enumerate(title):
        move_cursor(1, i + 1)
        print(f"{BCYAN}{line}{RESET}")
        time.sleep(0.1)
    
    move_cursor(1, 15)
    print(f"{BYELLOW}              A DEMO BY THE MONSTER GROUP COLLECTIVE{RESET}")
    move_cursor(1, 17)
    print(f"{BGREEN}                    71 SHARDS • 10-FOLD WAY{RESET}")
    move_cursor(1, 18)
    print(f"{BMAGENTA}                  BOTT PERIODICITY • PERIOD 8{RESET}")
    
    time.sleep(2)

def scroll_text(text, y, color, speed=0.05):
    """Amiga-style horizontal scroller"""
    width = 80
    padded = " " * width + text + " " * width
    
    for i in range(len(padded) - width):
        move_cursor(1, y)
        print(f"{color}{padded[i:i+width]}{RESET}", end="")
        sys.stdout.flush()
        time.sleep(speed)

def draw_starfield(duration=5):
    """Commodore 64 starfield effect"""
    clear()
    stars = []
    
    # Initialize stars
    for _ in range(50):
        stars.append({
            'x': random.randint(1, 80),
            'y': random.randint(1, 24),
            'speed': random.choice([1, 2, 3]),
            'char': random.choice(STAR)
        })
    
    start = time.time()
    while time.time() - start < duration:
        # Move and draw stars
        for star in stars:
            # Erase old position
            move_cursor(star['x'], star['y'])
            print(" ", end="")
            
            # Move star
            star['y'] += star['speed']
            
            # Wrap around
            if star['y'] > 24:
                star['y'] = 1
                star['x'] = random.randint(1, 80)
            
            # Draw new position
            move_cursor(star['x'], star['y'])
            color = random.choice([WHITE, BWHITE, CYAN, BCYAN])
            print(f"{color}{star['char']}{RESET}", end="")
        
        sys.stdout.flush()
        time.sleep(0.05)

def draw_boats_sailing(duration=5):
    """Boats sailing across the screen"""
    clear()
    
    # Draw ocean
    for y in range(15, 25):
        move_cursor(1, y)
        print(f"{BLUE}{'~' * 80}{RESET}")
    
    boat_x = 0
    start = time.time()
    
    while time.time() - start < duration:
        # Erase old boat
        for i, line in enumerate(BOAT):
            move_cursor(boat_x, 10 + i)
            print(" " * len(line), end="")
        
        # Move boat
        boat_x += 2
        if boat_x > 80:
            boat_x = 0
        
        # Draw new boat
        for i, line in enumerate(BOAT):
            move_cursor(boat_x, 10 + i)
            print(f"{BYELLOW}{line}{RESET}", end="")
        
        # Draw lobsters in water
        for _ in range(3):
            lx = random.randint(1, 75)
            ly = random.randint(16, 23)
            move_cursor(lx, ly)
            print(f"{BRED}🦞{RESET}", end="")
        
        sys.stdout.flush()
        time.sleep(0.1)

def draw_ziggurat_rise(duration=3):
    """Ziggurat rising from the ground"""
    clear()
    
    for step in range(len(ZIGGURAT)):
        for i in range(step + 1):
            move_cursor(35, 20 - step + i)
            print(f"{BYELLOW}{ZIGGURAT[i]}{RESET}")
        
        time.sleep(duration / len(ZIGGURAT))

def draw_termite_mound():
    """Termite mound with bugs"""
    clear()
    
    # Draw mound
    for i, line in enumerate(TERMITE_MOUND):
        move_cursor(35, 10 + i)
        print(f"{YELLOW}{line}{RESET}")
    
    # Animate bugs
    for _ in range(20):
        x = random.randint(30, 50)
        y = random.randint(10, 15)
        move_cursor(x, y)
        print(f"{GREEN}•{RESET}", end="")
        sys.stdout.flush()
        time.sleep(0.1)

def draw_song_of_generations():
    """The song that guides the generations"""
    clear()
    
    lyrics = [
        "♪ In the depths where lobsters dwell ♪",
        "♪ Seventy-one shards cast their spell ♪",
        "♪ Through the Monster's ancient way ♪",
        "♪ Bott's period guides the day ♪",
        "",
        "♪ BDI, the class of life ♪",
        "♪ Three-fold symmetry, free from strife ♪",
        "♪ Rooster crows at break of dawn ♪",
        "♪ The hunt continues, ever on ♪"
    ]
    
    for i, line in enumerate(lyrics):
        move_cursor(20, 8 + i)
        for char in line:
            print(f"{BMAGENTA}{char}{RESET}", end="")
            sys.stdout.flush()
            time.sleep(0.03)
        time.sleep(0.3)
    
    time.sleep(2)

def draw_lobster_hunt():
    """The epic lobster hunt scene"""
    clear()
    
    # Draw ocean floor
    for y in range(20, 25):
        move_cursor(1, y)
        print(f"{BLUE}{'≈' * 80}{RESET}")
    
    # Draw lobsters
    lobster_positions = [(10, 15), (30, 17), (50, 16), (70, 18)]
    
    for x, y in lobster_positions:
        for i, line in enumerate(LOBSTER):
            move_cursor(x, y + i)
            print(f"{BRED}{line}{RESET}")
    
    # Draw hunter (boat)
    move_cursor(35, 5)
    print(f"{BGREEN}{'=' * 10}{RESET}")
    move_cursor(37, 6)
    print(f"{BGREEN}HUNTER{RESET}")
    
    time.sleep(3)

def plasma_effect(duration=3):
    """Amiga-style plasma effect"""
    clear()
    
    start = time.time()
    frame = 0
    
    while time.time() - start < duration:
        for y in range(1, 25):
            for x in range(1, 81):
                # Plasma calculation
                value = math.sin(x * 0.1 + frame * 0.1)
                value += math.sin(y * 0.1 + frame * 0.1)
                value += math.sin((x + y) * 0.1 + frame * 0.1)
                
                # Map to color
                if value > 1:
                    color = BRED
                elif value > 0:
                    color = BYELLOW
                elif value > -1:
                    color = BGREEN
                else:
                    color = BCYAN
                
                move_cursor(x, y)
                print(f"{color}█{RESET}", end="")
        
        frame += 1
        sys.stdout.flush()
        time.sleep(0.05)

def credits_scroll():
    """End credits"""
    clear()
    
    credits = [
        "",
        "TRADEWARS: THE LOBSTER HUNT",
        "",
        "A DEMO BY",
        "THE MONSTER GROUP COLLECTIVE",
        "",
        "CODE",
        "Kiro AI • Meta-Introspector",
        "",
        "GRAPHICS",
        "ANSI Art • Commodore 64 Style",
        "",
        "MUSIC",
        "The Song of Generations",
        "Morse Code Symphony",
        "",
        "SPECIAL THANKS",
        "71 Shards",
        "10-Fold Way",
        "Bott Periodicity",
        "Monster Group",
        "",
        "POWERED BY",
        "P2P Gossip Protocol",
        "WebRTC • MCTS AI",
        "Prolog Voice • ZK-RDFa",
        "",
        "🔮⚡📻🦞",
        "",
        "QED",
        ""
    ]
    
    for line in credits:
        move_cursor(30, 12)
        print(f"{BCYAN}{line:^20}{RESET}")
        time.sleep(0.5)
        clear()

def main():
    """Run the full demo"""
    hide_cursor()
    
    try:
        # Title screen
        draw_title_screen()
        time.sleep(2)
        
        # Starfield
        draw_starfield(5)
        
        # Boats sailing
        draw_boats_sailing(5)
        
        # Ziggurat rises
        draw_ziggurat_rise(3)
        time.sleep(1)
        
        # Termite mound
        draw_termite_mound()
        time.sleep(2)
        
        # The song
        draw_song_of_generations()
        
        # The hunt
        draw_lobster_hunt()
        
        # Plasma effect
        plasma_effect(3)
        
        # Credits
        credits_scroll()
        
        # Final screen
        clear()
        move_cursor(30, 12)
        print(f"{BOLD}{BCYAN}THE END{RESET}")
        move_cursor(25, 14)
        print(f"{BGREEN}Press any key to exit...{RESET}")
        
    finally:
        show_cursor()
        print()

if __name__ == "__main__":
    main()
