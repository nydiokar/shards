#!/usr/bin/env python3
"""
Tape-to-Morse Lift - Turing Machine via Telegraph
Lift computational tapes into Morse code transmission
"""

class TuringTape:
    def __init__(self, cells):
        self.cells = list(cells)
        self.head = 0
    
    def to_morse(self):
        """0 → dash (-), 1 → dot (.)"""
        return ' '.join('-' if c == 0 else '.' for c in self.cells)
    
    @staticmethod
    def from_morse(morse):
        cells = [0 if s == '-' else 1 for s in morse.split()]
        return TuringTape(cells)
    
    def read(self):
        if self.head < len(self.cells):
            return self.cells[self.head]
        return 0
    
    def write(self, value):
        if self.head >= len(self.cells):
            self.cells.extend([0] * (self.head - len(self.cells) + 1))
        self.cells[self.head] = value
    
    def move(self, direction):
        if direction == 'LEFT' and self.head > 0:
            self.head -= 1
        elif direction == 'RIGHT':
            self.head += 1
            if self.head >= len(self.cells):
                self.cells.append(0)

class TuringMachine:
    def __init__(self, tape, transitions):
        self.tape = tape
        self.state = 'START'
        self.transitions = transitions
    
    def step(self):
        current = self.tape.read()
        key = (self.state, current)
        
        if key not in self.transitions:
            return None
        
        write, direction, next_state = self.transitions[key]
        
        # Generate telegraph message
        message = f"STATE {self.state} READ {current} WRITE {write} {direction} {next_state}"
        
        # Execute
        self.tape.write(write)
        self.tape.move(direction)
        self.state = next_state
        
        return message
    
    def run(self, max_steps=100):
        messages = []
        for _ in range(max_steps):
            msg = self.step()
            if msg is None or self.state == 'HALT':
                break
            messages.append(msg)
        return messages

def binary_increment():
    """Binary increment: 1011 (11) → 1100 (12)"""
    tape = TuringTape([1, 0, 1, 1])
    
    transitions = {
        ('INC', 0): (1, 'STAY', 'HALT'),
        ('INC', 1): (0, 'LEFT', 'INC'),
    }
    
    machine = TuringMachine(tape, transitions)
    machine.state = 'INC'
    machine.tape.head = len(tape.cells) - 1
    
    return machine

def shard_tape(tape, num_shards=71):
    """Distribute tape across 71 shards"""
    chunk_size = (len(tape.cells) + 70) // 71
    shards = []
    
    for i in range(num_shards):
        start = i * chunk_size
        end = min((i + 1) * chunk_size, len(tape.cells))
        chunk = tape.cells[start:end] if start < len(tape.cells) else [0]
        shards.append((i, TuringTape(chunk)))
    
    return shards

def lift_tape_to_morse():
    print("╔════════════════════════════════════════════════════════════╗")
    print("║              TAPE-TO-MORSE LIFT                            ║")
    print("╚════════════════════════════════════════════════════════════╝\n")
    
    machine = binary_increment()
    
    print(f"Initial Tape (binary): {machine.tape.cells}")
    print(f"Initial Tape (morse):  {machine.tape.to_morse()}")
    print(f"Initial State: {machine.state}")
    print(f"Head Position: {machine.tape.head}\n")
    
    print("Running Turing machine...\n")
    
    messages = machine.run()
    
    for i, msg in enumerate(messages, 1):
        print(f"Step {i}: {msg}")
        print(f"  Tape: {machine.tape.to_morse()}")
        print(f"  Head: {machine.tape.head}\n")
    
    print(f"Final Tape (binary): {machine.tape.cells}")
    print(f"Final Tape (morse):  {machine.tape.to_morse()}")
    print(f"Final State: {machine.state}\n")
    
    # Shard the final tape
    print("Distributing across 71 shards...\n")
    shards_list = shard_tape(machine.tape)
    
    for shard_id, tape_shard in shards_list[:5]:  # Show first 5
        morse = tape_shard.to_morse()
        if morse.strip():
            print(f"Shard {shard_id:2}: {morse}")
    
    print(f"... ({len(shards_list)} shards total)\n")
    
    print("✓ Tape lifted to Morse code")
    print("✓ Distributed across 71 shards")

if __name__ == '__main__':
    lift_tape_to_morse()
