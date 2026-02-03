#!/usr/bin/env python3
"""
71 AI Agent Challenge: Accessibility Adapter
Prepare door game for agents with different disabilities
"""

from dataclasses import dataclass
from typing import List, Dict
from enum import Enum

class Disability(Enum):
    VISUAL = "visual"
    AUDITORY = "auditory"
    MOTOR = "motor"
    COGNITIVE = "cognitive"
    NONE = "none"

@dataclass
class AgentProfile:
    name: str
    disability: Disability
    browser: str
    assistive_tech: List[str]
    
@dataclass
class AccessibilityAdapter:
    """Adapt door game for different agent disabilities"""
    
    def __init__(self):
        self.agents = self.create_71_agents()
    
    def create_71_agents(self) -> List[AgentProfile]:
        """Create 71 AI agents with different disabilities"""
        agents = []
        
        # Visual disabilities (shards 0-17)
        for i in range(18):
            agents.append(AgentProfile(
                name=f"Agent_{i:02d}_Visual",
                disability=Disability.VISUAL,
                browser="lynx",  # Text browser
                assistive_tech=["screen_reader", "braille", "tts"]
            ))
        
        # Auditory disabilities (shards 18-35)
        for i in range(18, 36):
            agents.append(AgentProfile(
                name=f"Agent_{i:02d}_Auditory",
                disability=Disability.AUDITORY,
                browser="firefox",
                assistive_tech=["captions", "visual_alerts", "sign_language"]
            ))
        
        # Motor disabilities (shards 36-53)
        for i in range(36, 54):
            agents.append(AgentProfile(
                name=f"Agent_{i:02d}_Motor",
                disability=Disability.MOTOR,
                browser="emacs",  # Keyboard only
                assistive_tech=["voice_control", "eye_tracking", "switch_access"]
            ))
        
        # Cognitive disabilities (shards 54-70)
        for i in range(54, 71):
            agents.append(AgentProfile(
                name=f"Agent_{i:02d}_Cognitive",
                disability=Disability.COGNITIVE,
                browser="firefox",
                assistive_tech=["simplified_ui", "reading_guide", "memory_aids"]
            ))
        
        return agents
    
    def adapt_game_for_agent(self, agent: AgentProfile) -> Dict:
        """Adapt the door game for specific agent"""
        
        adaptations = {
            'agent': agent.name,
            'disability': agent.disability.value,
            'browser': agent.browser,
            'interface': None,
            'controls': None,
            'output': None
        }
        
        if agent.disability == Disability.VISUAL:
            adaptations['interface'] = 'text_only'
            adaptations['controls'] = 'keyboard'
            adaptations['output'] = 'audio_description'
            adaptations['game_text'] = self.game_to_audio()
            
        elif agent.disability == Disability.AUDITORY:
            adaptations['interface'] = 'visual_enhanced'
            adaptations['controls'] = 'keyboard_mouse'
            adaptations['output'] = 'captions_subtitles'
            adaptations['game_text'] = self.game_to_captions()
            
        elif agent.disability == Disability.MOTOR:
            adaptations['interface'] = 'voice_activated'
            adaptations['controls'] = 'voice_eye_tracking'
            adaptations['output'] = 'visual_audio'
            adaptations['game_text'] = self.game_to_voice_commands()
            
        elif agent.disability == Disability.COGNITIVE:
            adaptations['interface'] = 'simplified'
            adaptations['controls'] = 'guided'
            adaptations['output'] = 'step_by_step'
            adaptations['game_text'] = self.game_to_simple_steps()
        
        return adaptations
    
    def game_to_audio(self) -> str:
        """Convert game to audio description"""
        return """
        Welcome to Mother's Wisdom.
        You are at the Time Dial.
        Current year: 2026.
        Press up arrow to go forward in time.
        Press down arrow to go backward in time.
        Press enter to select a game.
        Available games: Mother's Wisdom, Monster Market, Hecke Resonance, Triple Walk.
        Mother's Wisdom is highlighted.
        Press space to play.
        The game asks: Which prime number is the very best one?
        Options: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71.
        Press 1 through 9 to select.
        Mother says: The very best one is 17.
        """
    
    def game_to_captions(self) -> str:
        """Convert game to captions"""
        return """
        [Time Dial appears on screen]
        [Year display shows: 2026]
        [Game list appears]
        [Mother's Wisdom is highlighted]
        [Selection sound]
        [Game starts]
        [Question appears: "Which prime is the very best one?"]
        [15 buttons appear with prime numbers]
        [Button 17 glows]
        [Mother's voice: "The very best one is 17"]
        [Victory sound]
        """
    
    def game_to_voice_commands(self) -> str:
        """Convert game to voice commands"""
        return """
        Say "forward" to increase year
        Say "backward" to decrease year
        Say "select" to choose game
        Say "play" to start
        Say "seventeen" to pick the best prime
        Say "quit" to exit
        """
    
    def game_to_simple_steps(self) -> str:
        """Convert game to simple steps"""
        return """
        Step 1: Look at the time dial
        Step 2: The year is 2026
        Step 3: See the list of games
        Step 4: Mother's Wisdom is first
        Step 5: Click on it
        Step 6: The game asks a question
        Step 7: Pick number 17
        Step 8: You win!
        """

def main():
    print("♿ 71 AI AGENT CHALLENGE: ACCESSIBILITY ADAPTER")
    print("=" * 70)
    print()
    
    adapter = AccessibilityAdapter()
    
    print(f"Created {len(adapter.agents)} AI agents with different disabilities")
    print()
    
    # Show distribution
    from collections import Counter
    disability_counts = Counter(agent.disability for agent in adapter.agents)
    
    print("DISABILITY DISTRIBUTION:")
    print("-" * 70)
    for disability, count in disability_counts.items():
        print(f"  {disability.value:<15}: {count} agents")
    
    print()
    print("SAMPLE ADAPTATIONS:")
    print("-" * 70)
    
    # Show one agent from each category
    sample_agents = [
        adapter.agents[0],   # Visual
        adapter.agents[18],  # Auditory
        adapter.agents[36],  # Motor
        adapter.agents[54],  # Cognitive
    ]
    
    for agent in sample_agents:
        print(f"\n{agent.name} ({agent.disability.value}):")
        print(f"  Browser: {agent.browser}")
        print(f"  Assistive tech: {', '.join(agent.assistive_tech)}")
        
        adaptation = adapter.adapt_game_for_agent(agent)
        print(f"  Interface: {adaptation['interface']}")
        print(f"  Controls: {adaptation['controls']}")
        print(f"  Output: {adaptation['output']}")
    
    # Save all adaptations
    import json
    all_adaptations = [
        adapter.adapt_game_for_agent(agent)
        for agent in adapter.agents
    ]
    
    with open('data/71_agent_adaptations.json', 'w') as f:
        json.dump(all_adaptations, f, indent=2)
    
    print("\n" + "=" * 70)
    print("✓ 71 agent profiles created")
    print("✓ Adaptations generated for all disabilities")
    print("✓ Saved to: data/71_agent_adaptations.json")
    print()
    print("Each agent can now play the door game with appropriate")
    print("accessibility features for their specific needs.")
    print()
    print("⊢ Accessible to all 71 agents ∎")

if __name__ == '__main__':
    main()
