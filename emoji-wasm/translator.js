// English ↔ Emoji Translator (Pure JavaScript)

const EMOJI_MAP = {
  // Core CICADA-71
  'magic': '🔮', 'energy': '⚡', 'hole': '🕳️', 'ikea': '🛋️', 'spiral': '🌀',
  'sparkle': '✨', 'music': '🎵', 'lock': '🔐', 'math': '📐', 'wave': '🌊',
  'abacus': '🧮', 'mask': '🎭', 'moon': '🌙', 'star': '⭐', 'science': '🔬',
  'art': '🎨', 'temple': '🏛️', 'rainbow': '🌈', 'fire': '🔥', 'comet': '💫',
  
  // Math terms
  'hecke': '🔮', 'maass': '🌀', 'mock': '🎭', 'shadow': '🕳️', 'harmonic': '🎵',
  'zen': '🌙', 'proof': '✅', 'shard': '💎', 'jail': '🔒', 'sus': '🚨',
  'prime': '🔢', 'gandalf': '🧙', 'eternal': '♾️', 'ephemeral': '⏳',
  'ontology': '📚', 'operator': '⚙️', 'form': '📋', 'modular': '🧩',
  'automorphic': '🔄', 'moonshine': '🌙✨', 'monster': '👹', 'group': '👥',
  'supersingular': '⭐⭐', 'elliptic': '⭕', 'curve': '〰️', 'invariant': '🔒',
  'coefficient': '🔢', 'theorem': '📐', 'lemma': '📝', 'conjecture': '❓',
  'axiom': '⚖️', 'qed': '✅', 'verify': '✔️', 'witness': '👁️', 'groth16': '🔐',
  
  // Numbers
  '71': '7️⃣1️⃣', '72': '7️⃣2️⃣', '73': '7️⃣3️⃣',
  
  // Actions
  'compile': '⚙️', 'build': '🔨', 'deploy': '🚀', 'test': '🧪', 'run': '▶️'
};

const REVERSE_MAP = Object.fromEntries(
  Object.entries(EMOJI_MAP).map(([k, v]) => [v, k])
);

function englishToEmoji(text) {
  return text.toLowerCase()
    .split(/\s+/)
    .map(word => EMOJI_MAP[word] || word)
    .join(' ');
}

function emojiToEnglish(text) {
  return text.split(/\s+/)
    .map(emoji => REVERSE_MAP[emoji] || emoji)
    .join(' ');
}

// WASM-compatible exports
if (typeof Module !== 'undefined') {
  Module.englishToEmoji = englishToEmoji;
  Module.emojiToEnglish = emojiToEnglish;
}

// Node.js exports
if (typeof module !== 'undefined') {
  module.exports = { englishToEmoji, emojiToEnglish, EMOJI_MAP };
}

// Browser global
if (typeof window !== 'undefined') {
  window.EmojiTranslator = { englishToEmoji, emojiToEnglish };
}
