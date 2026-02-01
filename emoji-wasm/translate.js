#!/usr/bin/env node

const { englishToEmoji, emojiToEnglish } = require('./translator.js');

const args = process.argv.slice(2);

if (args.length === 0) {
  console.log('🔮⚡ English ↔ Emoji Translator');
  console.log('');
  console.log('Usage:');
  console.log('  ./translate.js magic energy hole');
  console.log('  ./translate.js 🔮⚡🕳️');
  console.log('');
  console.log('Examples:');
  console.log('  magic energy hole → 🔮 ⚡ 🕳️');
  console.log('  hecke operator eternal → 🔮 ⚙️ ♾️');
  console.log('  proof verify qed → ✅ ✔️ ✅');
  process.exit(0);
}

const input = args.join(' ');

// Detect if input is emoji or english
const hasEmoji = /[\u{1F300}-\u{1F9FF}]/u.test(input);

if (hasEmoji) {
  console.log('Emoji → English:');
  console.log(emojiToEnglish(input));
} else {
  console.log('English → Emoji:');
  console.log(englishToEmoji(input));
}
