# Free-Tier AI Resources for CICADA-71

## API Keys Setup

```bash
# Create config directories
mkdir -p ~/.config/{gemini,anthropic,openai,huggingface}

# Add API keys (get from respective platforms)
echo "YOUR_KEY_HERE" > ~/.config/gemini/api_key
echo "YOUR_KEY_HERE" > ~/.config/anthropic/api_key
echo "YOUR_KEY_HERE" > ~/.config/openai/api_key
echo "YOUR_KEY_HERE" > ~/.config/huggingface/token
```

---

## Free-Tier AI Services

### 1. Google Gemini (Free)
- **Model**: gemini-pro
- **Limits**: 60 requests/minute
- **Get Key**: https://makersuite.google.com/app/apikey
- **Cost**: Free

```bash
curl https://generativelanguage.googleapis.com/v1beta/models/gemini-pro:generateContent \
  -H "x-goog-api-key: $GEMINI_API_KEY" \
  -d '{"contents":[{"parts":[{"text":"Analyze this"}]}]}'
```

### 2. Anthropic Claude (Free Trial)
- **Model**: claude-3-haiku-20240307
- **Limits**: $5 free credit
- **Get Key**: https://console.anthropic.com/
- **Cost**: Free trial, then $0.25/1M tokens

```bash
curl https://api.anthropic.com/v1/messages \
  -H "x-api-key: $ANTHROPIC_API_KEY" \
  -H "anthropic-version: 2023-06-01" \
  -d '{"model":"claude-3-haiku-20240307","max_tokens":1024,"messages":[{"role":"user","content":"Analyze"}]}'
```

### 3. OpenAI GPT (Free Trial)
- **Model**: gpt-3.5-turbo
- **Limits**: $5 free credit
- **Get Key**: https://platform.openai.com/api-keys
- **Cost**: Free trial, then $0.50/1M tokens

```bash
curl https://api.openai.com/v1/chat/completions \
  -H "Authorization: Bearer $OPENAI_API_KEY" \
  -d '{"model":"gpt-3.5-turbo","messages":[{"role":"user","content":"Analyze"}]}'
```

### 4. Ollama (Local, Free)
- **Model**: llama3.2, mistral, phi3
- **Limits**: None (local)
- **Install**: https://ollama.ai/
- **Cost**: Free (uses local GPU/CPU)

```bash
# Install
curl -fsSL https://ollama.ai/install.sh | sh

# Run
ollama run llama3.2

# API
curl http://localhost:11434/api/generate \
  -d '{"model":"llama3.2","prompt":"Analyze","stream":false}'
```

### 5. Hugging Face (Free)
- **Models**: Many open models
- **Limits**: Rate limited
- **Get Token**: https://huggingface.co/settings/tokens
- **Cost**: Free

```bash
curl https://api-inference.huggingface.co/models/meta-llama/Llama-2-7b-chat-hf \
  -H "Authorization: Bearer $HF_TOKEN" \
  -d '{"inputs":"Analyze this"}'
```

### 6. Groq (Free)
- **Model**: llama3-70b, mixtral-8x7b
- **Limits**: 14,400 requests/day
- **Get Key**: https://console.groq.com/
- **Cost**: Free

```bash
curl https://api.groq.com/openai/v1/chat/completions \
  -H "Authorization: Bearer $GROQ_API_KEY" \
  -d '{"model":"llama3-70b-8192","messages":[{"role":"user","content":"Analyze"}]}'
```

### 7. Together AI (Free Trial)
- **Models**: Many open models
- **Limits**: $25 free credit
- **Get Key**: https://api.together.xyz/
- **Cost**: Free trial

```bash
curl https://api.together.xyz/v1/chat/completions \
  -H "Authorization: Bearer $TOGETHER_API_KEY" \
  -d '{"model":"meta-llama/Llama-3-70b-chat-hf","messages":[{"role":"user","content":"Analyze"}]}'
```

### 8. Cohere (Free Trial)
- **Model**: command, command-light
- **Limits**: 100 requests/minute
- **Get Key**: https://dashboard.cohere.com/
- **Cost**: Free trial

```bash
curl https://api.cohere.ai/v1/generate \
  -H "Authorization: Bearer $COHERE_API_KEY" \
  -d '{"model":"command","prompt":"Analyze"}'
```

### 9. Mistral AI (Free Trial)
- **Model**: mistral-tiny, mistral-small
- **Limits**: Free tier available
- **Get Key**: https://console.mistral.ai/
- **Cost**: Free tier

```bash
curl https://api.mistral.ai/v1/chat/completions \
  -H "Authorization: Bearer $MISTRAL_API_KEY" \
  -d '{"model":"mistral-tiny","messages":[{"role":"user","content":"Analyze"}]}'
```

### 10. Perplexity (Free Trial)
- **Model**: pplx-7b-online, pplx-70b-online
- **Limits**: $5 free credit
- **Get Key**: https://www.perplexity.ai/settings/api
- **Cost**: Free trial

```bash
curl https://api.perplexity.ai/chat/completions \
  -H "Authorization: Bearer $PERPLEXITY_API_KEY" \
  -d '{"model":"pplx-7b-online","messages":[{"role":"user","content":"Analyze"}]}'
```

---

## Usage in Pipelight

```bash
# Run swab with all free-tier AI
pipelight run swab_deck

# Run specific AI analysis
nix develop .#gemini-cli -c gemini-analyze-shards
nix develop .#claude-cli -c claude-analyze-shards
nix develop .#openai-cli -c gpt-analyze-shards

# Local Ollama (no API key needed)
nix develop .#ollama -c ollama-analyze-shards

# Compute consensus
python3 ai_consensus.py
```

---

## Cost Optimization

### Strategy 1: Rotate Free Trials
- Use Gemini (free) as primary
- Fallback to Ollama (local, free)
- Use paid APIs only for critical analysis

### Strategy 2: Batch Requests
- Collect all analyses
- Send once per day (scheduled via Pipelight)
- Stay within free tier limits

### Strategy 3: Local First
- Run Ollama locally for most tasks
- Use cloud APIs for complex analysis only

---

## Monitoring Usage

```bash
# Check API usage
curl https://generativelanguage.googleapis.com/v1beta/models \
  -H "x-goog-api-key: $GEMINI_API_KEY"

# Ollama stats (local)
curl http://localhost:11434/api/tags

# Check consensus results
cat AI_ANALYSIS.json | jq '.sources'
```

---

## Nix Integration

```nix
# flake.nix already includes:
# - gemini-cli
# - claude-cli
# - openai-cli
# - ollama-cli
# - ai-consensus

# Add more:
groq-cli = pkgs.writeShellScriptBin "groq-analyze-shards" ''
  export GROQ_API_KEY=$(cat ~/.config/groq/api_key)
  curl https://api.groq.com/openai/v1/chat/completions \
    -H "Authorization: Bearer $GROQ_API_KEY" \
    -d '{"model":"llama3-70b-8192","messages":[{"role":"user","content":"Analyze: $(cat HECKE_MAASS_MANIFEST.json)"}]}'
'';
```

---

## Scheduled Execution

```toml
# pipelight.toml
triggers:
  - name: daily_swab
    cron: "0 2 * * *"  # 2 AM daily
    
  - name: weekly_deep_analysis
    cron: "0 3 * * 0"  # 3 AM Sunday
```

---

## Expected Output

```json
{
  "timestamp": "2026-02-01T14:00:00Z",
  "sources": ["gemini", "claude", "gpt", "ollama"],
  "total_insights": 12,
  "categories": {
    "distribution": {
      "count": 4,
      "sources": ["gemini", "claude"],
      "avg_confidence": 0.8
    },
    "optimization": {
      "count": 3,
      "sources": ["gpt", "ollama"],
      "avg_confidence": 0.7
    }
  },
  "recommendations": [
    {
      "priority": "high",
      "action": "Review shard distribution balance",
      "reason": "2 AI sources flagged distribution issues"
    }
  ]
}
```

---

## Contact

- **AI Integration**: ai@solfunmeme.com
- **Technical**: shards@solfunmeme.com

**Free-tier AI. Scheduled swabs. Consensus-driven optimization.** 🤖🔢✨
