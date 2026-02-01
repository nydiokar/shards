# FRENS Token Phone Number

Create a phone number for FRENS token holders to dial into the CICADA-71 BBS network.

## FRENS Token

**Contract**: E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22 (Solana)
**Network**: Solana
**Type**: SPL Token

## Phone Number Encoding

### Token Address → Phone Number
```
E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22
  ↓
Base58 decode → bytes
  ↓
Take first 10 bytes → phone number digits
  ↓
+1-744-196-8840 (FRENS hotline)
```

### Vanity Number
```
1-744-FRENS-71
1-744-373-6771

Or j-invariant themed:
1-744-196-8840 (744 = constant, 196884 = Moonshine)
```

## Token-Gated Access

### Verify FRENS Holdings
```rust
use solana_client::rpc_client::RpcClient;
use spl_token::state::Account;

async fn verify_frens_holder(wallet: &str) -> Result<bool, Error> {
    let rpc = RpcClient::new("https://api.mainnet-beta.solana.com");
    
    // Get token account
    let token_account = get_associated_token_address(
        &wallet.parse()?,
        &"E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22".parse()?
    );
    
    // Check balance
    let account = rpc.get_account(&token_account)?;
    let token_data = Account::unpack(&account.data)?;
    
    Ok(token_data.amount > 0)
}
```

### BBS Access Control
```javascript
// Cloudflare Worker
async function handleFrensAccess(request, env) {
  const wallet = request.headers.get('X-Solana-Wallet');
  const signature = request.headers.get('X-Solana-Signature');
  
  // Verify wallet signature
  if (!verifySignature(wallet, signature)) {
    return new Response('Invalid signature', { status: 401 });
  }
  
  // Check FRENS balance
  const balance = await checkFrensBalance(wallet);
  
  if (balance === 0) {
    return new Response('No FRENS tokens', { status: 403 });
  }
  
  // Grant access to FRENS-only shard
  return dialNumber('744-196-8840');
}
```

## FRENS Shard

### Dedicated Shard for Token Holders
```
Shard 71: Public (Moonshine)
Shard 72: FRENS-only (token-gated)

Access:
1. Hold FRENS tokens
2. Sign message with wallet
3. Dial 1-744-196-8840
4. Connect to FRENS shard
```

### FRENS BBS Features
```
╔═══════════════════════════════════════════════════════════════╗
║                    FRENS-ONLY BBS                             ║
║                  Token-Gated Access                           ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Your FRENS Balance: 1,000,000                               ║
║  Wallet: 7xKX...Qv22                                         ║
║                                                               ║
║  [M] FRENS Message Board                                     ║
║  [T] Token Swap (DEX)                                        ║
║  [G] Governance (DAO)                                        ║
║  [A] Airdrop Claims                                          ║
║  [S] Staking                                                 ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

## Phone Number Registration

### Twilio Integration
```javascript
// Register FRENS hotline
const twilio = require('twilio');
const client = twilio(accountSid, authToken);

async function registerFrensNumber() {
  const number = await client.incomingPhoneNumbers.create({
    phoneNumber: '+17441968840',
    voiceUrl: 'https://cicada71.bbs.workers.dev/voice/frens',
    smsUrl: 'https://cicada71.bbs.workers.dev/sms/frens',
  });
  
  console.log('FRENS hotline:', number.phoneNumber);
}
```

### Voice Response
```xml
<!-- TwiML for voice calls -->
<Response>
  <Say voice="alice">
    Welcome to the FRENS hotline.
    Please enter your Solana wallet address followed by pound.
  </Say>
  <Gather action="/verify-frens" numDigits="44">
    <Say>Enter wallet address now.</Say>
  </Gather>
</Response>
```

## SMS Commands

### Text-to-BBS
```
Text to: +1-744-196-8840

Commands:
  BALANCE - Check FRENS balance
  DIAL 744-196884-23 - Connect to shard
  GOSSIP - Get network status
  ONION - Get .onion address
  HELP - Show commands
```

### SMS Handler
```javascript
async function handleFrensSMS(request, env) {
  const body = await request.formData();
  const from = body.get('From');
  const message = body.get('Body').toUpperCase();
  
  let response = '';
  
  if (message === 'BALANCE') {
    const balance = await getFrensBalance(from);
    response = `Your FRENS balance: ${balance}`;
  } else if (message.startsWith('DIAL ')) {
    const number = message.slice(5);
    response = `Dialing ${number}...\nConnect at: https://cicada71.bbs.workers.dev/dial/${number}`;
  } else if (message === 'ONION') {
    response = `FRENS onion: cicada71frens...onion`;
  }
  
  return new Response(`<?xml version="1.0" encoding="UTF-8"?>
    <Response>
      <Message>${response}</Message>
    </Response>`, {
    headers: { 'Content-Type': 'text/xml' },
  });
}
```

## Token Integration

### FRENS Token Metadata
```json
{
  "name": "FRENS",
  "symbol": "FRENS",
  "decimals": 9,
  "address": "E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22",
  "phone": "+1-744-196-8840",
  "bbs": "https://cicada71.bbs.workers.dev/dial/744-196-8840",
  "onion": "cicada71frens...onion",
  "shard": 72
}
```

### On-Chain Phone Number
```rust
// Store phone number in token metadata
use mpl_token_metadata::state::Metadata;

let metadata = Metadata {
    name: "FRENS".to_string(),
    symbol: "FRENS".to_string(),
    uri: "https://cicada71.bbs.workers.dev/frens-metadata.json".to_string(),
    // Custom field
    phone_number: Some("+1-744-196-8840".to_string()),
    ..Default::default()
};
```

## DAO Integration

### FRENS DAO Voting via Phone
```
Call: +1-744-196-8840
Press 1: Vote YES on proposal
Press 2: Vote NO on proposal
Press 3: Abstain
Press 9: Check voting power
```

### Voice Voting
```javascript
async function handleVoiceVote(request, env) {
  const digit = request.formData().get('Digits');
  const wallet = await getWalletFromPhone(request.formData().get('From'));
  
  if (digit === '1') {
    await castVote(wallet, 'yes');
    return twiml('Vote YES recorded. Thank you.');
  } else if (digit === '2') {
    await castVote(wallet, 'no');
    return twiml('Vote NO recorded. Thank you.');
  }
}
```

## FRENS Rewards

### Call-to-Earn
```
Every call to FRENS hotline:
  - Verify token holdings
  - Award 10 FRENS per minute
  - Bonus for completing challenges
  - Airdrop for referrals
```

### Referral System
```
Share your referral code: FRENS-7441968840
Friend calls and mentions code
You both get 100 FRENS bonus
```

## URL Format

```
https://cicada71.bbs.workers.dev/frens
  ↓
Redirects to: /dial/744-196-8840
  ↓
Token-gated access check
  ↓
FRENS-only BBS shard
```

## Integration Example

```rust
use solana_sdk::signature::Keypair;

async fn connect_frens_bbs(keypair: &Keypair) -> Result<()> {
    // Sign message
    let message = b"FRENS BBS Access";
    let signature = keypair.sign_message(message);
    
    // Connect with auth
    let client = reqwest::Client::new();
    let response = client
        .get("https://cicada71.bbs.workers.dev/frens")
        .header("X-Solana-Wallet", keypair.pubkey().to_string())
        .header("X-Solana-Signature", bs58::encode(&signature).into_string())
        .send()
        .await?;
    
    // WebSocket connection
    let ws = connect_websocket(&response.text().await?).await?;
    
    Ok(())
}
```

## Marketing

```
🤝 FRENS Token Hotline: 1-744-196-8840

Hold FRENS tokens?
Call now for exclusive access to:
  ✅ Token-gated BBS
  ✅ DAO voting via phone
  ✅ Call-to-earn rewards
  ✅ FRENS-only features

Dial the j-invariant. Meet your FRENS. 📞
```

## References

- Solana SPL Token: https://spl.solana.com/token
- Twilio Voice: https://www.twilio.com/voice
- Token-gated access: Web3 authentication
- Solscan: https://solscan.io/
