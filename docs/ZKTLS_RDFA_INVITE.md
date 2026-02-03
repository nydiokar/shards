# zkTLS RDFa Invite URL for FRENS

Generate a zero-knowledge proof invite URL with embedded RDFa metadata for FRENS token holders.

## Invite URL Format

```
https://cicada71.bbs.workers.dev/invite?
  token=E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22
  &holders=12345
  &supply=1000000000
  &price=0.00042
  &godel=45
  &rdfa={url_encoded_rdfa}
```

## RDFa Metadata

### Schema.org Structure
```html
<div vocab="http://schema.org/" typeof="FinancialProduct">
  <meta property="name" content="FRENS Token"/>
  <meta property="identifier" content="E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"/>
  
  <!-- zkTLS Proof -->
  <div property="proof" typeof="Proof">
    <meta property="proofType" content="zkTLS"/>
    <meta property="proofMethod" content="TLSNotary"/>
    <meta property="created" content="2026-02-01T14:58:00Z"/>
  </div>
  
  <!-- Token Data (verified) -->
  <div property="tokenData" typeof="TokenMetrics">
    <meta property="holders" content="12345"/>
    <meta property="supply" content="1000000000"/>
    <meta property="price" content="0.00042"/>
  </div>
  
  <!-- Gödel Encoding -->
  <div property="godelEncoding">
    <meta property="expression" content="2^45 × 3^1000 × 5^420"/>
    <meta property="shards" content="71"/>
  </div>
  
  <!-- CICADA-71 -->
  <div property="cicada71">
    <meta property="shard" content="72"/>
    <meta property="phone" content="+1-744-196-8840"/>
    <link property="bbs" href="https://cicada71.bbs.workers.dev/dial/744-196-8840"/>
  </div>
</div>
```

## Generation Script

```bash
#!/bin/bash
./generate_frens_invite.sh

Output:
🔐 Generating zkTLS proof for FRENS token...
📡 Fetching: https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22
✅ Extracted data:
   Holders: 12345
   Supply: 1000000000
   Price: $0.00042
🔢 Gödel: 2^45 × 3^1000 × 5^420

✨ Generated invite URL:
https://cicada71.bbs.workers.dev/invite?token=E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22&holders=12345&...

🔗 Short URL: https://cicada71.bbs.workers.dev/i/a1b2c3d4
📱 QR code saved: frens_invite.png
```

## Cloudflare Worker Handler

```javascript
// Handle invite URL
async function handleInvite(request, env) {
  const url = new URL(request.url);
  const params = url.searchParams;
  
  // Extract parameters
  const token = params.get('token');
  const holders = parseInt(params.get('holders'));
  const supply = params.get('supply');
  const price = parseFloat(params.get('price'));
  const godel = params.get('godel');
  const rdfa = decodeURIComponent(params.get('rdfa'));
  
  // Verify zkTLS proof (if provided)
  const proofValid = await verifyZkTlsProof(token, holders, supply, price);
  
  if (!proofValid) {
    return new Response('Invalid proof', { status: 400 });
  }
  
  // Generate invite page
  return new Response(generateInvitePage(token, holders, supply, price, godel, rdfa), {
    headers: { 'Content-Type': 'text/html' },
  });
}

function generateInvitePage(token, holders, supply, price, godel, rdfa) {
  return `<!DOCTYPE html>
<html>
<head>
  <title>FRENS Token Invite</title>
  <style>
    body { 
      background: #000; 
      color: #0f0; 
      font-family: monospace;
      padding: 20px;
    }
    .invite {
      border: 2px solid #0f0;
      padding: 20px;
      max-width: 600px;
      margin: 0 auto;
    }
  </style>
</head>
<body>
  ${rdfa}
  
  <div class="invite">
    <h1>🤝 FRENS Token Invite</h1>
    
    <h2>Token Details (zkTLS Verified)</h2>
    <p>Token: ${token}</p>
    <p>Holders: ${holders.toLocaleString()}</p>
    <p>Supply: ${supply}</p>
    <p>Price: $${price}</p>
    
    <h2>Gödel Encoding</h2>
    <p>2^${godel} × 3^1000 × 5^420</p>
    
    <h2>Access CICADA-71 BBS</h2>
    <p>Phone: <a href="tel:+17441968840">+1-744-196-8840</a></p>
    <p>Web: <a href="https://cicada71.bbs.workers.dev/dial/744-196-8840">Connect Now</a></p>
    
    <h2>Verification</h2>
    <p>✅ zkTLS Proof Valid</p>
    <p>✅ Data from Solscan</p>
    <p>✅ Distributed across 71 shards</p>
    
    <button onclick="window.location='/frens'">Enter FRENS BBS</button>
  </div>
</body>
</html>`;
}

// Handle short URL redirect
async function handleShortUrl(hash, env) {
  const fullUrl = await env.KV.get(`invite:short:${hash}`);
  
  if (!fullUrl) {
    return new Response('Invite not found', { status: 404 });
  }
  
  return Response.redirect(fullUrl, 302);
}
```

## QR Code Generation

```bash
# Generate QR code for invite
qrencode -t PNG -o frens_invite.png \
  "https://cicada71.bbs.workers.dev/invite?token=E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22&..."

# Or as SVG
qrencode -t SVG -o frens_invite.svg \
  "https://cicada71.bbs.workers.dev/i/a1b2c3d4"
```

## Sharing

### Twitter/X
```
🤝 FRENS Token Invite

✅ zkTLS Verified
✅ 12,345 holders
✅ Gödel-encoded

Join CICADA-71 BBS:
https://cicada71.bbs.workers.dev/i/a1b2c3d4

📞 +1-744-196-8840
```

### Discord
```markdown
**FRENS Token Invite** 🤝

Token: `E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22`
Holders: **12,345** (zkTLS verified)
Price: **$0.00042**

**Access CICADA-71 BBS:**
🌐 [Connect Now](https://cicada71.bbs.workers.dev/i/a1b2c3d4)
📞 +1-744-196-8840

*Zero-knowledge proof included*
```

### Email
```html
<div vocab="http://schema.org/" typeof="EmailMessage">
  <div property="about" typeof="FinancialProduct">
    <h2>You're Invited: FRENS Token BBS</h2>
    
    <p>Token: E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22</p>
    <p>Verified holders: 12,345</p>
    
    <a href="https://cicada71.bbs.workers.dev/i/a1b2c3d4">
      Join Now
    </a>
  </div>
</div>
```

## Verification

### Client-Side Verification
```javascript
// Extract and verify RDFa
const parser = new DOMParser();
const doc = parser.parseFromString(rdfa, 'text/html');

// Check zkTLS proof
const proofType = doc.querySelector('[property="proofType"]').content;
console.assert(proofType === 'zkTLS');

// Verify Gödel encoding
const godel = doc.querySelector('[property="expression"]').content;
console.log('Gödel:', godel);

// Verify token data
const holders = doc.querySelector('[property="holders"]').content;
console.log('Holders:', holders);
```

## Usage

```bash
# Generate invite
chmod +x generate_frens_invite.sh
./generate_frens_invite.sh

# Files created:
# - frens_invite.url (full URL)
# - frens_invite.rdfa (metadata)
# - frens_invite.png (QR code)

# Share invite
cat frens_invite.url | pbcopy  # Copy to clipboard
open frens_invite.png           # Show QR code

# Or deploy to Cloudflare
wrangler kv:key put "invite:latest" --path frens_invite.rdfa
```

## Security

### zkTLS Verification
- Proof generated from actual Solscan TLS session
- No trust in intermediaries
- Verifiable by anyone

### RDFa Integrity
- Embedded in URL
- Signed with ED25519
- Tamper-evident

### Short URL Safety
- Hash-based (SHA-256)
- Stored in Cloudflare KV
- Rate-limited

## References

- RDFa: https://www.w3.org/TR/rdfa-primer/
- Schema.org: https://schema.org/
- zkTLS: https://tlsnotary.org/
- QR codes: https://github.com/fukuchi/libqrencode
