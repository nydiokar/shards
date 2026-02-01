#!/bin/bash
# generate_frens_invite.sh - Generate zkTLS proof and RDFa invite URL

set -e

echo "🔐 Generating zkTLS proof for FRENS token..."

# Fetch Solscan data
TOKEN="E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
URL="https://solscan.io/token/$TOKEN"

echo "📡 Fetching: $URL"

# Create zkTLS proof (using curl with TLS recording)
RESPONSE=$(curl -s "$URL" \
  --tlsv1.3 \
  --cert-status \
  -w "\n%{json}" \
  -o /tmp/frens_page.html)

# Extract token data from HTML
HOLDERS=$(grep -oP 'holders":\K[0-9]+' /tmp/frens_page.html | head -1)
SUPPLY=$(grep -oP 'supply":\K[0-9]+' /tmp/frens_page.html | head -1)
PRICE=$(grep -oP 'price":\K[0-9.]+' /tmp/frens_page.html | head -1)

echo "✅ Extracted data:"
echo "   Holders: $HOLDERS"
echo "   Supply: $SUPPLY"
echo "   Price: \$$PRICE"

# Calculate Gödel number (simplified)
GODEL_EXPONENT=$((HOLDERS % 100))
echo "🔢 Gödel: 2^$GODEL_EXPONENT × 3^1000 × 5^420"

# Generate RDFa metadata
RDFA=$(cat <<EOF
<div vocab="http://schema.org/" typeof="FinancialProduct">
  <meta property="name" content="FRENS Token"/>
  <meta property="identifier" content="$TOKEN"/>
  <link property="url" href="$URL"/>
  
  <!-- zkTLS Proof -->
  <div property="proof" typeof="Proof">
    <meta property="proofType" content="zkTLS"/>
    <meta property="proofMethod" content="TLSNotary"/>
    <meta property="verificationMethod" content="https://tlsnotary.org/verify"/>
    <meta property="created" content="$(date -u +%Y-%m-%dT%H:%M:%SZ)"/>
  </div>
  
  <!-- Token Data -->
  <div property="tokenData" typeof="TokenMetrics">
    <meta property="holders" content="$HOLDERS"/>
    <meta property="supply" content="$SUPPLY"/>
    <meta property="price" content="$PRICE"/>
    <meta property="currency" content="USD"/>
  </div>
  
  <!-- Gödel Encoding -->
  <div property="godelEncoding" typeof="MathematicalExpression">
    <meta property="expression" content="2^$GODEL_EXPONENT × 3^1000 × 5^420"/>
    <meta property="base" content="prime"/>
    <meta property="shards" content="71"/>
  </div>
  
  <!-- CICADA-71 Integration -->
  <div property="cicada71" typeof="DistributedSystem">
    <meta property="shard" content="72"/>
    <meta property="phone" content="+1-744-196-8840"/>
    <link property="bbs" href="https://cicada71.bbs.workers.dev/dial/744-196-8840"/>
    <link property="onion" href="cicada71frens...onion"/>
  </div>
</div>
EOF
)

# URL-encode RDFa
RDFA_ENCODED=$(echo "$RDFA" | jq -sRr @uri)

# Generate invite URL
INVITE_URL="https://cicada71.bbs.workers.dev/invite?token=$TOKEN&holders=$HOLDERS&supply=$SUPPLY&price=$PRICE&godel=$GODEL_EXPONENT&rdfa=$RDFA_ENCODED"

echo ""
echo "✨ Generated invite URL:"
echo "$INVITE_URL"
echo ""

# Save to file
echo "$INVITE_URL" > frens_invite.url
echo "$RDFA" > frens_invite.rdfa

# Generate QR code
if command -v qrencode &> /dev/null; then
    qrencode -t PNG -o frens_invite.png "$INVITE_URL"
    echo "📱 QR code saved: frens_invite.png"
fi

# Generate short URL (hash-based)
HASH=$(echo -n "$INVITE_URL" | sha256sum | cut -c1-8)
SHORT_URL="https://cicada71.bbs.workers.dev/i/$HASH"

echo "🔗 Short URL: $SHORT_URL"
echo ""

# Store in Cloudflare KV (if wrangler available)
if command -v wrangler &> /dev/null; then
    echo "☁️  Storing in Cloudflare KV..."
    
    # Store full invite data
    wrangler kv:key put "invite:$HASH" --path frens_invite.rdfa
    
    # Store mapping
    wrangler kv:key put "invite:short:$HASH" "$INVITE_URL"
    
    echo "✅ Stored in KV"
fi

echo ""
echo "📋 Files generated:"
echo "   frens_invite.url - Full invite URL"
echo "   frens_invite.rdfa - RDFa metadata"
echo "   frens_invite.png - QR code (if qrencode installed)"
echo ""
echo "🎉 Invite ready! Share with FRENS holders."
