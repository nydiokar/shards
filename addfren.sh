#!/bin/bash
# addfren.sh - Schedule zkTLS proof generation for a FRENS token

set -e

if [ $# -lt 1 ]; then
    echo "Usage: $0 <solscan_token_url> [schedule]"
    echo ""
    echo "Examples:"
    echo "  $0 https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22"
    echo "  $0 https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22 hourly"
    echo "  $0 https://solscan.io/token/E6QQQ1xECshESosESjgtGvnLaHXJSkDcHPV6pd2RQv22 daily"
    exit 1
fi

URL="$1"
SCHEDULE="${2:-once}"
TOKEN=$(echo "$URL" | rev | cut -d'/' -f1 | rev)

echo "🤝 Adding FREN: $TOKEN"
echo "📅 Schedule: $SCHEDULE"
echo ""

# Create job script
JOB_SCRIPT="/tmp/fren_${TOKEN}.sh"
cat > "$JOB_SCRIPT" <<EOF
#!/bin/bash
cd $(pwd)/shard0/zktls
nix build
perf record -o frens_${TOKEN}.perf -- ./result/bin/frens_phone $URL
perf report -i frens_${TOKEN}.perf --stdio > frens_${TOKEN}_report.txt

# Save witness
cat > frens_${TOKEN}_witness.json <<WITNESS
{
  "timestamp": "\$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "token": "$TOKEN",
  "url": "$URL",
  "schedule": "$SCHEDULE",
  "proof_exists": \$(test -f frens_proof.tlsn && echo "true" || echo "false"),
  "phone_exists": \$(test -f frens_phone.txt && echo "true" || echo "false")
}
WITNESS

# Commit
git add frens_${TOKEN}_witness.json frens_${TOKEN}_report.txt
git commit -m "Add FREN $TOKEN witness \$(date -u +%Y-%m-%d)" || true
git push origin main || true
EOF

chmod +x "$JOB_SCRIPT"

# Schedule based on type
case "$SCHEDULE" in
    once)
        echo "▶️  Running once now..."
        "$JOB_SCRIPT"
        echo "✅ Complete!"
        ;;
    
    hourly)
        echo "⏰ Scheduling hourly via cron..."
        (crontab -l 2>/dev/null; echo "0 * * * * $JOB_SCRIPT") | crontab -
        echo "✅ Scheduled! Will run every hour."
        ;;
    
    daily)
        echo "⏰ Scheduling daily via cron..."
        (crontab -l 2>/dev/null; echo "0 0 * * * $JOB_SCRIPT") | crontab -
        echo "✅ Scheduled! Will run daily at midnight."
        ;;
    
    systemd)
        echo "⏰ Creating systemd timer..."
        
        # Create service
        sudo tee /etc/systemd/system/fren-${TOKEN}.service > /dev/null <<SERVICE
[Unit]
Description=zkTLS proof for FREN $TOKEN

[Service]
Type=oneshot
ExecStart=$JOB_SCRIPT
User=$USER
SERVICE

        # Create timer
        sudo tee /etc/systemd/system/fren-${TOKEN}.timer > /dev/null <<TIMER
[Unit]
Description=Hourly zkTLS proof for FREN $TOKEN

[Timer]
OnCalendar=hourly
Persistent=true

[Install]
WantedBy=timers.target
TIMER

        sudo systemctl daemon-reload
        sudo systemctl enable fren-${TOKEN}.timer
        sudo systemctl start fren-${TOKEN}.timer
        
        echo "✅ Systemd timer created and started!"
        ;;
    
    *)
        echo "❌ Unknown schedule: $SCHEDULE"
        echo "   Valid options: once, hourly, daily, systemd"
        exit 1
        ;;
esac

echo ""
echo "📞 FREN added!"
echo "   Token: $TOKEN"
echo "   URL: $URL"
echo "   Schedule: $SCHEDULE"
echo ""
echo "View status:"
echo "  crontab -l                              # Cron jobs"
echo "  systemctl status fren-${TOKEN}.timer    # Systemd timer"
echo "  git log --oneline | grep $TOKEN         # Witness commits"
