export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    
    // BBS Terminal
    if (url.pathname === '/bbs') {
      return handleBBS(request, env);
    }
    
    // State API
    if (url.pathname === '/state') {
      return handleState(request, env);
    }
    
    // Shard status
    if (url.pathname === '/shards') {
      return handleShards(env);
    }
    
    // Landing page
    return new Response(ANSI_WELCOME, {
      headers: { 'Content-Type': 'text/plain; charset=utf-8' },
    });
  }
};

async function handleBBS(request, env) {
  // Load state from 71 shards
  const shards = await loadShards(env);
  
  // Reconstruct with quorum (12 of 23)
  if (shards.length < 12) {
    return new Response('Insufficient shards for quorum', { status: 503 });
  }
  
  const state = reconstructState(shards);
  
  // Return WebSocket for terminal
  const pair = new WebSocketPair();
  const [client, server] = Object.values(pair);
  
  server.accept();
  
  // Handle BBS session
  handleSession(server, state, env);
  
  return new Response(null, {
    status: 101,
    webSocket: client,
  });
}

async function handleState(request, env) {
  const { shard_id } = await request.json();
  
  if (shard_id < 0 || shard_id > 70) {
    return new Response('Invalid shard_id', { status: 400 });
  }
  
  const closure = await env.KV.get(`shard-${shard_id}`);
  
  return new Response(JSON.stringify({
    shard_id,
    closure,
    encrypted: true,
    size: closure?.length || 0,
  }), {
    headers: { 'Content-Type': 'application/json' },
  });
}

async function handleShards(env) {
  const shards = [];
  
  for (let i = 0; i < 71; i++) {
    const closure = await env.KV.get(`shard-${i}`);
    shards.push({
      id: i,
      online: !!closure,
      size: closure?.length || 0,
    });
  }
  
  return new Response(JSON.stringify({
    total: 71,
    online: shards.filter(s => s.online).length,
    quorum: 12,
    shards,
  }), {
    headers: { 'Content-Type': 'application/json' },
  });
}

async function loadShards(env) {
  const shards = [];
  
  for (let i = 0; i < 71; i++) {
    const closure = await env.KV.get(`shard-${i}`);
    if (closure) {
      shards.push({ id: i, data: closure });
    }
  }
  
  return shards;
}

function reconstructState(shards) {
  // Shamir secret sharing reconstruction
  // Requires 12 of 23 nodes
  
  // Simplified: XOR all shards
  let state = new Uint8Array(1024);
  
  for (const shard of shards.slice(0, 12)) {
    const data = new Uint8Array(Buffer.from(shard.data, 'base64'));
    for (let i = 0; i < state.length && i < data.length; i++) {
      state[i] ^= data[i];
    }
  }
  
  return state;
}

function handleSession(ws, state, env) {
  // Send ANSI welcome
  ws.send(ANSI_WELCOME);
  
  ws.addEventListener('message', async (event) => {
    const input = event.data;
    
    // Handle BBS commands
    if (input === 'M') {
      ws.send(ANSI_MESSAGES);
    } else if (input === 'S') {
      const shards = await handleShards(env);
      ws.send(shards.body);
    } else if (input === 'Q') {
      ws.send('Goodbye!\n');
      ws.close();
    } else {
      ws.send('Invalid command\n');
    }
  });
}

const ANSI_WELCOME = `\x1b[2J\x1b[H
╔═══════════════════════════════════════════════════════════════╗
║                    CICADA-71 BBS v0.1                         ║
║                  Running on Linux 0.01 (1991)                 ║
║                    Compiled to WASM (2025)                    ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  [M] Message Boards (71 Forums)                              ║
║  [F] File Areas                                              ║
║  [C] Chat Rooms                                              ║
║  [G] Games (Door Games)                                      ║
║  [E] Email                                                   ║
║  [S] Shard Status                                            ║
║  [Q] Quit                                                    ║
║                                                               ║
║  Current Shard: 0                                            ║
║  Users Online: 23                                            ║
║  Messages: 196,883                                           ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝

Command: `;

const ANSI_MESSAGES = `\x1b[2J\x1b[H
╔═══════════════════════════════════════════════════════════════╗
║                      MESSAGE BOARDS                           ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Forum 0:  Level 0 - Bootstrap (357 bytes)                   ║
║  Forum 1:  Level 1 - j-Invariant                             ║
║  Forum 2:  Level 2 - Haystack Search                         ║
║  Forum 3:  Level 3 - Tikkun Restoration                      ║
║  Forum 4:  Level 4 - Name of God                             ║
║  Forum 5:  Level 5 - Dial j-Invariant                        ║
║  ...                                                          ║
║  Forum 70: Moonshine (Shard 70)                              ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝

Select forum (0-70) or [Q] to quit: `;
