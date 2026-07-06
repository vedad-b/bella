"use strict";

const http = require("http");
const path = require("path");
const fs = require("fs");
const WebSocket = require("./node_modules/ws");

const PORT = process.env.PORT || 3000;

// ============================================================
// ENGINE
// ============================================================
const SUITS = ["hearts", "bells", "acorns", "leaves"];
const RANKS = ["7", "8", "9", "10", "J", "Q", "K", "A"];
const NONTRUMP_ORDER = ["7", "8", "9", "J", "Q", "K", "10", "A"];
const TRUMP_ORDER = ["7", "8", "Q", "K", "10", "A", "9", "J"];
const NONTRUMP_POINTS = { 7: 0, 8: 0, 9: 0, J: 2, Q: 3, K: 4, 10: 10, A: 11 };
const TRUMP_POINTS = { 7: 0, 8: 0, Q: 3, K: 4, 10: 10, A: 11, 9: 14, J: 20 };
const BASE_POT = 162;
const CAPOT_BONUS = 90;
const WINNING_SCORE = 1000;
const NATURAL_ORDER = ["7", "8", "9", "10", "J", "Q", "K", "A"];

function buildDeck() {
  const deck = [];
  for (const suit of SUITS) for (const rank of RANKS) deck.push({ id: suit + "_" + rank, suit, rank });
  return deck;
}
function shuffle(deck) {
  const arr = deck.slice();
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    const tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
  }
  return arr;
}
function cardPoints(card, trumpSuit) {
  if (card.suit === trumpSuit) return TRUMP_POINTS[card.rank];
  return NONTRUMP_POINTS[card.rank];
}
function rankIndex(card, trumpSuit) {
  const order = card.suit === trumpSuit ? TRUMP_ORDER : NONTRUMP_ORDER;
  return order.indexOf(card.rank);
}
function compareSameSuit(a, b, trumpSuit) { return rankIndex(a, trumpSuit) - rankIndex(b, trumpSuit); }

function dealInitial(deck) {
  const hands = [[], [], [], []];
  let idx = 0;
  for (let p = 0; p < 4; p++) { hands[p] = deck.slice(idx, idx + 6); idx += 6; }
  const kitty = [deck.slice(idx,idx+2), deck.slice(idx+2,idx+4), deck.slice(idx+4,idx+6), deck.slice(idx+6,idx+8)];
  return { hands, kitty };
}
function nextSeat(seat) { return (seat + 1) % 4; }
function teamOf(seat) { return seat % 2; }

function currentWinningCard(trick, trumpSuit) {
  const ledSuit = trick[0].card.suit;
  const trumpsPlayed = trick.filter(t => t.card.suit === trumpSuit);
  const pool = trumpsPlayed.length > 0 ? trumpsPlayed : trick.filter(t => t.card.suit === ledSuit);
  let best = pool[0];
  for (const entry of pool.slice(1)) if (compareSameSuit(entry.card, best.card, trumpSuit) > 0) best = entry;
  return best;
}

function legalPlays(hand, trick, trumpSuit) {
  if (trick.length === 0) return hand.slice();
  const ledSuit = trick[0].card.suit;
  const sameSuitCards = hand.filter(c => c.suit === ledSuit);
  if (sameSuitCards.length > 0) {
    const trumpsInTrick = trick.filter(t => t.card.suit === trumpSuit);
    const alreadyTrumped = ledSuit !== trumpSuit && trumpsInTrick.length > 0;
    if (alreadyTrumped) return sameSuitCards;
    const best = currentWinningCard(trick, trumpSuit);
    const canBeat = sameSuitCards.some(c => compareSameSuit(c, best.card, trumpSuit) > 0);
    if (canBeat) return sameSuitCards.filter(c => compareSameSuit(c, best.card, trumpSuit) > 0);
    return sameSuitCards;
  }
  const trumpCards = hand.filter(c => c.suit === trumpSuit);
  if (trumpCards.length > 0) {
    const trumpsInTrick = trick.filter(t => t.card.suit === trumpSuit);
    if (trumpsInTrick.length === 0) return trumpCards;
    const best = currentWinningCard(trick, trumpSuit);
    const canBeat = trumpCards.some(c => compareSameSuit(c, best.card, trumpSuit) > 0);
    if (canBeat) return trumpCards.filter(c => compareSameSuit(c, best.card, trumpSuit) > 0);
    return trumpCards;
  }
  return hand.slice();
}

function resolveTrick(trick, trumpSuit) {
  const winner = currentWinningCard(trick, trumpSuit);
  const points = trick.reduce((sum, t) => sum + cardPoints(t.card, trumpSuit), 0);
  return { winnerSeat: winner.seat, points };
}

function detectMelds(hand, trumpSuit) {
  const melds = [];
  for (const suit of SUITS) {
    const suitCards = hand.filter(c => c.suit === suit);
    const naturalIdx = suitCards.map(c => ({ card: c, idx: NATURAL_ORDER.indexOf(c.rank) })).sort((a,b) => a.idx - b.idx);
    let i = 0;
    while (i < naturalIdx.length) {
      let j = i;
      while (j+1 < naturalIdx.length && naturalIdx[j+1].idx === naturalIdx[j].idx+1) j++;
      if (j-i+1 >= 3) melds.push(...meldsFromRun(naturalIdx.slice(i,j+1).map(x=>x.card), suit));
      i = j+1;
    }
  }
  for (const rank of RANKS) {
    const c4 = hand.filter(c => c.rank === rank);
    if (c4.length === 4) {
      let value = 100;
      if (rank === "9") value = 150;
      if (rank === "J") value = 200;
      melds.push({ type: "four-of-a-kind", suit: null, rank, cards: c4, value, topRank: rank });
    }
  }
  const trumpK = hand.find(c => c.suit === trumpSuit && c.rank === "K");
  const trumpQ = hand.find(c => c.suit === trumpSuit && c.rank === "Q");
  const trumpA = hand.find(c => c.suit === trumpSuit && c.rank === "A");
  if (trumpK && trumpQ) {
    melds.push({ type: "bella", suit: trumpSuit, cards: trumpA ? [trumpQ,trumpK,trumpA] : [trumpQ,trumpK], value: 20, topRank: "K", hidden: true });
  }
  return melds;
}
function meldsFromRun(runCards, suit) {
  const len = runCards.length;
  if (len >= 5) return [meldObj("run5plus", suit, runCards, 100)];
  if (len === 4) return [meldObj("quart", suit, runCards, 50)];
  if (len === 3) return [meldObj("tierce", suit, runCards, 20)];
  return [];
}
function meldObj(type, suit, cards, value) {
  return { type, suit, cards, value, topRank: cards[cards.length-1].rank };
}
function compareMelds(a, b) {
  if (a.value !== b.value) return a.value - b.value;
  return NATURAL_ORDER.indexOf(a.topRank) - NATURAL_ORDER.indexOf(b.topRank);
}
function resolveMelds(meldsBySeat, callerSeat) {
  const visible = meldsBySeat.map(list => list.filter(m => !m.hidden));
  const hidden = meldsBySeat.map(list => list.filter(m => m.hidden));
  const bestPerSeat = visible.map(list => list.length === 0 ? null : list.reduce((b,m) => compareMelds(m,b)>0?m:b));
  const teamBest = [null, null];
  for (let t = 0; t < 2; t++) {
    for (const seat of (t===0 ? [0,2] : [1,3])) {
      const m = bestPerSeat[seat];
      if (!m) continue;
      if (!teamBest[t] || compareMelds(m, teamBest[t].meld) > 0) teamBest[t] = { meld: m, seat };
    }
  }
  let winningTeam = null;
  if (teamBest[0] && !teamBest[1]) winningTeam = 0;
  else if (teamBest[1] && !teamBest[0]) winningTeam = 1;
  else if (teamBest[0] && teamBest[1]) {
    const cmp = compareMelds(teamBest[0].meld, teamBest[1].meld);
    if (cmp > 0) winningTeam = 0;
    else if (cmp < 0) winningTeam = 1;
    else winningTeam = teamOf(callerSeat);
  }
  let totalAwarded = 0;
  const awarded = [[],[],[],[]];
  if (winningTeam !== null) {
    for (const seat of (winningTeam===0 ? [0,2] : [1,3])) {
      for (const m of visible[seat]) { totalAwarded += m.value; awarded[seat].push(m); }
    }
  }
  return { winningTeam, totalAwarded, awardedMeldsBySeat: awarded, hiddenMeldsBySeat: hidden };
}
function scoreHand({ trickPointsByTeam, capotTeam, callerTeam, meldResult }) {
  const bellaByTeam = [0,0];
  meldResult.hiddenMeldsBySeat.forEach((list, seat) => { for (const m of list) bellaByTeam[teamOf(seat)] += m.value; });
  const meldByTeam = [0,0];
  if (meldResult.winningTeam !== null) meldByTeam[meldResult.winningTeam] = meldResult.totalAwarded;
  meldByTeam[0] += bellaByTeam[0];
  meldByTeam[1] += bellaByTeam[1];
  const pot = BASE_POT + meldByTeam[0] + meldByTeam[1];
  if (capotTeam !== null && capotTeam !== undefined) {
    const scores = [0,0];
    scores[capotTeam] = pot + CAPOT_BONUS;
    scores[capotTeam===0?1:0] = 0;
    return { scores, pot, set: false, capot: true };
  }
  const other = callerTeam === 0 ? 1 : 0;
  const callerEarned = trickPointsByTeam[callerTeam] + meldByTeam[callerTeam];
  if (callerEarned > pot / 2) {
    const scores = [0,0];
    scores[callerTeam] = callerEarned;
    scores[other] = trickPointsByTeam[other] + meldByTeam[other];
    return { scores, pot, set: false, capot: false };
  } else {
    const scores = [0,0];
    scores[callerTeam] = 0;
    scores[other] = pot;
    return { scores, pot, set: true, capot: false };
  }
}

function checkEightCardSuit(hands) {
  for (let seat = 0; seat < 4; seat++) {
    for (const suit of SUITS) {
      const count = hands[seat].filter(c => c.suit === suit).length;
      if (count === 8) return { seat, suit };
    }
  }
  return null;
}

// ============================================================
// ROOM MANAGEMENT
// ============================================================
const rooms = new Map();

function generateRoomCode() {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let code;
  do { code = Array.from({ length: 4 }, () => chars[Math.floor(Math.random() * chars.length)]).join(""); }
  while (rooms.has(code));
  return code;
}

function createRoom(code) {
  const room = {
    code,
    players: [null, null, null, null],
    pending: [],
    game: null,
    handNum: 0,
    teamScores: [0, 0],
    log: [],
  };
  rooms.set(code, room);
  return room;
}

function teamCount(room, team) {
  const seats = team === "A" ? [0, 2] : [1, 3];
  return seats.filter(s => room.players[s] !== null).length;
}

function findEmptySeatOnTeam(room, team) {
  const seats = team === "A" ? [0, 2] : [1, 3];
  return seats.find(s => room.players[s] === null);
}

function isReadyToStart(room) {
  return teamCount(room, "A") === 2 && teamCount(room, "B") === 2;
}

function totalPlayers(room) {
  return room.players.filter(p => p !== null).length;
}

// ============================================================
// GAME STATE HELPERS
// ============================================================
function startHand(room) {
  const deck = shuffle(buildDeck());
  const { hands, kitty } = dealInitial(deck);
  const dealer = room.handNum === 0 ? 0 : (room.game ? nextSeat(room.game.dealer) : 0);
  room.handNum++;
  room.game = {
    phase: "bidding",
    dealer,
    hands,
    kitty,
    revealedKitty: [false, false, false, false],
    biddingTurn: nextSeat(dealer),
    passes: [],
    trumpSuit: null,
    callerSeat: null,
    trick: [],
    trickLeader: nextSeat(dealer),
    tricksWon: [],
    meldsBySeat: [[], [], [], []],
    meldResult: null,
    lastHandSummary: null,
  };
  room.log = [];
  addLog(room, `Hand ${room.handNum}: ${playerName(room, dealer)} deals.`);
  addLog(room, `${playerName(room, nextSeat(dealer))} bids first.`);
}

function addLog(room, msg, notice) {
  room.log.push({ msg, notice: !!notice });
  if (room.log.length > 80) room.log.shift();
}

function playerName(room, seat) {
  const p = room.players[seat];
  return p ? p.name : `Seat ${seat + 1}`;
}

// ============================================================
// BROADCAST
// ============================================================
function buildStateForSeat(room, seat) {
  const g = room.game;
  const playersInfo = room.players.map(p => p ? { name: p.name, connected: p.connected } : null);

  if (!g) {
    return {
      phase: "lobby",
      teamScores: room.teamScores,
      players: playersInfo,
      teamA: [
        room.players[0] ? room.players[0].name : null,
        room.players[2] ? room.players[2].name : null,
      ],
      teamB: [
        room.players[1] ? room.players[1].name : null,
        room.players[3] ? room.players[3].name : null,
      ],
    };
  }

  const hands = g.hands.map((hand, s) => {
    if (s === seat) return hand;
    return hand.map(() => ({ id: "hidden", hidden: true }));
  });
  const kitty = g.kitty.map((k, s) => {
    if (g.revealedKitty[s] && s === seat) return k;
    return k.map(() => ({ id: "hidden", hidden: true }));
  });
  const meldsBySeat = g.meldsBySeat.map((list, s) =>
    list.map(m => (m.hidden && s !== seat) ? { ...m, cards: m.cards.map(() => ({ id: "hidden", hidden: true })) } : m)
  );

  return {
    phase: g.phase,
    dealer: g.dealer,
    handNum: room.handNum,
    teamScores: room.teamScores,
    players: playersInfo,
    teamA: [
      room.players[0] ? room.players[0].name : null,
      room.players[2] ? room.players[2].name : null,
    ],
    teamB: [
      room.players[1] ? room.players[1].name : null,
      room.players[3] ? room.players[3].name : null,
    ],
    mySeat: seat,
    hands,
    kitty,
    revealedKitty: g.revealedKitty,
    biddingTurn: g.biddingTurn,
    passes: g.passes,
    trumpSuit: g.trumpSuit,
    callerSeat: g.callerSeat,
    trick: g.trick,
    trickLeader: g.trickLeader,
    tricksWon: g.tricksWon.length,
    meldsBySeat,
    meldResult: g.meldResult,
    lastHandSummary: g.lastHandSummary,
    log: room.log,
  };
}

function lobbyStateForPending(room) {
  return {
    phase: "lobby",
    teamScores: room.teamScores,
    players: room.players.map(p => p ? { name: p.name, connected: p.connected } : null),
    teamA: [room.players[0]?.name||null, room.players[2]?.name||null],
    teamB: [room.players[1]?.name||null, room.players[3]?.name||null],
  };
}

function broadcastAll(room) {
  for (let seat = 0; seat < 4; seat++) {
    const p = room.players[seat];
    if (p && p.ws && p.ws.readyState === WebSocket.OPEN) {
      p.ws.send(JSON.stringify({ type: "state", state: buildStateForSeat(room, seat) }));
    }
  }
  const lobbyState = lobbyStateForPending(room);
  for (const pws of (room.pending || [])) {
    if (pws.readyState === WebSocket.OPEN) {
      pws.send(JSON.stringify({ type: "state", state: lobbyState }));
    }
  }
}

// ============================================================
// ACTION HANDLERS
// ============================================================
function handlePass(room, seat) {
  const g = room.game;
  if (g.phase !== "bidding" || g.biddingTurn !== seat) return "Not your turn to bid.";
  if (g.passes.length === 3) return "Dealer must call, cannot pass.";
  g.passes.push(seat);
  g.revealedKitty[seat] = true;
  g.biddingTurn = nextSeat(seat);
  addLog(room, `${playerName(room, seat)} passes.`);
  return null;
}

function handleCall(room, seat, suit) {
  const g = room.game;
  if (g.phase !== "bidding" || g.biddingTurn !== seat) return "Not your turn to bid.";
  if (!SUITS.includes(suit)) return "Invalid suit.";
  for (let i = 0; i < 4; i++) g.hands[i] = g.hands[i].concat(g.kitty[i]);
  g.revealedKitty = [true, true, true, true];
  g.trumpSuit = suit;
  g.callerSeat = seat;
  g.meldsBySeat = g.hands.map(h => detectMelds(h, suit));
  g.phase = "melds";
  g.trickLeader = nextSeat(g.dealer);
  addLog(room, `${playerName(room, seat)} calls ${suit} as trump!`, true);
  addLog(room, `All players reveal their final 2 cards.`);
  return null;
}

function handleConfirmMelds(room, seat) {
  const g = room.game;
  if (g.phase !== "melds") return "Not in meld phase.";
  if (!g.meldConfirms) g.meldConfirms = new Set();
  g.meldConfirms.add(seat);
  if (g.meldConfirms.size < 4) {
    addLog(room, `${playerName(room, seat)} confirms melds (${g.meldConfirms.size}/4).`);
    return null;
  }

  const eightCard = checkEightCardSuit(g.hands);
  if (eightCard) {
    const winnerTeam = teamOf(eightCard.seat);
    const winnerName = playerName(room, eightCard.seat);
    addLog(room, `${winnerName} holds all 8 ${eightCard.suit}! Instant game win!`, true);
    room.teamScores[winnerTeam] = WINNING_SCORE + 1;
    g.lastHandSummary = { pot: 0, scores: winnerTeam === 0 ? [WINNING_SCORE+1, room.teamScores[1]] : [room.teamScores[0], WINNING_SCORE+1], set: false, capot: false, instantWin: true, instantWinSuit: eightCard.suit, instantWinSeat: eightCard.seat };
    g.phase = "game-end";
    g.meldConfirms = null;
    return null;
  }

  const meldResult = resolveMelds(g.meldsBySeat, g.callerSeat);
  g.meldResult = meldResult;
  if (meldResult.winningTeam === null) {
    addLog(room, "No melds on the table.");
  } else {
    const label = meldResult.winningTeam === 0 ? "Team A" : "Team B";
    addLog(room, `${label} win the meld comparison: +${meldResult.totalAwarded} pts.`, true);
  }
  g.phase = "playing";
  g.trick = [];
  g.meldConfirms = null;
  return null;
}

function handlePlayCard(room, seat, cardId) {
  const g = room.game;
  if (g.phase !== "playing") return "Not in playing phase.";
  const expectedSeat = g.trick.length === 0 ? g.trickLeader : nextSeat(g.trick[g.trick.length - 1].seat);
  if (seat !== expectedSeat) return "Not your turn to play.";
  const hand = g.hands[seat];
  const card = hand.find(c => c.id === cardId);
  if (!card) return "Card not in your hand.";
  const legal = legalPlays(hand, g.trick, g.trumpSuit);
  if (!legal.some(c => c.id === cardId)) return "That play is not legal.";

  g.hands[seat] = hand.filter(c => c.id !== cardId);
  g.trick.push({ seat, card });
  addLog(room, `${playerName(room, seat)} plays ${card.rank} of ${card.suit}.`);

  if (g.trick.length < 4) return null;

  const result = resolveTrick(g.trick, g.trumpSuit);
  g.tricksWon.push({ seat: result.winnerSeat, points: result.points });
  addLog(room, `${playerName(room, result.winnerSeat)} wins the trick (+${result.points} pts).`, true);

  const handDone = g.hands.every(h => h.length === 0);
  if (handDone) {
    const finalTricks = g.tricksWon.slice();
    finalTricks[finalTricks.length-1] = { ...finalTricks[finalTricks.length-1], points: finalTricks[finalTricks.length-1].points + 10 };
    const trickPointsByTeam = [0,0];
    finalTricks.forEach(t => { trickPointsByTeam[teamOf(t.seat)] += t.points; });
    const teamsWithTricks = new Set(finalTricks.map(t => teamOf(t.seat)));
    const capotTeam = teamsWithTricks.size === 1 ? [...teamsWithTricks][0] : null;
    const callerTeam = teamOf(g.callerSeat);
    const scoreResult = scoreHand({ trickPointsByTeam, capotTeam, callerTeam, meldResult: g.meldResult });
    room.teamScores = [room.teamScores[0] + scoreResult.scores[0], room.teamScores[1] + scoreResult.scores[1]];
    g.tricksWon = finalTricks;
    g.lastHandSummary = { ...scoreResult, trickPointsByTeam, capotTeam };
    addLog(room, `Hand complete. Pot: ${scoreResult.pot} pts.`, true);
    if (scoreResult.capot) {
      addLog(room, 'CAPOT! Full sweep.', true);
    } else if (scoreResult.set) {
      const callerLabel = callerTeam === 0 ? 'Team A' : 'Team B';
      const otherLabel  = callerTeam === 0 ? 'Team B' : 'Team A';
      const callerPts = trickPointsByTeam[callerTeam];
      const otherPts  = trickPointsByTeam[callerTeam === 0 ? 1 : 0];
      addLog(room, `Card points — ${callerLabel}: ${callerPts}, ${otherLabel}: ${otherPts}.`);
      addLog(room, `${callerLabel} needed >${Math.floor(scoreResult.pot/2)} but only had ${callerPts} — SET. ${otherLabel} takes all ${scoreResult.pot} pts.`, true);
    }
    addLog(room, `Team A +${scoreResult.scores[0]}, Team B +${scoreResult.scores[1]}.`, true);
    const gameOver = room.teamScores[0] >= WINNING_SCORE || room.teamScores[1] >= WINNING_SCORE;
    g.phase = gameOver ? "game-end" : "hand-end";
    g.trick = [];
    return null;
  }

  g.trickLeader = result.winnerSeat;
  g.trick = [];
  return null;
}

function handleNextHand(room, seat) {
  const g = room.game;
  if (g.phase !== "hand-end") return "Hand is not over yet.";
  if (!g.nextHandVotes) g.nextHandVotes = new Set();
  g.nextHandVotes.add(seat);
  if (g.nextHandVotes.size < 4) {
    addLog(room, `${playerName(room, seat)} ready for next hand (${g.nextHandVotes.size}/4).`);
    return null;
  }
  startHand(room);
  return null;
}

function handleNewGame(room, seat) {
  const g = room.game;
  if (g.phase !== "game-end") return "Game is not over yet.";
  if (!g.newGameVotes) g.newGameVotes = new Set();
  g.newGameVotes.add(seat);
  if (g.newGameVotes.size < 4) {
    addLog(room, `${playerName(room, seat)} wants a new game (${g.newGameVotes.size}/4).`);
    return null;
  }
  room.teamScores = [0, 0];
  room.handNum = 0;
  startHand(room);
  return null;
}

// ============================================================
// HTTP SERVER
// ============================================================
const httpServer = http.createServer((req, res) => {
  if (req.url === "/" || req.url === "/index.html") {
    const file = path.join(__dirname, "client.html");
    fs.readFile(file, (err, data) => {
      if (err) { res.writeHead(404); res.end("Not found"); return; }
      res.writeHead(200, { "Content-Type": "text/html" });
      res.end(data);
    });
  } else {
    res.writeHead(404); res.end("Not found");
  }
});

// ============================================================
// WEBSOCKET SERVER
// ============================================================
const wss = new WebSocket.Server({ server: httpServer });

wss.on("connection", (ws) => {
  let playerRoom = null;
  let playerSeat = null;

  ws.on("message", (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }

    if (msg.type === "create") {
      const name = (msg.name || "Player").trim().slice(0, 20) || "Player";
      const code = generateRoomCode();
      const room = createRoom(code);
      ws._pendingRoom = room;
      room.pending.push(ws);
      ws.send(JSON.stringify({ type: "created", roomCode: code, name }));
      broadcastAll(room);
      return;
    }

    if (msg.type === "register_pending") {
      const code = (msg.code || "").toUpperCase().trim();
      let room = rooms.get(code);
      if (!room) { sendError(ws, "Room not found. Check the code."); return; }
      ws._pendingRoom = room;
      if (!room.pending.includes(ws)) room.pending.push(ws);
      ws.send(JSON.stringify({ type: "state", state: lobbyStateForPending(room) }));
      return;
    }

    if (msg.type === "join") {
      const name = (msg.name || "Player").trim().slice(0, 20) || "Player";
      const code = (msg.code || "").toUpperCase().trim();
      const team = msg.team;
      const sessionId = msg.sessionId;

      let room = rooms.get(code);
      if (!room) { sendError(ws, "Room not found. Check the code and try again."); return; }
      
      // Lock Check: Verify if this session ID is already seated somewhere in the room
      const alreadySeated = room.players.some(p => p && p.sessionId === sessionId);
      if (alreadySeated) {
        sendError(ws, "You have already joined a team in this room!");
        return;
      }

      if (!["A","B"].includes(team)) { sendError(ws, "Pick a team (A or B)."); return; }
      if (teamCount(room, team) >= 2) { sendError(ws, `Team ${team} is full (2 players max).`); return; }
      if (totalPlayers(room) >= 4) { sendError(ws, "Room is full."); return; }

      const seat = findEmptySeatOnTeam(room, team);
      // Save sessionId alongside connection tracking
      room.players[seat] = { ws, name, sessionId, connected: true };
      playerRoom = room;
      playerSeat = seat;
      room.pending = (room.pending || []).filter(p => p !== ws);

      ws.send(JSON.stringify({ type: "joined", roomCode: code, seat, name, team }));
      addLog(room, `${name} joined Team ${team}.`);

      if (isReadyToStart(room)) {
        addLog(room, "Both teams ready. Starting first hand...", true);
        startHand(room);
      }
      broadcastAll(room);
      return;
    }

    if (!playerRoom) { sendError(ws, "Not in a room."); return; }

    const room = playerRoom;
    const seat = playerSeat;
    let err = null;

    if (msg.type === "pass") err = handlePass(room, seat);
    else if (msg.type === "call") err = handleCall(room, seat, msg.suit);
    else if (msg.type === "confirm_melds") err = handleConfirmMelds(room, seat);
    else if (msg.type === "play_card") err = handlePlayCard(room, seat, msg.cardId);
    else if (msg.type === "next_hand") err = handleNextHand(room, seat);
    else if (msg.type === "new_game") err = handleNewGame(room, seat);
    else { sendError(ws, "Unknown action."); return; }

    if (err) { sendError(ws, err); return; }
    broadcastAll(room);
  });

  ws.on("close", () => {
    if (!playerRoom && ws._pendingRoom) {
      ws._pendingRoom.pending = ws._pendingRoom.pending.filter(p => p !== ws);
      return;
    }
    if (!playerRoom) return;
    const room = playerRoom;
    room.pending = (room.pending || []).filter(p => p !== ws);
    if (room.players[playerSeat]) {
      room.players[playerSeat].connected = false;
      addLog(room, `${playerName(room, playerSeat)} disconnected.`);
      broadcastAll(room);
    }
    setTimeout(() => {
      if (room.players.every(p => p === null || !p.connected)) {
        rooms.delete(room.code);
        console.log(`Room ${room.code} cleaned up.`);
      }
    }, 5 * 60 * 1000);
  });

  ws.on("error", (err) => console.error("WS error:", err.message));
});

httpServer.listen(PORT, () => {
  console.log(`Bella server running on http://localhost:${PORT}`);
});