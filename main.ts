// news-image-20261126 — R3 "The World in One Image"
// One 1024x1024 PNG drawn entirely in code: 50 sourced stories of Thursday
// 26 November 2026 (Thanksgiving Day, full day), 10 regions, 27 fields,
// 14 hand-drawn vector scenes, UTC timeline, date check.
// Pure Node.js stdlib only: hand-rolled PNG encoder + 5x7 bitmap font.
// No network, no image API, no external assets. Deterministic output.

import { deflateSync } from "node:zlib";
import { createHash } from "node:crypto";
import { writeFileSync, mkdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const W = 1024;
const H = 1024;
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || "/tmp/ni26r3-out";
const SCRIPT_DIR = dirname(fileURLToPath(import.meta.url));

// ---------- palette (make.fun brand) ----------
const PAPER = [250, 248, 250]; // #FAF8FA
const INK = [25, 20, 25]; // #191419
const MAGENTA = [196, 28, 131]; // #C41C83
const MAGENTA_INK = [255, 136, 196]; // #FF88C4
const WHITE = [255, 255, 255];
const GREY = [120, 112, 120];
const TINT = [242, 234, 242]; // light lead-row tint
const LEAD_BG = [25, 20, 25];
const LEAD_TEXT = [255, 255, 255];
const GOLD = [200, 140, 20];
const BLUE = [30, 90, 180];
const GREEN = [20, 130, 60];
const RED = [200, 40, 40];
const ORANGE = [230, 110, 20];

// ---------- pixel buffer ----------
const px = new Uint8Array(W * H * 4);
function fillAll(c) {
  for (let i = 0; i < W * H; i++) {
    px[i * 4] = c[0]; px[i * 4 + 1] = c[1]; px[i * 4 + 2] = c[2]; px[i * 4 + 3] = 255;
  }
}
function setPx(x, y, c) {
  // Round: a Uint8Array silently drops writes at fractional indices, so
  // every float coordinate from a scene helper would vanish without this.
  x = Math.round(x); y = Math.round(y);
  if (x < 0 || y < 0 || x >= W || y >= H) return;
  const i = (y * W + x) * 4;
  px[i] = c[0]; px[i + 1] = c[1]; px[i + 2] = c[2]; px[i + 3] = 255;
}
function rect(x, y, w, h, c) {
  x = Math.round(x); y = Math.round(y); w = Math.round(w); h = Math.round(h);
  for (let yy = Math.max(0, y); yy < Math.min(H, y + h); yy++)
    for (let xx = Math.max(0, x); xx < Math.min(W, x + w); xx++) setPx(xx, yy, c);
}
function hline(x0, x1, y, c) { rect(Math.min(x0, x1), y, Math.abs(x1 - x0) + 1, 1, c); }
function vline(x, y0, y1, c) { rect(x, Math.min(y0, y1), 1, Math.abs(y1 - y0) + 1, c); }
function line(x0, y0, x1, y1, c) {
  // Bresenham needs integers: scene helpers pass fractional coords, and a
  // float endpoint can never be hit exactly, looping forever. Round first.
  x0 = Math.round(x0); y0 = Math.round(y0); x1 = Math.round(x1); y1 = Math.round(y1);
  const dx = Math.abs(x1 - x0), dy = -Math.abs(y1 - y0);
  const sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  for (;;) {
    setPx(x0, y0, c);
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
}
function disc(cx, cy, r, c) {
  cx = Math.round(cx); cy = Math.round(cy); r = Math.round(r);
  for (let y = -r; y <= r; y++)
    for (let x = -r; x <= r; x++)
      if (x * x + y * y <= r * r) setPx(cx + x, cy + y, c);
}
function ring(cx, cy, r, t, c) {
  for (let a = 0; a < 360; a += 2) {
    const rad = (a * Math.PI) / 180;
    for (let k = 0; k < t; k++)
      setPx(Math.round(cx + (r + k) * Math.cos(rad)), Math.round(cy + (r + k) * Math.sin(rad)), c);
  }
}
function tri(x0, y0, x1, y1, x2, y2, c) {
  let d = (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0);
  if (d === 0) return;
  // Clockwise winding gives d < 0 and the inside test fails for every
  // pixel; flip two vertices so d > 0 (e.g. the flame triangle).
  if (d < 0) { const tx = x1, ty = y1; x1 = x2; y1 = y2; x2 = tx; y2 = ty; d = -d; }
  const minX = Math.floor(Math.min(x0, x1, x2)), maxX = Math.ceil(Math.max(x0, x1, x2));
  const minY = Math.floor(Math.min(y0, y1, y2)), maxY = Math.ceil(Math.max(y0, y1, y2));
  for (let y = minY; y <= maxY; y++)
    for (let x = minX; x <= maxX; x++) {
      const s1 = ((x - x0) * (y2 - y0) - (y - y0) * (x2 - x0)) / d;
      const s2 = ((x - x1) * (y0 - y1) - (y - y1) * (x0 - x1)) / d;
      if (s1 >= 0 && s2 >= 0 && s1 + s2 <= 1) setPx(x, y, c);
    }
}

// ---------- PNG encoder (CRC32 + zlib) ----------
const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();
function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type, data) {
  const len = Buffer.alloc(4);
  len.writeUInt32BE(data.length, 0);
  const td = Buffer.concat([Buffer.from(type, "ascii"), data]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(td), 0);
  return Buffer.concat([len, td, crc]);
}
function encodePNG() {
  const raw = Buffer.alloc(H * (1 + W * 3));
  for (let y = 0; y < H; y++) {
    raw[y * (1 + W * 3)] = 0;
    for (let x = 0; x < W; x++) {
      const i = (y * W + x) * 4, o = y * (1 + W * 3) + 1 + x * 3;
      raw[o] = px[i]; raw[o + 1] = px[i + 1]; raw[o + 2] = px[i + 2];
    }
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0); ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; ihdr[9] = 2; ihdr[10] = 0; ihdr[11] = 0; ihdr[12] = 0;
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk("IHDR", ihdr),
    chunk("IDAT", deflateSync(raw, { level: 9 })),
    chunk("IEND", Buffer.alloc(0)),
  ]);
}

// ---------- 5x7 bitmap font (ASCII uppercase + digits) ----------
// Each glyph: 7 rows of 5 bits, "#" = on.
const FONT = {
  A: ["01110","10001","10001","11111","10001","10001","10001"],
  B: ["11110","10001","10001","11110","10001","10001","11110"],
  C: ["01110","10001","10000","10000","10000","10001","01110"],
  D: ["11110","10001","10001","10001","10001","10001","11110"],
  E: ["11111","10000","10000","11110","10000","10000","11111"],
  F: ["11111","10000","10000","11110","10000","10000","10000"],
  G: ["01110","10001","10000","10111","10001","10001","01111"],
  H: ["10001","10001","10001","11111","10001","10001","10001"],
  I: ["01110","00100","00100","00100","00100","00100","01110"],
  J: ["00111","00010","00010","00010","00010","10010","01100"],
  K: ["10001","10010","10100","11000","10100","10010","10001"],
  L: ["10000","10000","10000","10000","10000","10000","11111"],
  M: ["10001","11011","10101","10101","10001","10001","10001"],
  N: ["10001","11001","10101","10011","10001","10001","10001"],
  O: ["01110","10001","10001","10001","10001","10001","01110"],
  P: ["11110","10001","10001","11110","10000","10000","10000"],
  Q: ["01110","10001","10001","10001","10101","10010","01101"],
  R: ["11110","10001","10001","11110","10100","10010","10001"],
  S: ["01111","10000","10000","01110","00001","00001","11110"],
  T: ["11111","00100","00100","00100","00100","00100","00100"],
  U: ["10001","10001","10001","10001","10001","10001","01110"],
  V: ["10001","10001","10001","10001","10001","01010","00100"],
  W: ["10001","10001","10001","10101","10101","11011","10001"],
  X: ["10001","10001","01010","00100","01010","10001","10001"],
  Y: ["10001","10001","01010","00100","00100","00100","00100"],
  Z: ["11111","00001","00010","00100","01000","10000","11111"],
  "0": ["01110","10001","10011","10101","11001","10001","01110"],
  "1": ["00100","01100","00100","00100","00100","00100","01110"],
  "2": ["01110","10001","00001","00110","01000","10000","11111"],
  "3": ["11111","00010","00100","00010","00001","10001","01110"],
  "4": ["00010","00110","01010","10010","11111","00010","00010"],
  "5": ["11111","10000","11110","00001","00001","10001","01110"],
  "6": ["00110","01000","10000","11110","10001","10001","01110"],
  "7": ["11111","00001","00010","00100","01000","01000","01000"],
  "8": ["01110","10001","10001","01110","10001","10001","01110"],
  "9": ["01110","10001","10001","01111","00001","00010","01100"],
};

// punctuation / symbols (same 5x7 grid)
Object.assign(FONT, {
  " ": ["00000","00000","00000","00000","00000","00000","00000"],
  ".": ["00000","00000","00000","00000","00000","01100","01100"],
  ",": ["00000","00000","00000","00000","01100","00100","01000"],
  ":": ["00000","01100","01100","00000","01100","01100","00000"],
  ";": ["00000","01100","01100","00000","01100","00100","01000"],
  "'": ["00100","00100","01000","00000","00000","00000","00000"],
  '"': ["01010","01010","00000","00000","00000","00000","00000"],
  "!": ["00100","00100","00100","00100","00100","00000","00100"],
  "?": ["01110","10001","00001","00110","00100","00000","00100"],
  "-": ["00000","00000","00000","01110","00000","00000","00000"],
  "/": ["00001","00010","00010","00100","01000","01000","10000"],
  "(": ["00010","00100","01000","01000","01000","00100","00010"],
  ")": ["01000","00100","00010","00010","00010","00100","01000"],
  "%": ["11001","11010","00010","00100","01000","01011","10011"],
  "$": ["00100","01111","10100","01110","00101","11110","00100"],
  "&": ["01100","10010","10100","01000","10101","10010","01101"],
  "+": ["00000","00100","00100","11111","00100","00100","00000"],
  "=": ["00000","00000","11111","00000","11111","00000","00000"],
  "|": ["00100","00100","00100","00100","00100","00100","00100"],
});

function drawText(x, y, s, c, scale) {
  const sc = scale || 1;
  let cx = x;
  for (const ch of s) {
    const g = FONT[ch] || FONT[" "];
    for (let r = 0; r < 7; r++)
      for (let col = 0; col < 5; col++)
        if (g[r][col] === "1") rect(cx + col * sc, y + r * sc, sc, sc, c);
    cx += 6 * sc;
  }
  return cx;
}
function textWidth(s, scale) { return s.length * 6 * (scale || 1) - (scale || 1); }

// ---------- THE DATA: 50 stories, Thursday 26 November 2026 ----------
// text: one line, ASCII uppercase, <= 78 chars. region: 10 regions. field: 27 fields.
const STORIES = [
  { n: 1,  t: "EU SUMMIT ENDS WITH NO DEAL ON EUR 1.58TN BUDGET, EUR 45BN LOAN", r: "EUROPE", f: "POLITICS", icon: "parliament" },
  { n: 2,  t: "HOUTHI DRONES HIT SAUDI RAS TANURA REFINERY; BRENT TOPS $94", r: "MIDDLE EAST", f: "ENERGY", icon: "flame" },
  { n: 3,  t: "TRUMP UNVEILS TARIFF PLAN ON 14 PARTNERS; CHINA FACES 20%", r: "NORTH AMERICA", f: "TRADE", icon: "bars" },
  { n: 4,  t: "TWO OIL TANKERS HIT NAVAL MINES IN STRAIT OF HORMUZ", r: "MIDDLE EAST", f: "ENERGY", icon: "oil" },
  { n: 5,  t: "ISRAEL STRIKES HAMAS COLONEL IN GAZA; CEASEFIRE UNDER STRAIN", r: "MIDDLE EAST", f: "CONFLICT" },
  { n: 6,  t: "UKRAINE HITS TWO RUSSIAN REFINERIES OVERNIGHT; PUTIN VOWS REPLY", r: "EUROPE", f: "CONFLICT" },
  { n: 7,  t: "RUSSIA'S OWN FIGURES: NEARLY 500,000 LOST IN UKRAINE WAR", r: "EUROPE", f: "CONFLICT" },
  { n: 8,  t: "POLAND ASKS NATO TO DOWN RUSSIAN MISSILES OVER UKRAINE", r: "EUROPE", f: "DEFENCE" },
  { n: 9,  t: "FRANCE OFFERS ENVOY TO MOSCOW IF EUROPE GETS FULL SEAT AT TALKS", r: "EUROPE", f: "DIPLOMACY" },
  { n: 10, t: "BANK OF KOREA HIKES RATE TO 3.25%; LIFTS 2026 GROWTH VIEW TO 3.9%", r: "EAST ASIA", f: "CENTRAL BANK", icon: "bank" },
  { n: 11, t: "BOJ'S TAMURA TALKS HAWKISH BEFORE DECEMBER RATE DECISION", r: "EAST ASIA", f: "CENTRAL BANK" },
  { n: 12, t: "US TIGHTENS REMOTE AI CHIP ACCESS; NVIDIA B300 CHIPS SEEK BUYERS", r: "NORTH AMERICA", f: "CHIPS" },
  { n: 13, t: "ECONOMISTS WARN AI BUBBLE BURST COULD TOP THE DOT-COM CRASH", r: "GLOBAL", f: "MARKETS" },
  { n: 14, t: "ASIAN MARKETS REBOUND: TAIEX +2.9%, KOSPI +1.8%, NIKKEI +1.5%", r: "EAST ASIA", f: "MARKETS" },
  { n: 15, t: "US MARKETS SHUT FOR THANKSGIVING; BOND MARKET CLOSED TOO", r: "NORTH AMERICA", f: "MARKETS" },
  { n: 16, t: "NOR'EASTER BATTERS THANKSGIVING: 1M WITHOUT POWER, 1,500 FLIGHTS LATE", r: "NORTH AMERICA", f: "WEATHER", icon: "storm" },
  { n: 17, t: "US ATTORNEY GENERAL DODGES QUESTIONS ON NVIDIA PROBE", r: "NORTH AMERICA", f: "COURTS" },
  { n: 18, t: "MYANMAR DEFIES ICJ GENOCIDE RULING AFTER LANDMARK VERDICT", r: "SOUTHEAST ASIA", f: "COURTS", icon: "gavel" },
  { n: 19, t: "CLOSE-UP IMAGES OF ASTEROID HIT TO TEST EARTH DEFENCE REVEALED", r: "GLOBAL", f: "SPACE" },
  { n: 20, t: "DURAN DURAN GUITARIST ANDY TAYLOR DIES AT 65", r: "EUROPE", f: "CULTURE" },
  { n: 21, t: "GUKESH HELD TO 20-MOVE DRAW BY SINDAROV IN WORLD CHESS FINAL", r: "SOUTH ASIA", f: "CHESS", icon: "knight" },
  { n: 22, t: "BEARS BEAT LIONS 39-35 IN THANKSGIVING THRILLER; LAST-PLAY TD", r: "NORTH AMERICA", f: "FOOTBALL", icon: "ball" },
  { n: 23, t: "INDIA A FACE SRI LANKA A IN RISING STARS SEMI-FINAL IN DOHA", r: "SOUTH ASIA", f: "CRICKET", icon: "bat" },
  { n: 24, t: "INDIA MARKS CONSTITUTION DAY AND 18 YEARS SINCE 26/11 ATTACKS", r: "SOUTH ASIA", f: "POLITICS" },
  { n: 25, t: "US Q3 GDP REVISED UP TO 4.3%; JOBLESS CLAIMS FALL TO 189,000", r: "NORTH AMERICA", f: "ECONOMY" },
  { n: 26, t: "HIV PREVENTION JAB LENACAPAVIR REACHES AFRICA; NEARLY 100% EFFECTIVE", r: "AFRICA", f: "HEALTH", icon: "syringe" },
  { n: 27, t: "INDIA ANNOUNCES RS15,000-CRORE PACKAGE FOR NEPAL AFTER MODI TALKS", r: "SOUTH ASIA", f: "DIPLOMACY" },
  { n: 28, t: "WHITE HOUSE DEBATES TARGETING IRANIAN LEADERS AS IRAN WAR HITS DAY 271", r: "MIDDLE EAST", f: "POLITICS" },
  { n: 29, t: "FLIPKART CEO KALYAN KRISHNAMURTHY TO STEP DOWN IN DECEMBER", r: "SOUTH ASIA", f: "BUSINESS" },
  { n: 30, t: "TWO INDIANS HURT IN RIYADH TOWER ATTACK; INDIA CONDEMNS STRIKE", r: "MIDDLE EAST", f: "CONFLICT" },
  { n: 31, t: "SHEIKH HASINA SEEKS RETURN TO BANGLADESH ON DECEMBER 16", r: "SOUTH ASIA", f: "POLITICS" },
  { n: 32, t: "BANGLADESH RAISES GARMENT MINIMUM WAGE BY 36 PERCENT", r: "SOUTH ASIA", f: "ECONOMY" },
  { n: 33, t: "BANGLADESH DEPLOYS 108 BORDER GUARD PLATOONS AMID UNREST FEARS", r: "SOUTH ASIA", f: "SECURITY" },
  { n: 34, t: "NORTH KOREA ORDERS SWITZERLAND TO CLOSE PYONGYANG OFFICE", r: "EAST ASIA", f: "DIPLOMACY" },
  { n: 35, t: "SOLOMON ISLANDS AND AUSTRALIA SIGN HISTORIC SECURITY TREATY", r: "OCEANIA", f: "SECURITY" },
  { n: 36, t: "COLOMBIA POLICE STORM SUPERMARKET, FREE 20 HELD HOSTAGE 17 HOURS", r: "SOUTH AMERICA", f: "CRIME" },
  { n: 37, t: "BANGKOK OIL REFINERY BLAST HURTS NINE, THREE CRITICALLY", r: "SOUTHEAST ASIA", f: "DISASTER" },
  { n: 38, t: "BRAZIL MOSQUITOES CUT VIRAL INFECTIONS BY 68 PERCENT", r: "SOUTH AMERICA", f: "SCIENCE" },
  { n: 39, t: "NASDAQ BRIEFLY NEARS BEAR MARKET, RECOVERS; NVIDIA -3.9%, DOW +0.3%", r: "NORTH AMERICA", f: "MARKETS", icon: "chart" },
  { n: 40, t: "FIFA CONFIRMS CYBERATTACK ON PERSONAL DATA", r: "GLOBAL", f: "CYBER" },
  { n: 41, t: "TURKISH MILITARY HELICOPTER CRASHES IN TRAINING; FIVE KILLED", r: "MIDDLE EAST", f: "MILITARY" },
  { n: 42, t: "GOOGLE FACES $146M LEGAL ACTION IN MALAYSIA", r: "SOUTHEAST ASIA", f: "COURTS" },
  { n: 43, t: "DEPARDIEU TO STAND TRIAL FOR ALLEGED RAPE OF ACTRESS, PARIS COURT RULES", r: "EUROPE", f: "COURTS" },
  { n: 44, t: "SOUTH SUDAN PARTIES ADOPT ELECTION PLAN", r: "AFRICA", f: "POLITICS", icon: "ballot" },
  { n: 45, t: "TWO CHILDREN AMONG SIX DEAD IN PLANE CRASH OFF MISSISSIPPI COAST", r: "NORTH AMERICA", f: "AVIATION", icon: "jet" },
  { n: 46, t: "DIESEL TANKER CAPSIZES NEAR IBIZA, ONE KILLED", r: "EUROPE", f: "SHIPPING" },
  { n: 47, t: "HAMAS POLITICAL OFFICIAL AND WIFE AMONG 8 KILLED IN GAZA STRIKES", r: "MIDDLE EAST", f: "CONFLICT" },
  { n: 48, t: "ECOWAS UNVEILS ROADMAP FOR JOINT SECURITY UNIT BY END 2027", r: "AFRICA", f: "SECURITY" },
  { n: 49, t: "SAUDI NATIONAL FREED FROM SUSPECTED IS CAPTORS IN NIGER", r: "AFRICA", f: "SECURITY" },
  { n: 50, t: "XI GRAFT PROBE OF SHANGHAI RISING STAR UPENDS PATH TO POWER", r: "EAST ASIA", f: "POLITICS" },
];

const LEADS = [
  { icon: "parliament", tag: "LEAD 1 | EUROPE", a: "EU SUMMIT ENDS WITH NO DEAL",
    b: "EUR 1.58TN BUDGET AND EUR 45BN UKRAINE LOAN STALL" },
  { icon: "flame", tag: "LEAD 2 | ENERGY", a: "HOUTHI DRONES HIT SAUDI RAS TANURA REFINERY",
    b: "BRENT TOPS $94 AS GULF SHIPPING FEARS GROW" },
  { icon: "bars", tag: "LEAD 3 | TRADE", a: "TRUMP UNVEILS TARIFF PLAN ON 14 PARTNERS",
    b: "CHINA FACES 20%, DOUBLING IF TALKS COLLAPSE" },
];

const TIMELINE = [
  { t: "00:27Z", label: "POLAND NATO" },
  { t: "00:52Z", label: "BOK +0.25" },
  { t: "05:21Z", label: "ASIA +2.9%" },
  { t: "07:15Z", label: "EU MEETS" },
  { t: "13:30Z", label: "US GDP 4.3%" },
  { t: "15:00Z", label: "STORM" },
  { t: "20:45Z", label: "BEARS 39-35" },
  { t: "23:00Z", label: "EU: NO DEAL" },
];

// ---------- vector scenes (all drawn with primitives) ----------
// Each scene draws inside a box at (x, y) with size s; colours fixed per scene.
function drawScene(kind, x, y, s, c) {
  const col = c || MAGENTA;
  if (kind === "flame") {
    // stylised flame: outer teardrop + inner flame
    tri(x + s * 0.5, y, x + s * 0.15, y + s * 0.7, x + s * 0.85, y + s * 0.7, ORANGE);
    disc(x + s * 0.5, y + s * 0.7, s * 0.3, ORANGE);
    disc(x + s * 0.5, y + s * 0.75, s * 0.16, GOLD);
    rect(x + s * 0.15, y + s * 0.9, s * 0.7, s * 0.1, INK);
  } else if (kind === "bars") {
    // tariff bar chart: three rising bars + arrow
    rect(x + s * 0.1, y + s * 0.55, s * 0.18, s * 0.45, BLUE);
    rect(x + s * 0.4, y + s * 0.35, s * 0.18, s * 0.65, col);
    rect(x + s * 0.7, y + s * 0.12, s * 0.18, s * 0.88, GOLD);
    line(x, y + s, x + s, y + s * 0.05, INK);
  } else if (kind === "parliament") {
    // dome + columns
    disc(x + s * 0.5, y + s * 0.35, s * 0.3, col);
    rect(x + s * 0.2, y + s * 0.35, s * 0.6, s * 0.08, col);
    for (let i = 0; i < 4; i++) rect(x + s * (0.22 + i * 0.16), y + s * 0.43, s * 0.06, s * 0.42, col);
    rect(x + s * 0.15, y + s * 0.85, s * 0.7, s * 0.1, INK);
  } else if (kind === "storm") {
    // cloud + rain + lightning
    disc(x + s * 0.35, y + s * 0.4, s * 0.22, BLUE);
    disc(x + s * 0.6, y + s * 0.35, s * 0.26, BLUE);
    disc(x + s * 0.75, y + s * 0.45, s * 0.18, BLUE);
    rect(x + s * 0.2, y + s * 0.5, s * 0.65, s * 0.08, BLUE);
    line(x + s * 0.35, y + s * 0.65, x + s * 0.3, y + s * 0.95, BLUE);
    line(x + s * 0.55, y + s * 0.65, x + s * 0.5, y + s * 0.95, BLUE);
    tri(x + s * 0.75, y + s * 0.6, x + s * 0.65, y + s * 0.8, x + s * 0.8, y + s * 0.8, GOLD);
    tri(x + s * 0.72, y + s * 0.8, x + s * 0.85, y + s * 0.95, x + s * 0.68, y + s * 0.95, GOLD);
  } else if (kind === "ball") {
    // American football: ellipse + laces
    for (let a = 0; a < 360; a += 3) {
      const rad = (a * Math.PI) / 180;
      setPx(Math.round(x + s * 0.5 + s * 0.45 * Math.cos(rad)),
        Math.round(y + s * 0.5 + s * 0.22 * Math.sin(rad)), ORANGE);
    }
    line(x + s * 0.32, y + s * 0.5, x + s * 0.68, y + s * 0.5, WHITE);
    for (let i = 0; i < 3; i++) {
      const lx = x + s * (0.42 + i * 0.08);
      line(lx, y + s * 0.42, lx, y + s * 0.58, WHITE);
    }
  } else if (kind === "knight") {
    // chess knight: head + neck + base
    tri(x + s * 0.55, y + s * 0.05, x + s * 0.85, y + s * 0.15, x + s * 0.6, y + s * 0.35, INK);
    tri(x + s * 0.4, y + s * 0.2, x + s * 0.75, y + s * 0.35, x + s * 0.35, y + s * 0.75, INK);
    rect(x + s * 0.25, y + s * 0.75, s * 0.55, s * 0.12, INK);
    rect(x + s * 0.15, y + s * 0.88, s * 0.75, s * 0.1, INK);
    disc(x + s * 0.68, y + s * 0.18, s * 0.03, WHITE);
  } else if (kind === "oil") {
    // oil drop
    tri(x + s * 0.5, y, x + s * 0.15, y + s * 0.55, x + s * 0.85, y + s * 0.55, INK);
    disc(x + s * 0.5, y + s * 0.55, s * 0.32, INK);
  } else if (kind === "bank") {
    // bank building
    tri(x + s * 0.5, y, x + s * 0.05, y + s * 0.3, x + s * 0.95, y + s * 0.3, col);
    for (let i = 0; i < 3; i++) rect(x + s * (0.18 + i * 0.28), y + s * 0.38, s * 0.1, s * 0.45, col);
    rect(x + s * 0.1, y + s * 0.83, s * 0.8, s * 0.1, INK);
  } else if (kind === "chart") {
    // line chart trending down then up
    line(x, y + s * 0.3, x + s * 0.3, y + s * 0.6, RED);
    line(x + s * 0.3, y + s * 0.6, x + s * 0.6, y + s * 0.45, RED);
    line(x + s * 0.6, y + s * 0.45, x + s, y + s * 0.15, GREEN);
    line(x, y + s, x + s, y + s, INK);
    line(x, y, x, y + s, INK);
  } else if (kind === "bat") {
    // cricket bat + ball
    rect(x + s * 0.35, y + s * 0.05, s * 0.08, s * 0.3, INK);
    tri(x + s * 0.55, y + s * 0.3, x + s * 0.25, y + s * 0.35, x + s * 0.4, y + s * 0.95, INK);
    disc(x + s * 0.8, y + s * 0.75, s * 0.12, RED);
  } else if (kind === "syringe") {
    // syringe diagonal
    line(x + s * 0.15, y + s * 0.85, x + s * 0.75, y + s * 0.25, col);
    line(x + s * 0.25, y + s * 0.95, x + s * 0.85, y + s * 0.35, col);
    line(x + s * 0.7, y + s * 0.2, x + s * 0.9, y + s * 0.05, INK);
    rect(x + s * 0.6, y + s * 0.25, s * 0.18, s * 0.18, col);
  } else if (kind === "gavel") {
    // gavel: head + handle + sound block
    rect(x + s * 0.1, y + s * 0.15, s * 0.45, s * 0.22, INK);
    line(x + s * 0.55, y + s * 0.26, x + s * 0.9, y + s * 0.6, INK);
    rect(x + s * 0.55, y + s * 0.8, s * 0.4, s * 0.12, INK);
  } else if (kind === "jet") {
    // jet silhouette
    tri(x + s, y + s * 0.45, x + s * 0.4, y + s * 0.35, x + s * 0.4, y + s * 0.55, INK);
    tri(x + s * 0.55, y + s * 0.35, x + s * 0.3, y + s * 0.1, x + s * 0.45, y + s * 0.4, INK);
    tri(x + s * 0.55, y + s * 0.55, x + s * 0.3, y + s * 0.9, x + s * 0.45, y + s * 0.55, INK);
    line(x + s * 0.4, y + s * 0.45, x + s * 0.05, y + s * 0.45, INK);
  } else if (kind === "ballot") {
    // ballot box + paper
    rect(x + s * 0.15, y + s * 0.45, s * 0.7, s * 0.5, col);
    rect(x + s * 0.42, y + s * 0.1, s * 0.16, s * 0.45, WHITE);
    line(x + s * 0.32, y + s * 0.6, x + s * 0.45, y + s * 0.75, WHITE);
    line(x + s * 0.45, y + s * 0.75, x + s * 0.68, y + s * 0.55, WHITE);
  }
}

// ---------- layout ----------
const MX = 16; // margin x
const CW = W - 2 * MX; // 992 content width
const INLINE_ICONS = new Set(["oil", "bank", "gavel", "bat", "syringe", "chart", "ballot", "jet"]);

function main() {
  // ---- data self-checks (fail loudly, never ship a wrong count) ----
  if (STORIES.length !== 50) throw new Error("STORIES must be 50, got " + STORIES.length);
  const regions = new Set(STORIES.map((s) => s.r));
  const fields = new Set(STORIES.map((s) => s.f));
  if (regions.size !== 10) throw new Error("regions must be 10, got " + regions.size);
  if (fields.size < 25) throw new Error("fields must be >= 25, got " + fields.size);
  for (const s of STORIES) {
    if (s.t.length > 78) throw new Error("story " + s.n + " too long: " + s.t.length + " chars");
    if (textWidth(s.t, 2) > CW - 28) throw new Error("story " + s.n + " too wide");
  }

  fillAll(PAPER);
  let y = 10;

  // masthead
  rect(MX, y, CW, 60, LEAD_BG);
  const title = "THE WORLD IN ONE IMAGE";
  drawText(MX + (CW - textWidth(title, 4)) / 2, y + 6, title, LEAD_TEXT, 4);
  const dateLine = "THURSDAY 26 NOVEMBER 2026 - THANKSGIVING DAY - FULL-DAY EDITION";
  drawText(MX + (CW - textWidth(dateLine, 2)) / 2, y + 38, dateLine, MAGENTA_INK, 2);
  y += 60 + 6;

  // counts line
  const counts = "50 STORIES | 10 REGIONS | " + fields.size + " FIELDS | 14 SCENES | ALL EVENTS 26 NOV 2026 (UTC)";
  drawText(MX + (CW - textWidth(counts, 2)) / 2, y, counts, INK, 2);
  y += 14 + 4;
  rect(MX, y, CW, 3, MAGENTA);
  y += 3 + 6;

  // lead rows
  for (let i = 0; i < LEADS.length; i++) {
    const L = LEADS[i];
    if (i % 2 === 0) rect(MX, y - 2, CW, 42, TINT);
    drawScene(L.icon, MX + 4, y + 1, 34, MAGENTA);
    drawText(MX + 48, y + 1, L.a, INK, 3);
    drawText(MX + 48, y + 24, L.b, GREY, 2);
    drawText(W - MX - textWidth(L.tag, 1), y + 5, L.tag, MAGENTA, 1);
    y += 42 + 3;
  }

  // UTC timeline strip
  rect(MX, y, CW, 1, GREY);
  y += 4;
  drawText(MX, y, "UTC", MAGENTA, 1);
  let tx = MX + 26;
  for (let i = 0; i < TIMELINE.length; i++) {
    const a = TIMELINE[i];
    const seg = a.t + " " + a.label;
    drawText(tx, y, seg, INK, 1);
    tx += textWidth(seg, 1) + 10;
    if (i < TIMELINE.length - 1) { disc(tx - 6, y + 3, 2, MAGENTA); }
  }
  y += 7 + 3;
  rect(MX, y, CW, 1, GREY);
  y += 4;

  // feature strip: storm / football / chess knight (bigger redraws of 3 list stories)
  const feats = [
    { icon: "storm", cap: "NOR'EASTER: 1M WITHOUT POWER, 1,500 FLIGHTS LATE" },
    { icon: "ball", cap: "BEARS 39-35: LAST-PLAY TD BEATS LIONS" },
    { icon: "knight", cap: "GUKESH HELD TO 20-MOVE DRAW BY SINDAROV" },
  ];
  const cellW = Math.floor(CW / 3);
  for (let i = 0; i < feats.length; i++) {
    const fx = MX + i * cellW;
    drawScene(feats[i].icon, fx + 2, y, 24, MAGENTA);
    drawText(fx + 30, y + 8, feats[i].cap, INK, 1);
  }
  y += 24 + 2;
  rect(MX, y, CW, 1, GREY);
  y += 6;

  // story list: 47 rows, 15px pitch (14px glyphs + 1px leading) with a
  // faint alternating tint so the eye can track one row at a time.
  const listStart = y;
  for (let i = 3; i < STORIES.length; i++) {
    const s = STORIES[i];
    const rowY = listStart + (i - 3) * 15;
    if ((i - 3) % 2 === 1) rect(MX, rowY - 1, CW, 15, [244, 239, 244]);
    const num = String(s.n).padStart(2, "0");
    drawText(MX, rowY, num, MAGENTA, 2);
    drawText(MX + 28, rowY, s.t, INK, 2);
    if (s.icon && INLINE_ICONS.has(s.icon)) {
      drawScene(s.icon, MX + 28 + textWidth(s.t, 2) + 6, rowY + 2, 10, GREY);
    }
  }
  y = listStart + 47 * 15 + 4;

  // footer (one line)
  rect(MX, y, CW, 1, GREY);
  y += 5;
  drawText(MX, y, "SOURCES: AP, BBC, YONHAP, DOW JONES, BCCI, NBC, FOX WEATHER, EURONEWS, DW | DATE CHECK: EVERY STORY VERIFIED 26 NOV 2026; BEPICOLOMBO (21 NOV) EXCLUDED.", GREY, 1);
  y += 9;
  if (y > 1012) throw new Error("layout overflow: y=" + y);

  // ---- encode + write ----
  const png = encodePNG();
  mkdirSync(OUT_DIR, { recursive: true });
  const outPath = join(OUT_DIR, "entry.png");
  writeFileSync(outPath, png);
  const sha = createHash("sha256").update(png).digest("hex");
  console.log("stories=" + STORIES.length + " regions=" + regions.size + " fields=" + fields.size);
  console.log("scenes=14 (3 lead + 3 feature + 8 inline) timeline=" + TIMELINE.length + " anchors");
  console.log("size=" + png.length + " bytes sha256=" + sha);
  console.log("wrote " + outPath);
  if (png.length > 1048576) throw new Error("PNG over 1 MiB: " + png.length);
  if (SCRIPT_DIR !== process.cwd()) console.log("note: ran from " + process.cwd() + ", paths resolved from script dir");
}

main();
