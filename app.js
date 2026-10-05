'use strict';

const $ = id => document.getElementById(id),
  canvas = $('core'),
  g = canvas.getContext('2d'),
  spec = $('spectrum'),
  sg = spec.getContext('2d');

// ── 常量 ────────────────────────────────────────────────
const BINS = 128;
const MAX_DPR = 1.0;
const AUDIO_TIMEOUT = 250;
const DECAY_RATE = 6;
const READOUT_INTERVAL = 150;

const ENERGY_SMOOTH_K = 0.055;
const ALARM_ATTACK_K = 0.045;
const ALARM_RELEASE_K = 0.022;
const ALARM_THRESHOLD = 0.30;
const ALARM_RANGE = 0.35;

// 音量归一化系数 —— energySmooth 达到此值时视为 100% 音量
const VOLUME_NORM = 0.55;

// ── 核爆触发参数（用户可调） ────────────────────────────
let chorusThreshold = 0.70;        // 0~1，用户设置音量阈值（0~100%）
let meltHoldThreshold = 2.5;       // 秒，超过阈值后持续多久触发核爆
let radDuration = 15;              // 秒，堆芯恢复时长
const DETONATION_DURATION = 13;    // 秒，核爆动画本身时长

// 核爆前预警设置
let enableWarning = true;
let warningAdvance = 0.80;

// ── 音效 ────────────────────────────────────────────────
const WARNING_SOUND_PATH = 'sounds/warning.mp3';
const EXPLOSION_SOUND_PATH = 'sounds/explosion.mp3';

let enableWarningSound = true;
let enableExplosionSound = true;

let warningSoundVolume = 0.7;
let explosionSoundVolume = 0.7;

let warningAudio = null;
let explosionAudio = null;
let warningSoundPlaying = false;

// ── 3D 相机参数 ─────────────────────────────────────────
const CAM_Z = 35;

const MIN_FREQ = 20, FREQ_RATIO = 1000;
function binToHz(i) {
  return MIN_FREQ * Math.pow(FREQ_RATIO, i / (BINS - 1));
}

// ── 状态 ────────────────────────────────────────────────
let bins = new Uint8Array(BINS),
  energy = 0, peak = 0, peakIndex = 0,
  hasInput = false,
  lastAudioTime = 0,
  isWallpaperEnv = false,
  angle = -.32, tilt = .58, zoom = 1, drag = null,
  gain = 1.4, smoothing = .75;

let sa = Math.sin(angle), ca = Math.cos(angle);
let sortedRods = null;
let lastSortAngle = NaN;
let lastFrameTime = 0;

let viewW = 0, viewH = 0, viewScale = 1;
let energySmooth = 0;
let alarmLevel = 0;
let meltLevel = 0;
let meltHoldTime = 0;
let detonationTime = -1;

// 辐射计时器
let radiationTime = -1;
let radParticles = null;

// ── 低频基线 ────────────────────────────────────────────
const lowBaseline = new Float32Array(BINS);
let lowBaselineReady = false;

// ── 核爆预警状态 ────────────────────────────────────────
let warningLevel = 0;
let warningPhase = 0;

// ── 反应堆功率状态 ──────────────────────────────────────
let reactorPower = 200;
const powerHistory = new Float32Array(120);
let powerHistoryIdx = 0;
let powerLastText = '';
let powerLastUnit = 'MW';
let powerLastClass = '';
let powerLastStatus = '';
let powerLastUpdate = 0;
const powerMonitorEl = $('power-monitor');
const powerReadingEl = $('power-reading');
const powerUnitEl = $('power-unit');
const powerBarEl = $('power-bar-fill');
const powerStatusEl = $('power-status');
const powerScopeEl = $('power-scope');
const powerScopeCtx = powerScopeEl ? powerScopeEl.getContext('2d') : null;

// ── 辐射监测器 ──────────────────────────────────────────
let radReading = 0.124;
let radLastUpdate = 0;
let radLastText = '';
let radLastUnit = '';
let radLastClass = '';
const radMonitorEl = $('rad-monitor');
const radReadingEl = $('rad-reading');
const radUnitEl = $('rad-unit');
const radBarEl = $('rad-bar-fill');
const radStatusEl = $('rad-status');

// ── RBMK 通道阵列 ──────────────────────────────────────
const GRID_HALF = 12;
const rods = [];
for (let x = -GRID_HALF; x <= GRID_HALF; x++) {
  for (let z = -GRID_HALF; z <= GRID_HALF; z++) {
    const r = Math.hypot(x, z);
    if (r > GRID_HALF + 0.35) continue;

    const s1 = Math.abs(Math.sin(x * 127.1 + z * 311.7));
    const s2 = Math.abs(Math.sin(x * 71.3 + z * 189.7));
    const s3 = Math.abs(Math.sin(x * 41.7 + z * 53.9));
    const s4 = Math.abs(Math.sin(x * 233.7 + z * 71.9));
    const s5 = Math.abs(Math.sin(x * 313.1 + z * 197.3));
    const s7 = Math.abs(Math.sin(x * 517.3 + z * 271.9));

    const isControl = s3 > 0.955;

    let heightOffset = 0;
    if (s5 > 0.975) heightOffset = 0.05;
    else if (s5 < 0.025) heightOffset = -0.04;

    const ejectCandidate = s7 > 0.955;
    const ejectDirX = (s4 - 0.5) * 0.55;
    const ejectDirZ = (s5 - 0.5) * 0.55;
    const ejectBias = 0.35 + s2 * 0.65;

    const rust = s2, shade = s4;
    let bR, bG, bB;
    if (isControl) {
      bR = 62 + shade * 18; bG = 61 + shade * 17; bB = 58 + shade * 15;
    } else {
      bR = 96 + shade * 32; bG = 94 + shade * 30; bB = 88 + shade * 26;
    }
    const rm = rust * 0.20;
    bR += rm * 38; bG += rm * 8; bB += rm * -18;

    const colTop = [bR * 1.08, bG * 1.07, bB * 1.05];
    const colBack = [bR * 0.62, bG * 0.61, bB * 0.60];
    const colRight = [bR * 0.58, bG * 0.57, bB * 0.55];
    const colFront = [bR * 0.40, bG * 0.39, bB * 0.38];
    const colLeft = [bR * 0.72, bG * 0.71, bB * 0.69];
    const colBoss = [bR * 0.72, bG * 0.71, bB * 0.69];

    rods.push({
      x, z, r,
      h: 0,
      seed: s1,
      isControl,
      heightOffset,
      ejectCandidate,
      ejectDirX,
      ejectDirZ,
      ejectBias,
      colTop, colBack, colRight, colFront, colLeft, colBoss,
    });
  }
}
$('count').textContent = rods.length;

// ── 蒸汽粒子 ───────────────────────────────────────────
const steamParticles = [];
const srnd = (() => {
  let s = 2048;
  return () => { s = (s * 9301 + 49297) % 233280; return s / 233280; };
})();
for (let i = 0; i < 14; i++) {
  const angle0 = srnd() * Math.PI * 2;
  const radius = srnd() * 8.5;
  steamParticles.push({
    ax: Math.cos(angle0) * radius,
    az: Math.sin(angle0) * radius,
    phase: srnd() * 1000,
    speed: 0.15 + srnd() * 0.2,
    maxH: 5 + srnd() * 4,
    size: 1.6 + srnd() * 1.4,
    seed: srnd(),
  });
}

// ── 钢板裂纹 ───────────────────────────────────────────
const cracks = [];
const crnd = (() => {
  let s = 512;
  return () => { s = (s * 9301 + 49297) % 233280; return s / 233280; };
})();
for (let i = 0; i < 9; i++) {
  const baseAngle = crnd() * Math.PI * 2;
  const pts = [[0, 0]];
  let rr = 0.8;
  let aa = baseAngle;
  const segs = 5;
  for (let k = 1; k <= segs; k++) {
    rr += 1.2 + crnd() * 1.6;
    aa += (crnd() - 0.5) * 0.55;
    pts.push([Math.cos(aa) * rr, Math.sin(aa) * rr]);
  }
  cracks.push({
    pts,
    threshold: 0.15 + crnd() * 0.40,
    seed: crnd(),
  });
}

// ── 读数区块搬移 ────────────────────────────────────────
const readoutSection = $('readout-section');
const stageReadout = $('stage-readout');
const readoutHomeParent = readoutSection.parentElement;
const readoutHomeNext = readoutSection.nextElementSibling;

function setReadoutOnStage(onStage) {
  if (onStage) {
    if (readoutSection.parentElement !== stageReadout) {
      stageReadout.appendChild(readoutSection);
      readoutSection.classList.add('on-stage');
      requestAnimationFrame(size);
    }
  } else {
    if (readoutSection.parentElement !== readoutHomeParent) {
      if (readoutHomeNext && readoutHomeNext.parentElement === readoutHomeParent) {
        readoutHomeParent.insertBefore(readoutSection, readoutHomeNext);
      } else {
        readoutHomeParent.appendChild(readoutSection);
      }
      readoutSection.classList.remove('on-stage');
      requestAnimationFrame(size);
    }
  }
}

// ── 背景缓存 ────────────────────────────────────────────
const bgCanvas = document.createElement('canvas');
const bgCtx = bgCanvas.getContext('2d');
let bgDirty = true;
let bgW = 0, bgH = 0, bgDpr = 0;
let bgAngle = NaN, bgTilt = NaN, bgZoom = NaN;

function size() {
  for (const c of [canvas, spec]) {
    const rect = c.getBoundingClientRect();
    const d = Math.min(devicePixelRatio || 1, MAX_DPR);
    c.width = Math.max(1, Math.round(rect.width * d));
    c.height = Math.max(1, Math.round(rect.height * d));
    c.getContext('2d').setTransform(d, 0, 0, d, 0, 0);
  }
  bgDirty = true;
}
new ResizeObserver(size).observe(canvas);
new ResizeObserver(size).observe(spec);

// ── 几何 ────────────────────────────────────────────────
function point(x, z, h = 0) {
  const s = viewScale,
    rx = x * ca - z * sa,
    rz = x * sa + z * ca;
  return [viewW / 2 + rx * s, viewH * .55 + rz * s * tilt - h * s];
}

function project3D(x, y, z) {
  const rx = x * ca - z * sa;
  const rz = x * sa + z * ca;
  const d = CAM_Z - rz;
  const s = viewScale * CAM_Z / Math.max(d, 5);
  return {
    x: viewW * 0.5 + rx * s,
    y: viewH * 0.55 + rz * s * tilt - y * s,
    z: d,
    s: s,
  };
}

function ring(c, r, color, width) {
  c.beginPath();
  for (let i = 0; i <= 140; i++) {
    const a = i / 140 * Math.PI * 2,
      p = point(Math.cos(a) * r, Math.sin(a) * r);
    i ? c.lineTo(p[0], p[1]) : c.moveTo(p[0], p[1]);
  }
  c.strokeStyle = color;
  c.lineWidth = width;
  c.stroke();
}

function srand(seed) {
  let s = seed;
  return () => {
    s = (s * 9301 + 49297) % 233280;
    return s / 233280;
  };
}

function drawTrefoil(c, cx, cy, radius, rot, stroke) {
  c.save();
  c.translate(cx, cy);
  c.rotate(rot);
  for (let i = 0; i < 3; i++) {
    c.save();
    c.rotate(i * Math.PI * 2 / 3);
    c.beginPath();
    c.moveTo(0, 0);
    c.arc(0, 0, radius, -Math.PI / 6, Math.PI / 6);
    c.closePath();
    c.strokeStyle = stroke;
    c.lineWidth = Math.max(1, radius * 0.22);
    c.stroke();
    c.restore();
  }
  c.beginPath();
  c.arc(0, 0, radius * 0.22, 0, Math.PI * 2);
  c.strokeStyle = stroke;
  c.lineWidth = Math.max(1, radius * 0.20);
  c.stroke();
  c.restore();
}

// ── 静态背景 ────────────────────────────────────────────
function renderBackground() {
  const w = viewW, H = viewH;
  const d = Math.min(devicePixelRatio || 1, MAX_DPR);
  const targetW = Math.max(1, Math.round(w * d));
  const targetH = Math.max(1, Math.round(H * d));

  if (bgCanvas.width !== targetW || bgCanvas.height !== targetH) {
    bgCanvas.width = targetW;
    bgCanvas.height = targetH;
  }
  bgCtx.setTransform(d, 0, 0, d, 0, 0);
  bgCtx.clearRect(0, 0, w, H);

  const rnd = srand(1337);

  ring(bgCtx, 14.0, '#141618', 34);
  ring(bgCtx, 13.95, '#1c1e1d', 3);
  ring(bgCtx, 13.5, '#2a2c2a', 1);

  for (let i = 0; i < 700; i++) {
    const rr = 13.2 + rnd() * 0.8;
    const aa = rnd() * Math.PI * 2;
    const pt = point(Math.cos(aa) * rr, Math.sin(aa) * rr);
    const sz = rnd() * 2.2 + 0.4;
    const v = 22 + Math.floor(rnd() * 16);
    bgCtx.fillStyle = `rgb(${v},${v + 1},${v})`;
    bgCtx.fillRect(pt[0] - sz / 2, pt[1] - sz / 2, sz, sz);
  }

  for (let i = 0; i < 8; i++) {
    const a = i * Math.PI / 4;
    const p1 = point(Math.cos(a) * 13.5, Math.sin(a) * 13.5);
    const p2 = point(Math.cos(a) * 14.0, Math.sin(a) * 14.0);
    bgCtx.beginPath();
    bgCtx.moveTo(p1[0], p1[1]);
    bgCtx.lineTo(p2[0], p2[1]);
    bgCtx.strokeStyle = 'rgba(6,7,7,0.85)';
    bgCtx.lineWidth = 1.6;
    bgCtx.stroke();
  }

  const WARN_IN = 14.05, WARN_OUT = 14.65;
  const WARN_SEG = 24;
  for (let i = 0; i < WARN_SEG; i++) {
    const a0 = i / WARN_SEG * Math.PI * 2,
      a1 = (i + 1) / WARN_SEG * Math.PI * 2;
    const isYellow = i % 2 === 0;
    bgCtx.beginPath();
    for (let k = 0; k <= 3; k++) {
      const a = a0 + (a1 - a0) * k / 3;
      const p = point(Math.cos(a) * WARN_IN, Math.sin(a) * WARN_IN);
      k ? bgCtx.lineTo(p[0], p[1]) : bgCtx.moveTo(p[0], p[1]);
    }
    for (let k = 3; k >= 0; k--) {
      const a = a0 + (a1 - a0) * k / 3;
      const p = point(Math.cos(a) * WARN_OUT, Math.sin(a) * WARN_OUT);
      bgCtx.lineTo(p[0], p[1]);
    }
    bgCtx.closePath();
    bgCtx.fillStyle = isYellow ? '#8a761c' : '#14120f';
    bgCtx.fill();
  }

  ring(bgCtx, 14.05, '#231f12', 1);
  ring(bgCtx, 14.65, '#231f12', 1);

  for (let i = 0; i < 4; i++) {
    const a = i * Math.PI / 2 + Math.PI / 4;
    const p = point(Math.cos(a) * 14.35, Math.sin(a) * 14.35);
    drawTrefoil(bgCtx, p[0], p[1], viewScale * 0.28, a, '#6b5c1a');
  }

  ring(bgCtx, 15.2, '#080909', 1);

  const plateR = 13.0;
  bgCtx.beginPath();
  for (let i = 0; i <= 80; i++) {
    const a = i / 80 * Math.PI * 2;
    const p = point(Math.cos(a) * plateR, Math.sin(a) * plateR);
    i ? bgCtx.lineTo(p[0], p[1]) : bgCtx.moveTo(p[0], p[1]);
  }
  bgCtx.closePath();
  bgCtx.fillStyle = '#0c0e0d';
  bgCtx.fill();

  bgCtx.strokeStyle = 'rgba(30,32,30,0.9)';
  bgCtx.lineWidth = 1.2;
  for (let i = -12; i <= 12; i += 6) {
    const p1 = point(i, -13, 0);
    const p2 = point(i, 13, 0);
    bgCtx.beginPath();
    bgCtx.moveTo(p1[0], p1[1]);
    bgCtx.lineTo(p2[0], p2[1]);
    bgCtx.stroke();

    const p3 = point(-13, i, 0);
    const p4 = point(13, i, 0);
    bgCtx.beginPath();
    bgCtx.moveTo(p3[0], p3[1]);
    bgCtx.lineTo(p4[0], p4[1]);
    bgCtx.stroke();
  }

  for (let i = 0; i < 1000; i++) {
    const rr = rnd() * 12.9;
    const aa = rnd() * Math.PI * 2;
    const pt = point(Math.cos(aa) * rr, Math.sin(aa) * rr);
    const sz = rnd() * 1.8 + 0.3;
    const v = 14 + Math.floor(rnd() * 14);
    bgCtx.fillStyle = `rgb(${v},${v + 1},${v - 1})`;
    bgCtx.fillRect(pt[0] - sz / 2, pt[1] - sz / 2, sz, sz);
  }

  bgW = w; bgH = H; bgDpr = d;
  bgAngle = angle; bgTilt = tilt; bgZoom = zoom;
  bgDirty = false;
}

// ── 分析 ────────────────────────────────────────────────
function updateAnalysis() {
  let sum = 0;

  for (let i = 0; i < BINS; i++) {
    const raw = bins[i];
    const v = (Number.isFinite(raw) ? raw : 0) / 255;
    sum += v * v;
  }

  energy = Math.sqrt(sum / BINS);

  const SKIP = 4;

  let bestV = 0;
  let bestI = -1;

  for (let i = SKIP; i < BINS - 1; i++) {
    const v = bins[i];
    if (v > bestV && v >= bins[i - 1] && v >= bins[i + 1]) {
      bestV = v;
      bestI = i;
    }
  }

  if (bestI >= 0 && bestV > 10) {
    peak = bestV;
    peakIndex = bestI;
  } else {
    let wSum = 0;
    let idxSum = 0;

    for (let i = SKIP; i < BINS; i++) {
      const v = bins[i];
      wSum += v;
      idxSum += v * i;
    }

    if (wSum > 0) {
      peakIndex = Math.max(SKIP, Math.min(BINS - 1, Math.round(idxSum / wSum)));
      peak = bins[peakIndex];
    } else {
      peak = 0;
      peakIndex = 0;
    }
  }
}

// ── 音量等级（0~1） ─────────────────────────────────────
function getVolumeLevel() {
  return Math.min(1, energySmooth / VOLUME_NORM);
}

// ── 音频回调 ────────────────────────────────────────────
function wallpaperAudioListener(audioArray) {
  lastAudioTime = performance.now();

  let hasSound = false;
  for (let i = 0; i < Math.min(16, audioArray.length); i++) {
    if (audioArray[i] > 0.005) { hasSound = true; break; }
  }
  if (hasSound && !hasInput) {
    hasInput = true;
    update();
  }

  const n = Math.min(BINS, audioArray.length);
  for (let i = 0; i < n; i++) {
    const raw = Math.max(0, audioArray[i]);

    if (i < 10) {
      if (!lowBaselineReady) {
        lowBaseline[i] = raw;
      } else {
        lowBaseline[i] += (raw - lowBaseline[i]) * 0.008;
      }
      const cleaned = Math.max(0, raw - lowBaseline[i] * 0.85);
      bins[i] = Math.min(255, cleaned * 255);
    } else {
      bins[i] = Math.min(255, raw * 255);
    }
  }

  for (let i = n; i < BINS; i++) {
    bins[i] = 0;
  }

  lowBaselineReady = true;
}

let lastReadoutTime = 0, lastLevelText = '', lastFreqText = '';
let lastAlarmClass = '';

// ════════════════════════════════════════════════════════
//  音效系统
// ════════════════════════════════════════════════════════
function loadWarningAudio() {
  stopWarningSound();
  warningAudio = null;
  if (!enableWarningSound) return;
  try {
    warningAudio = new Audio(WARNING_SOUND_PATH);
    warningAudio.loop = true;
    warningAudio.volume = warningSoundVolume;
    warningAudio.addEventListener('error', () => { warningAudio = null; });
    warningAudio.load();
  } catch (e) { warningAudio = null; }
}

function loadExplosionAudio() {
  explosionAudio = null;
  if (!enableExplosionSound) return;
  try {
    explosionAudio = new Audio(EXPLOSION_SOUND_PATH);
    explosionAudio.volume = explosionSoundVolume;
    explosionAudio.addEventListener('error', () => { explosionAudio = null; });
    explosionAudio.load();
  } catch (e) { explosionAudio = null; }
}

function initSounds() {
  loadWarningAudio();
  loadExplosionAudio();
}

function playWarningSound() {
  if (!warningAudio) return;
  if (!warningSoundPlaying) {
    warningSoundPlaying = true;
    try {
      warningAudio.currentTime = 0;
      warningAudio.play().catch(() => {
        warningSoundPlaying = false;
      });
    } catch (e) {
      warningSoundPlaying = false;
    }
  }
  if (radiationTime >= 0) {
    const radBoost = Math.min(1, Math.max(0, (radReading - 100) / 5000));
    warningAudio.volume = Math.min(1, warningSoundVolume * (0.6 + radBoost * 0.6));
  } else {
    warningAudio.volume = warningSoundVolume;
  }
}

function stopWarningSound() {
  if (!warningAudio || !warningSoundPlaying) return;
  warningSoundPlaying = false;
  try {
    warningAudio.pause();
    warningAudio.currentTime = 0;
  } catch (e) {}
}

function playExplosionSound() {
  if (!explosionAudio) return;
  try {
    explosionAudio.currentTime = 0;
    explosionAudio.play().catch(() => {});
  } catch (e) {}
}

function setWarningVolume(v) {
  warningSoundVolume = Math.max(0, Math.min(1, v));
  if (warningAudio) warningAudio.volume = warningSoundVolume;
}

function setExplosionVolume(v) {
  explosionSoundVolume = Math.max(0, Math.min(1, v));
  if (explosionAudio) explosionAudio.volume = explosionSoundVolume;
}

// ════════════════════════════════════════════════════════
//  反应堆功率监测器（基于音量）
// ════════════════════════════════════════════════════════
function updatePowerMonitor(t, dtSec) {
  let targetPower;

  if (detonationTime >= 0) {
    const detK = Math.min(1, detonationTime / 1.5);
    targetPower = 50000 + detK * 250000;
  } else if (radiationTime >= 0) {
    const restoreTime = Math.max(DETONATION_DURATION, radDuration);
    const remainK = Math.max(0, 1 - radiationTime / restoreTime);
    targetPower = 5000 + 250000 * remainK;
  } else {
    const volumeLevel = getVolumeLevel();
    targetPower = 200 + volumeLevel * 4800;
    targetPower += (peak / 255) * 400;
    targetPower += Math.sin(t * 0.0012) * 60;
  }

  const k = targetPower > reactorPower ? 0.14 : 0.06;
  reactorPower += (targetPower - reactorPower) * k;

  powerHistory[powerHistoryIdx] = reactorPower;
  powerHistoryIdx = (powerHistoryIdx + 1) % 120;

  if (t - powerLastUpdate < 80) return;
  powerLastUpdate = t;

  const v = reactorPower;
  let text, unit, cls, statusTxt;

  if (v >= 100000) {
    text = (v / 1000).toFixed(0);
    unit = 'GW';
  } else if (v >= 10000) {
    text = (v / 1000).toFixed(1);
    unit = 'GW';
  } else {
    text = Math.round(v).toString();
    unit = 'MW';
  }

  cls = '';
  statusTxt = '额定功率';

  if (v > 100000) { cls = 'alarm'; statusTxt = '!! 爆表 !!'; }
  else if (v > 30000) { cls = 'alarm'; statusTxt = '不可控'; }
  else if (v > 8000)  { cls = 'danger'; statusTxt = '超载'; }
  else if (v > 4500)  { cls = 'warn'; statusTxt = '偏高'; }
  else if (v < 400)   { statusTxt = '低功率'; }

  if (text !== powerLastText || unit !== powerLastUnit) {
    powerReadingEl.textContent = text;
    powerUnitEl.textContent = unit;
    powerLastText = text;
    powerLastUnit = unit;
  }

  const logP = Math.log10(Math.max(1, v));
  const pct = Math.max(2, Math.min(100, ((logP - 1) / 5.8) * 100));
  powerBarEl.style.width = pct + '%';

  if (cls !== powerLastClass) {
    powerLastClass = cls;
    powerMonitorEl.className = 'power-monitor' + (cls ? ' ' + cls : '');
  }
  if (statusTxt !== powerLastStatus) {
    powerLastStatus = statusTxt;
    powerStatusEl.textContent = statusTxt;
  }

  drawPowerScope();
}

function drawPowerScope() {
  if (!powerScopeCtx) return;
  const w = powerScopeEl.width;
  const h = powerScopeEl.height;
  const ctx = powerScopeCtx;
  ctx.clearRect(0, 0, w, h);

  ctx.strokeStyle = 'rgba(200,160,70,0.12)';
  ctx.lineWidth = 1;
  for (let i = 1; i < 4; i++) {
    const y = h * i / 4;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
  }

  ctx.beginPath();
  for (let i = 0; i < 120; i++) {
    const idx = (powerHistoryIdx + i) % 120;
    const v = powerHistory[idx];
    const logP = Math.log10(Math.max(1, v));
    const y = h - Math.min(h - 1, Math.max(1, ((logP - 1) / 5.8) * h));
    const x = (i / 119) * w;
    if (i === 0) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }

  const v = reactorPower;
  let color;
  if (v > 100000) color = '#ff2b20';
  else if (v > 30000) color = '#ff5a30';
  else if (v > 8000) color = '#ff8c28';
  else if (v > 4500) color = '#ffcc44';
  else color = '#88dd66';

  ctx.strokeStyle = color;
  ctx.lineWidth = 1.5;
  ctx.stroke();

  const lastV = reactorPower;
  const lastLogP = Math.log10(Math.max(1, lastV));
  const lastY = h - Math.min(h - 1, Math.max(1, ((lastLogP - 1) / 5.8) * h));
  ctx.fillStyle = color;
  ctx.beginPath();
  ctx.arc(w - 1, lastY, 2.5, 0, Math.PI * 2);
  ctx.fill();
}

// ════════════════════════════════════════════════════════
//  核爆预警
// ════════════════════════════════════════════════════════
function drawWarningOverlay(t, dtSec) {
  if (warningLevel < 0.015) return;

  const cx = viewW / 2;
  const cy = viewH / 2;

  const pulseRate = 1.6 + warningLevel * 6.5;
  warningPhase += dtSec * pulseRate;
  const pulse = 0.5 + 0.5 * Math.sin(warningPhase * Math.PI * 2);

  const intensity = warningLevel * (0.35 + 0.65 * pulse);

  const eg = g.createRadialGradient(cx, cy, viewH * 0.28, cx, cy, viewH * 1.1);
  eg.addColorStop(0, 'rgba(0,0,0,0)');
  eg.addColorStop(0.55, `rgba(190, 30, 20, ${intensity * 0.14})`);
  eg.addColorStop(1, `rgba(255, 50, 30, ${intensity * 0.68})`);
  g.fillStyle = eg;
  g.fillRect(0, 0, viewW, viewH);

  const bandH = 2 + warningLevel * 5;
  g.fillStyle = `rgba(255, 60, 40, ${intensity * 0.55})`;
  g.fillRect(0, 0, viewW, bandH);
  g.fillRect(0, viewH - bandH, viewW, bandH);

  const topY = Math.max(66, viewH * 0.10);
  const fs1 = Math.max(14, Math.min(22, viewW * 0.019));
  const fs2 = Math.max(11, Math.min(15, viewW * 0.013));
  const blink = pulse > 0.40;

  g.textAlign = 'center';
  g.textBaseline = 'middle';

  if (blink) {
    g.font = `bold ${fs1}px monospace`;
    g.fillStyle = `rgba(255, 80, 60, ${0.85 + intensity * 0.15})`;
    g.fillText('⚠ CORE INSTABILITY ⚠', cx, topY);

    g.font = `bold ${fs2}px monospace`;
    g.fillStyle = `rgba(255, 170, 140, ${0.75 + intensity * 0.25})`;
    g.fillText('堆芯失控 · 临界预警', cx, topY + fs1 + 6);
  } else {
    g.font = `bold ${fs1}px monospace`;
    g.fillStyle = `rgba(255, 80, 60, ${0.28 + intensity * 0.20})`;
    g.fillText('⚠ CORE INSTABILITY ⚠', cx, topY);

    g.font = `bold ${fs2}px monospace`;
    g.fillStyle = `rgba(255, 170, 140, ${0.22 + intensity * 0.18})`;
    g.fillText('堆芯失控 · 临界预警', cx, topY + fs1 + 6);
  }

  const triSize = 10 + warningLevel * 12;
  const pad = 16;
  const corners = [
    [pad, pad, 0],
    [viewW - pad, pad, Math.PI / 2],
    [viewW - pad, viewH - pad, Math.PI],
    [pad, viewH - pad, -Math.PI / 2],
  ];
  g.fillStyle = `rgba(255, 60, 40, ${0.45 + intensity * 0.55})`;
  for (const [px, py, rot] of corners) {
    g.save();
    g.translate(px, py);
    g.rotate(rot);
    g.beginPath();
    g.moveTo(0, 0);
    g.lineTo(triSize, 0);
    g.lineTo(0, triSize);
    g.closePath();
    g.fill();
    g.restore();
  }

  const barW = Math.min(440, viewW * 0.58);
  const barH = 8;
  const barX = cx - barW / 2;
  const barY = viewH - Math.max(70, viewH * 0.11);
  const progress = Math.max(0, Math.min(1, warningLevel));

  g.fillStyle = 'rgba(20, 6, 5, 0.62)';
  g.fillRect(barX - 2, barY - 2, barW + 4, barH + 4);

  g.strokeStyle = `rgba(255, 70, 50, ${0.5 + intensity * 0.5})`;
  g.lineWidth = 1;
  g.strokeRect(barX - 2, barY - 2, barW + 4, barH + 4);

  const grd = g.createLinearGradient(barX, 0, barX + barW, 0);
  grd.addColorStop(0, `rgba(255, 160, 45, ${0.75 + intensity * 0.25})`);
  grd.addColorStop(1, `rgba(255, 40, 25, ${0.88 + intensity * 0.12})`);
  g.fillStyle = grd;
  g.fillRect(barX, barY, barW * progress, barH);

  g.strokeStyle = 'rgba(255,255,255,0.14)';
  for (let i = 1; i < 10; i++) {
    const x = barX + barW * (i / 10);
    g.beginPath();
    g.moveTo(x, barY);
    g.lineTo(x, barY + barH);
    g.stroke();
  }

  g.font = 'bold 12px monospace';
  g.textAlign = 'center';
  g.textBaseline = 'middle';
  g.fillStyle = `rgba(255, 205, 185, ${0.80 + intensity * 0.20})`;
  g.fillText(`${Math.round(progress * 100)}%  TO DETONATION`,
             cx, barY + barH + 16);

  g.textAlign = 'start';
  g.textBaseline = 'alphabetic';
}

// ════════════════════════════════════════════════════════
//  辐射监测器
// ════════════════════════════════════════════════════════
function updateRadMonitor(t, dtSec) {
  const baseRad = 0.12
    + Math.sin(t * 0.0007) * 0.03
    + Math.sin(t * 0.0023) * 0.02
    + Math.sin(t * 0.0071) * 0.008;

  let radTarget;

  if (detonationTime >= 0) {
    if (detonationTime < 0.15) {
      const k = detonationTime / 0.15;
      radTarget = baseRad + k * 80000;
    } else if (detonationTime < 2) {
      const k = (detonationTime - 0.15) / 1.85;
      radTarget = 80000 + k * 220000 + Math.random() * 30000;
    } else if (detonationTime < 5) {
      const k = (detonationTime - 2) / 3;
      radTarget = 300000 * (1 - k * 0.85) + Math.random() * 40000;
    } else if (detonationTime < DETONATION_DURATION) {
      const k = (detonationTime - 5) / (DETONATION_DURATION - 5);
      radTarget = 45000 * (1 - k * 0.9) + Math.random() * 3000;
    } else {
      radTarget = 4500;
    }
  } else if (radiationTime >= 0) {
    const restoreTime = Math.max(DETONATION_DURATION, radDuration);
    const remainK = Math.max(0, 1 - radiationTime / restoreTime);
    radTarget = 100 + 4400 * remainK * remainK + Math.random() * 300;
  } else {
    radTarget = baseRad;
  }

  const radK = radTarget > radReading ? 0.30 : 0.05;
  radReading += (radTarget - radReading) * radK;

  if (t - radLastUpdate < 100) return;
  radLastUpdate = t;

  let radText, radUnit;
  const v = radReading;
  if (v < 1) {
    radText = v.toFixed(3);
    radUnit = 'μSv/h';
  } else if (v < 100) {
    radText = v.toFixed(2);
    radUnit = 'μSv/h';
  } else if (v < 10000) {
    radText = v.toFixed(0);
    radUnit = 'μSv/h';
  } else if (v < 1000000) {
    radText = (v / 1000).toFixed(1);
    radUnit = 'mSv/h';
  } else {
    radText = (v / 1000000).toFixed(2);
    radUnit = 'Sv/h';
  }

  let radCls = '';
  let statusTxt = '正常';
  if (v > 100000) { radCls = 'alarm'; statusTxt = '极度危险'; }
  else if (v > 10000) { radCls = 'alarm'; statusTxt = '严重泄漏'; }
  else if (v > 1000)  { radCls = 'danger'; statusTxt = '危险'; }
  else if (v > 1)     { radCls = 'warn'; statusTxt = '偏高'; }

  const logV = Math.log10(Math.max(0.1, v));
  const pct = Math.max(2, Math.min(100, ((logV - (-1)) / 7) * 100));

  if (radText !== radLastText || radUnit !== radLastUnit) {
    radReadingEl.textContent = radText;
    radUnitEl.textContent = radUnit;
    radLastText = radText;
    radLastUnit = radUnit;
  }
  radBarEl.style.width = pct + '%';

  if (radCls !== radLastClass) {
    radLastClass = radCls;
    radMonitorEl.className = 'rad-monitor' + (radCls ? ' ' + radCls : '');
    radStatusEl.textContent = statusTxt;
  } else if (radStatusEl.textContent !== statusTxt) {
    radStatusEl.textContent = statusTxt;
  }
}

// ════════════════════════════════════════════════════════
//  3D 核爆：爆炸对象与初始化
// ════════════════════════════════════════════════════════
let explosion = null;
let debris = null;

function initExplosion() {
  const rnd = srand(918273);
  explosion = { sparks: [] };

  for (let i = 0; i < 220; i++) {
    const theta = rnd() * Math.PI * 2;
    const phi = Math.acos(1 - 2 * rnd());
    const spd = 6 + rnd() * 24;
    explosion.sparks.push({
      x: 0, y: 1 + rnd() * 2, z: 0,
      vx: Math.sin(phi) * Math.cos(theta) * spd,
      vy: Math.cos(phi) * spd * 0.55 + 7 + rnd() * 8,
      vz: Math.sin(phi) * Math.sin(theta) * spd,
      life: 1.4 + rnd() * 3.2,
      size: 1.2 + rnd() * 3.4,
      seed: rnd(),
      dead: false,
    });
  }
}

function initDebris() {
  const rnd = srand(77713);
  debris = [];
  for (let i = 0; i < rods.length; i++) {
    const rod = rods[i];
    const dist = Math.hypot(rod.x, rod.z);
    const centerBoost = 1 + (1 - Math.min(1, dist / 13)) * 2.4;

    const a0 = Math.atan2(rod.z, rod.x) + (rnd() - 0.5) * 1.0;
    const spd = (1.1 + rnd() * 3.0) * centerBoost * 0.55;

    debris.push({
      x: rod.x,
      z: rod.z,
      h: Math.max(0.15, rod.h),
      vx: Math.cos(a0) * spd,
      vz: Math.sin(a0) * spd,
      vy: (2.6 + rnd() * 5.0) * (0.72 + centerBoost * 0.28),
      rot: rnd() * Math.PI * 2,
      rotV: (rnd() - 0.5) * 8,
      size: rod.isControl ? 0.44 : 0.40,
      col: rod.colTop,
      seed: rod.seed,
      landed: false,
      bounces: 0,
    });
  }
}

// ════════════════════════════════════════════════════════
//  辐射尘埃粒子系统
// ════════════════════════════════════════════════════════
function initRadParticles() {
  const rnd = srand(456789);
  radParticles = [];
  const N = 520;
  for (let i = 0; i < N; i++) {
    const ang = rnd() * Math.PI * 2;
    const r = Math.pow(rnd(), 0.6) * 22;

    radParticles.push({
      x: Math.cos(ang) * r,
      y: rnd() * 16,
      z: Math.sin(ang) * r,
      vx: (rnd() - 0.5) * 1.0,
      vy: 0.4 + rnd() * 1.6,
      vz: (rnd() - 0.5) * 1.0,
      phase: rnd() * 1000,
      driftAmp: 0.4 + rnd() * 1.2,
      size: 0.5 + rnd() * 2.2,
      hue: rnd(),
      pulse: rnd() * Math.PI * 2,
      appear: rnd() * 2.5,
    });
  }
}

// ════════════════════════════════════════════════════════
//  3D 核爆：物理更新
// ════════════════════════════════════════════════════════
function updateSparks3D(dtSec) {
  if (!explosion) return;
  const G = 22;
  const arr = explosion.sparks;
  for (let i = 0; i < arr.length; i++) {
    const sp = arr[i];
    if (sp.dead) continue;
    sp.vy -= G * dtSec;
    sp.x += sp.vx * dtSec;
    sp.y += sp.vy * dtSec;
    sp.z += sp.vz * dtSec;
    sp.life -= dtSec;

    if (sp.y < 0 && sp.vy < 0) {
      sp.y = 0;
      sp.vy *= -0.28;
      sp.vx *= 0.55;
      sp.vz *= 0.55;
      if (Math.abs(sp.vy) < 1.5) {
        sp.vy = 0;
        sp.vx *= 0.3;
        sp.vz *= 0.3;
      }
    }
    if (sp.life <= 0) sp.dead = true;
  }
}

function updateDebris(dtSec) {
  const GRAV = 15.5;
  for (let i = 0; i < debris.length; i++) {
    const d = debris[i];

    if (d.landed) {
      d.rotV *= 0.90;
      d.rot += d.rotV * dtSec;
      continue;
    }

    d.vy -= GRAV * dtSec;
    d.x += d.vx * dtSec;
    d.z += d.vz * dtSec;
    d.h += d.vy * dtSec;
    d.rot += d.rotV * dtSec;

    if (d.h <= 0) {
      d.h = 0;
      if (d.bounces < 2 && d.vy < -1.6) {
        d.vy = -d.vy * 0.34;
        d.vx *= 0.56;
        d.vz *= 0.56;
        d.rotV *= 0.6;
        d.bounces++;
      } else {
        d.landed = true;
        d.vy = 0;
        d.vx = 0;
        d.vz = 0;
      }
    }

    const rr = Math.hypot(d.x, d.z);
    if (rr > 26) {
      const k = 26 / rr;
      d.x *= k; d.z *= k;
      d.vx *= -0.28;
      d.vz *= -0.28;
    }
  }
}

// ════════════════════════════════════════════════════════
//  3D 核爆：绘制
// ════════════════════════════════════════════════════════
function drawShockwave3D(dtSec) {
  if (dtSec > 5.5) return;

  const t = Math.min(1, dtSec / 5.0);
  const R = 2 + t * 32;
  const fade = Math.pow(1 - t, 1.8);
  if (fade > 0.01) {
    g.beginPath();
    for (let i = 0; i <= 120; i++) {
      const ang = i / 120 * Math.PI * 2;
      const p = project3D(Math.cos(ang) * R, 0.08, Math.sin(ang) * R);
      i ? g.lineTo(p.x, p.y) : g.moveTo(p.x, p.y);
    }
    g.closePath();
    g.strokeStyle = `rgba(255, 242, 208, ${fade * 0.9})`;
    g.lineWidth = Math.max(0.5, 11 * (1 - t));
    g.stroke();
  }

  if (dtSec > 0.25) {
    const t2 = Math.min(1, (dtSec - 0.25) / 4.5);
    const R2 = 1 + t2 * 26;
    const fade2 = Math.pow(1 - t2, 2.0);
    if (fade2 > 0.01) {
      g.beginPath();
      for (let i = 0; i <= 120; i++) {
        const ang = i / 120 * Math.PI * 2;
        const p = project3D(Math.cos(ang) * R2, 0.08, Math.sin(ang) * R2);
        i ? g.lineTo(p.x, p.y) : g.moveTo(p.x, p.y);
      }
      g.closePath();
      g.strokeStyle = `rgba(255, 200, 140, ${fade2 * 0.55})`;
      g.lineWidth = Math.max(0.5, 5.5 * (1 - t2));
      g.stroke();
    }
  }

  if (dtSec > 0.5) {
    const t3 = Math.min(1, (dtSec - 0.5) / 4.0);
    const R3 = 1 + t3 * 22;
    const fade3 = Math.pow(1 - t3, 1.6) * 0.28;
    if (fade3 > 0.01) {
      g.beginPath();
      for (let i = 0; i <= 120; i++) {
        const ang = i / 120 * Math.PI * 2;
        const p = project3D(Math.cos(ang) * R3, 0.05, Math.sin(ang) * R3);
        i ? g.lineTo(p.x, p.y) : g.moveTo(p.x, p.y);
      }
      g.closePath();
      g.strokeStyle = `rgba(130, 105, 80, ${fade3})`;
      g.lineWidth = Math.max(0.5, 20 * (1 - t3));
      g.stroke();
    }
  }
}

function drawFireball3D(dtSec) {
  if (dtSec > 6.0) return;

  const t = Math.min(1, dtSec / 2.8);
  const ease = 1 - Math.pow(1 - t, 2.5);

  const baseY = 0.6 + ease * 3.2;
  const baseR = 1.5 + ease * 12;

  const spheres = [];
  spheres.push({ x: 0, y: baseY, z: 0, r: baseR, core: 1 });

  const sub = 9;
  for (let i = 0; i < sub; i++) {
    const ang = i / sub * Math.PI * 2 + dtSec * 0.55;
    const dist = ease * (3.5 + (i % 3) * 1.2);
    const yOff = Math.sin(i * 2.31) * ease * 2.4;
    spheres.push({
      x: Math.cos(ang) * dist,
      y: baseY + yOff,
      z: Math.sin(ang) * dist,
      r: baseR * (0.52 + (i % 4) * 0.10),
      core: 0.6 + (i % 3) * 0.1,
    });
  }
  for (let i = 0; i < 5; i++) {
    const ang = i / 5 * Math.PI * 2 + 1.7;
    spheres.push({
      x: Math.cos(ang) * ease * 2.2,
      y: baseY + 2 + Math.sin(i * 1.9) * ease * 3,
      z: Math.sin(ang) * ease * 2.2,
      r: baseR * 0.42,
      core: 0.55,
    });
  }

  spheres.sort((a, b) => {
    const ra = a.x * sa + a.z * ca;
    const rb = b.x * sa + b.z * ca;
    return ra - rb;
  });

  const fade = dtSec < 2.6 ? 1 : Math.max(0, 1 - (dtSec - 2.6) / 3.4);

  g.globalCompositeOperation = 'lighter';
  for (let i = 0; i < spheres.length; i++) {
    const s = spheres[i];
    const p = project3D(s.x, s.y, s.z);
    const screenR = s.r * p.s;
    if (screenR < 1.2) continue;

    const c = s.core;
    const grd = g.createRadialGradient(p.x, p.y, 0, p.x, p.y, screenR);
    grd.addColorStop(0.00, `rgba(255, 254, 244, ${0.88 * fade * c})`);
    grd.addColorStop(0.18, `rgba(255, 240, 190, ${0.80 * fade * c})`);
    grd.addColorStop(0.42, `rgba(255, 175, 65, ${0.62 * fade * c})`);
    grd.addColorStop(0.68, `rgba(205, 85, 25, ${0.45 * fade * c})`);
    grd.addColorStop(0.88, `rgba(95, 30, 12, ${0.24 * fade * c})`);
    grd.addColorStop(1.00, 'rgba(0,0,0,0)');

    g.fillStyle = grd;
    g.beginPath();
    g.arc(p.x, p.y, screenR, 0, Math.PI * 2);
    g.fill();
  }
  g.globalCompositeOperation = 'source-over';
}

function drawMushroom3D(dtSec) {
  if (dtSec < 0.35) return;

  const t = Math.min(1, (dtSec - 0.35) / 3.2);
  const ease = 1 - Math.pow(1 - t, 3.0);

  const stemTop = 3 + ease * 16;
  const stemR = 1.5 + ease * 2.6;
  const capR = 2.2 + ease * 8;

  const fade = dtSec < 6.0 ? 1 : Math.max(0, 1 - (dtSec - 6.0) / 5.0);
  const emberFade = Math.max(0, 1 - (dtSec - 0.35) / 4.5);

  const puffs = [];

  const stemN = 26;
  for (let i = 0; i < stemN; i++) {
    const pt = i / (stemN - 1);
    const y = pt * stemTop;
    const r = stemR * (0.85 + Math.sin(pt * Math.PI) * 0.6);
    const spiral = pt * 9.0;
    const layers = 3;
    for (let l = 0; l < layers; l++) {
      const ang = spiral + l / layers * Math.PI * 2;
      puffs.push({
        x: Math.cos(ang) * r * 0.55,
        y: y + Math.sin(i * 2.1 + l) * 0.3,
        z: Math.sin(ang) * r * 0.55,
        r: r * (0.7 + Math.sin(i * 1.3 + l * 2) * 0.22),
        dark: 1 - pt * 0.28,
        seed: i * 3 + l,
      });
    }
  }

  const capY = stemTop + capR * 0.3;
  const capLayers = 5;
  for (let l = 0; l < capLayers; l++) {
    const layerY = capY + (l - capLayers / 2 + 0.5) * capR * 0.22;
    const layerR = capR * (0.95 - Math.abs(l - capLayers / 2 + 0.5) * 0.13);
    const layerN = 14 + l * 7;
    for (let i = 0; i < layerN; i++) {
      const ang = i / layerN * Math.PI * 2 + l * 0.6;
      const dist = layerR * (0.35 + ((i * 7 + l * 3) % 11) / 20);
      puffs.push({
        x: Math.cos(ang) * dist,
        y: layerY + ((i + l) % 3) * capR * 0.1,
        z: Math.sin(ang) * dist,
        r: capR * (0.38 + ((i + l) % 4) * 0.09),
        dark: 0.85 - l * 0.04,
        seed: 500 + i + l * 100,
      });
    }
  }

  puffs.push({ x: 0, y: capY + capR * 0.55, z: 0, r: capR * 0.78, dark: 0.72, seed: 900 });
  puffs.push({ x: 0, y: capY - capR * 0.4, z: 0, r: capR * 0.5, dark: 0.55, seed: 901 });

  const edgeN = 28;
  for (let i = 0; i < edgeN; i++) {
    const ang = i / edgeN * Math.PI * 2;
    const dist = capR * (1.05 + Math.sin(i * 1.7) * 0.18);
    puffs.push({
      x: Math.cos(ang) * dist,
      y: capY + Math.sin(i * 2.3) * capR * 0.35,
      z: Math.sin(ang) * dist,
      r: capR * 0.45,
      dark: 0.72,
      seed: 1000 + i,
    });
  }

  puffs.push({ x: capR * 0.6, y: capY + capR * 0.35, z: -capR * 0.5, r: capR * 0.68, dark: 0.85, seed: 1101 });
  puffs.push({ x: -capR * 0.55, y: capY + capR * 0.28, z: capR * 0.45, r: capR * 0.72, dark: 0.85, seed: 1102 });
  puffs.push({ x: capR * 0.15, y: capY + capR * 0.75, z: -capR * 0.3, r: capR * 0.6, dark: 0.88, seed: 1103 });

  puffs.sort((a, b) => {
    const ra = a.x * sa + a.z * ca;
    const rb = b.x * sa + b.z * ca;
    return ra - rb;
  });

  for (let i = 0; i < puffs.length; i++) {
    const puff = puffs[i];
    const p = project3D(puff.x, puff.y, puff.z);
    const screenR = puff.r * p.s;
    if (screenR < 1.2) continue;

    const base = 0.5 * puff.dark * fade;

    const lx = p.x - screenR * 0.28;
    const ly = p.y - screenR * 0.38;
    const grd = g.createRadialGradient(lx, ly, 0, p.x, p.y, screenR);
    grd.addColorStop(0.00, `rgba(120, 100, 82, ${base * 1.1})`);
    grd.addColorStop(0.30, `rgba(85, 68, 54, ${base})`);
    grd.addColorStop(0.60, `rgba(50, 40, 32, ${base * 0.9})`);
    grd.addColorStop(0.85, `rgba(25, 19, 15, ${base * 0.55})`);
    grd.addColorStop(1.00, 'rgba(12, 9, 8, 0)');
    g.fillStyle = grd;
    g.beginPath();
    g.arc(p.x, p.y, screenR, 0, Math.PI * 2);
    g.fill();

    if (emberFade > 0.02 && puff.dark > 0.62 && puff.dark < 0.78) {
      g.globalCompositeOperation = 'lighter';
      const eGrd = g.createRadialGradient(p.x, p.y, 0, p.x, p.y, screenR * 0.75);
      eGrd.addColorStop(0.00, `rgba(255, 130, 45, ${emberFade * 0.22})`);
      eGrd.addColorStop(0.55, `rgba(180, 55, 15, ${emberFade * 0.10})`);
      eGrd.addColorStop(1.00, 'rgba(0,0,0,0)');
      g.fillStyle = eGrd;
      g.beginPath();
      g.arc(p.x, p.y, screenR * 0.75, 0, Math.PI * 2);
      g.fill();
      g.globalCompositeOperation = 'source-over';
    }
  }
}

function drawSparks3D() {
  if (!explosion) return;
  const arr = explosion.sparks;

  const live = [];
  for (let i = 0; i < arr.length; i++) {
    if (!arr[i].dead) live.push(arr[i]);
  }
  if (!live.length) return;

  live.sort((a, b) => {
    const ra = a.x * sa + a.z * ca;
    const rb = b.x * sa + b.z * ca;
    return ra - rb;
  });

  g.globalCompositeOperation = 'lighter';
  for (let i = 0; i < live.length; i++) {
    const sp = live[i];
    const p = project3D(sp.x, sp.y, sp.z);
    const screenR = Math.max(0.6, sp.size * p.s * 0.10);
    const alpha = Math.min(1, sp.life) * 0.9;

    const grd = g.createRadialGradient(p.x, p.y, 0, p.x, p.y, screenR * 4);
    grd.addColorStop(0.00, `rgba(255, 252, 230, ${alpha})`);
    grd.addColorStop(0.22, `rgba(255, 205, 110, ${alpha * 0.85})`);
    grd.addColorStop(0.58, `rgba(255, 120, 30, ${alpha * 0.38})`);
    grd.addColorStop(1.00, 'rgba(0,0,0,0)');
    g.fillStyle = grd;
    g.beginPath();
    g.arc(p.x, p.y, screenR * 4, 0, Math.PI * 2);
    g.fill();
  }
  g.globalCompositeOperation = 'source-over';
}

function drawDebris3D() {
  if (!debris) return;
  const elapsed = detonationTime >= 0 ? detonationTime : 999;

  g.globalAlpha = 0.30;
  g.fillStyle = '#000';
  for (let i = 0; i < debris.length; i++) {
    const d = debris[i];
    const p = project3D(d.x, 0, d.z);
    if (p.x < -60 || p.x > viewW + 60 || p.y < -60 || p.y > viewH + 60) continue;
    const sz = d.size * p.s * 0.85;
    g.beginPath();
    g.ellipse(p.x, p.y, sz * 0.62, sz * 0.62 * tilt, 0, 0, Math.PI * 2);
    g.fill();
  }
  g.globalAlpha = 1;

  for (let i = 0; i < debris.length; i++) {
    const d = debris[i];
    const p = project3D(d.x, d.h + 0.16, d.z);
    const sz = d.size * p.s;
    if (sz < 0.8) continue;
    if (p.x < -sz * 3 || p.x > viewW + sz * 3 ||
        p.y < -sz * 3 || p.y > viewH + sz * 3) continue;

    const heat = elapsed < 4 ? Math.max(0, 1 - (elapsed - 0.08) / 3.6) : 0;
    const glow = heat * heat;

    g.save();
    g.translate(p.x, p.y);
    g.rotate(d.rot * 0.7);
    const squash = Math.max(0.22, Math.abs(Math.cos(d.rot)));
    g.scale(1, squash);

    const r = Math.min(255, d.col[0] + glow * 320) | 0;
    const gg = Math.min(255, d.col[1] + glow * 190) | 0;
    const b = Math.min(255, d.col[2] + glow * 65) | 0;
    g.fillStyle = `rgb(${r},${gg},${b})`;
    g.fillRect(-sz * 0.5, -sz * 0.5, sz, sz);

    if (glow > 0.02) {
      g.globalCompositeOperation = 'lighter';
      g.fillStyle = `rgba(255,${(150 + glow * 90) | 0},50,${glow * 0.5})`;
      g.fillRect(-sz * 0.5, -sz * 0.5, sz, sz);
      g.globalCompositeOperation = 'source-over';
    }
    g.restore();
  }
}

// ════════════════════════════════════════════════════════
//  辐射覆盖层
// ════════════════════════════════════════════════════════
let radiationPattern = null;

function getRadiationPattern() {
  if (radiationPattern) return radiationPattern;
  const N = 256;
  const nc = document.createElement('canvas');
  nc.width = N; nc.height = N;
  const nx = nc.getContext('2d');
  const img = nx.createImageData(N, N);
  const rnd = srand(91357);
  for (let i = 0; i < N * N; i++) {
    const v = rnd();
    let a;
    if (v > 0.990) a = 180;
    else if (v > 0.940) a = 55;
    else a = 8;
    img.data[i * 4]     = 45 + v * 60;
    img.data[i * 4 + 1] = 180 + v * 70;
    img.data[i * 4 + 2] = 55 + v * 45;
    img.data[i * 4 + 3] = a;
  }
  nx.putImageData(img, 0, 0);
  radiationPattern = g.createPattern(nc, 'repeat');
  return radiationPattern;
}

const RAD_DELAY = 2.5;

function drawRadiationOverlay(elapsed) {
  const radT = elapsed - RAD_DELAY;
  if (radT <= 0) return;

  const restoreTime = Math.max(DETONATION_DURATION, radDuration);
  const effDur = Math.max(2, restoreTime - RAD_DELAY);

  let globalAlpha = 1;
  if (radT < 1.8) {
    globalAlpha = radT / 1.8;
  } else if (radT > effDur - 2.5) {
    globalAlpha = Math.max(0, (effDur - radT) / 2.5);
  }
  if (globalAlpha <= 0) return;

  const cx = viewW / 2, cy = viewH / 2;
  const fadeT = Math.min(1, radT / 3);

  if (!radParticles) initRadParticles();

  {
    const glowR = viewScale * (4 + fadeT * 26);
    const glowA = globalAlpha * fadeT * 0.22;
    const gg = g.createRadialGradient(cx, cy, 0, cx, cy, glowR);
    gg.addColorStop(0.00, `rgba(150, 240, 90, ${glowA})`);
    gg.addColorStop(0.25, `rgba(100, 200, 60, ${glowA * 0.7})`);
    gg.addColorStop(0.55, `rgba(60, 150, 40, ${glowA * 0.35})`);
    gg.addColorStop(1.00, 'rgba(0,0,0,0)');
    g.fillStyle = gg;
    g.beginPath();
    g.ellipse(cx, cy, glowR, glowR * tilt, 0, 0, Math.PI * 2);
    g.fill();
  }

  if (radParticles) {
    const sorted = radParticles.slice().sort((a, b) => {
      const ra = a.x * sa + a.z * ca;
      const rb = b.x * sa + b.z * ca;
      return ra - rb;
    });

    g.globalCompositeOperation = 'lighter';

    for (let i = 0; i < sorted.length; i++) {
      const t = sorted[i];
      const apT = Math.max(0, radT - t.appear);
      if (apT <= 0) continue;

      const lifeY = (t.y + t.vy * apT) % 16;
      const wobbleX = Math.sin(elapsed * 0.8 + t.phase) * t.driftAmp;
      const wobbleZ = Math.cos(elapsed * 0.7 + t.phase * 1.3) * t.driftAmp;
      const px = t.x + t.vx * apT * 0.5 + wobbleX;
      const pz = t.z + t.vz * apT * 0.5 + wobbleZ;

      const distC = Math.hypot(px, pz);
      const distFade = Math.max(0, 1 - distC / 26);
      const heightFade = Math.max(0, 1 - lifeY / 16) * 0.6 + 0.4;

      const pulse = 0.55 + 0.45 * Math.sin(elapsed * 3.2 + t.pulse);
      const alpha = globalAlpha * Math.min(1, apT / 1.5)
                  * distFade * heightFade * pulse * 0.55;
      if (alpha < 0.012) continue;

      const p = project3D(px, lifeY, pz);
      const screenR = Math.max(0.7, t.size * p.s * 0.65);
      if (screenR < 0.8) continue;
      if (p.x < -screenR * 5 || p.x > viewW + screenR * 5 ||
          p.y < -screenR * 5 || p.y > viewH + screenR * 5) continue;

      const cr = 120 + t.hue * 110;
      const cg = 230 + t.hue * 25;
      const cb = 60 + t.hue * 40;

      const grd = g.createRadialGradient(p.x, p.y, 0, p.x, p.y, screenR * 3);
      grd.addColorStop(0.00, `rgba(${cr|0},${cg|0},${cb|0},${alpha})`);
      grd.addColorStop(0.35, `rgba(${(cr*0.7)|0},${(cg*0.75)|0},${(cb*0.7)|0},${alpha * 0.5})`);
      grd.addColorStop(0.75, `rgba(${(cr*0.35)|0},${(cg*0.4)|0},${(cb*0.35)|0},${alpha * 0.15})`);
      grd.addColorStop(1.00, 'rgba(0,0,0,0)');

      g.fillStyle = grd;
      g.beginPath();
      g.arc(p.x, p.y, screenR * 3, 0, Math.PI * 2);
      g.fill();
    }

    g.globalCompositeOperation = 'source-over';
  }

  {
    const fogA = globalAlpha * fadeT * 0.14;
    const fogTop = viewH * 0.32;
    const fogBot = viewH * 1.0;
    const fg = g.createLinearGradient(0, fogTop, 0, fogBot);
    fg.addColorStop(0.00, 'rgba(0,0,0,0)');
    fg.addColorStop(0.45, `rgba(55, 140, 40, ${fogA * 0.55})`);
    fg.addColorStop(0.80, `rgba(70, 170, 50, ${fogA})`);
    fg.addColorStop(1.00, `rgba(40, 110, 30, ${fogA * 0.4})`);
    g.fillStyle = fg;
    g.fillRect(0, fogTop, viewW, fogBot - fogTop);
  }

  const pat = getRadiationPattern();
  if (pat) {
    g.save();
    g.globalCompositeOperation = 'screen';
    g.globalAlpha = fadeT * 0.32 * globalAlpha;
    const ox = (elapsed * 41) % 256;
    const oy = (elapsed * 67) % 256;
    g.translate(-ox, -oy);
    g.fillStyle = pat;
    g.fillRect(-256, -256, viewW + 512, viewH + 512);
    g.restore();
  }

  g.save();
  g.globalAlpha = fadeT * 0.13 * globalAlpha;
  g.fillStyle = '#8cff7a';
  const off = (elapsed * 150) % 7;
  for (let y = -off; y < viewH; y += 7) {
    g.fillRect(0, y, viewW, 1);
  }
  g.restore();

  if (fadeT > 0.4 && globalAlpha > 0.3) {
    const jitter = Math.sin(elapsed * 18) * 1.2;
    if (Math.abs(jitter) > 0.2) {
      g.save();
      g.globalCompositeOperation = 'lighter';
      g.globalAlpha = fadeT * globalAlpha * 0.06;
      g.drawImage(canvas, jitter, 0, viewW, viewH);
      g.restore();
    }
  }

  const vg = g.createRadialGradient(cx, cy, viewH * 0.16, cx, cy, viewH * 0.95);
  vg.addColorStop(0, 'rgba(0,0,0,0)');
  vg.addColorStop(0.6, `rgba(3,12,3,${fadeT * 0.4 * globalAlpha})`);
  vg.addColorStop(1, `rgba(2,10,2,${fadeT * 0.92 * globalAlpha})`);
  g.fillStyle = vg;
  g.fillRect(0, 0, viewW, viewH);

  const pulse = 0.5 + 0.5 * Math.sin(elapsed * 2.6);
  g.save();
  g.globalAlpha = fadeT * globalAlpha * (0.10 + 0.07 * pulse);
  const eg = g.createRadialGradient(cx, cy, viewH * 0.32, cx, cy, viewH * 1.05);
  eg.addColorStop(0, 'rgba(0,0,0,0)');
  eg.addColorStop(1, 'rgba(90,230,100,0.95)');
  g.fillStyle = eg;
  g.fillRect(0, 0, viewW, viewH);
  g.restore();
}

// ════════════════════════════════════════════════════════
//  核爆总绘制
// ════════════════════════════════════════════════════════
function drawDetonation(dtSec) {
  if (dtSec < 0.20) {
    const a = Math.pow(1 - dtSec / 0.20, 1.5);
    g.fillStyle = `rgba(255,255,255,${a})`;
    g.fillRect(0, 0, viewW, viewH);
  }

  drawShockwave3D(dtSec);
  drawFireball3D(dtSec);
  drawMushroom3D(dtSec);
  drawSparks3D();
}

// ── 主循环 ──────────────────────────────────────────────
function frame(t) {
  requestAnimationFrame(frame);

  const dt = lastFrameTime ? Math.min((t - lastFrameTime) / 16.67, 4) : 1;
  lastFrameTime = t;

  sa = Math.sin(angle);
  ca = Math.cos(angle);

  viewW = canvas.clientWidth;
  viewH = canvas.clientHeight;
  viewScale = Math.min(viewW / 42, viewH / 34) * zoom;

  const dpr = Math.min(devicePixelRatio || 1, MAX_DPR);
  const smoothFactor = 1 - Math.pow(.45 + smoothing * .53, dt);

  g.clearRect(0, 0, viewW, viewH);

  if (performance.now() - lastAudioTime >= AUDIO_TIMEOUT) {
    for (let i = 0; i < BINS; i++) {
      bins[i] = Math.max(0, bins[i] - DECAY_RATE);
    }
  }

  updateAnalysis();

  energySmooth += (energy - energySmooth) * Math.min(1, dt * ENERGY_SMOOTH_K);
  const volumeLevel = getVolumeLevel();

  const alarmTarget = Math.max(0, Math.min(1,
    (energySmooth - ALARM_THRESHOLD) / ALARM_RANGE));
  const alarmK = alarmTarget > alarmLevel ? ALARM_ATTACK_K : ALARM_RELEASE_K;
  alarmLevel += (alarmTarget - alarmLevel) * Math.min(1, dt * alarmK);

  const dtSec = dt / 60;

  // ════════════════════════════════════════════════════
  //  核爆触发：音量超过阈值持续一段时间
  // ════════════════════════════════════════════════════
  if (detonationTime < 0) {
    if (volumeLevel > chorusThreshold) {
      meltHoldTime += dtSec;
      if (meltHoldTime > meltHoldThreshold) {
        detonationTime = 0;
        radiationTime = 0;
        radParticles = null;
        meltHoldTime = 0;
        initExplosion();
        initDebris();
        playExplosionSound();
        stopWarningSound();
      }
    } else {
      meltHoldTime = Math.max(0, meltHoldTime - dtSec / 1.5);
    }
  } else {
    detonationTime += dtSec;
    if (detonationTime > DETONATION_DURATION) {
      detonationTime = -1;
      explosion = null;
      meltHoldTime = 0;
      alarmLevel = 0;
      energySmooth = 0;
    }
  }

  // ════════════════════════════════════════════════════
  //  核爆预警
  // ════════════════════════════════════════════════════
  {
    let warningTarget = 0;
    if (enableWarning && detonationTime < 0 && radiationTime < 0) {
      if (volumeLevel > chorusThreshold) {
        const overK = (volumeLevel - chorusThreshold) /
                      Math.max(0.05, 1 - chorusThreshold);
        const holdK = Math.min(1, meltHoldTime / Math.max(0.05, meltHoldThreshold));
        const startRatio = 1 - warningAdvance;
        if (holdK > startRatio) {
          const warnK = (holdK - startRatio) / Math.max(0.01, warningAdvance);
          warningTarget = Math.min(1, warnK * 0.7 + overK * 0.3);
        } else {
          warningTarget = Math.min(1, overK * 0.15);
        }
      }
    }

    if (warningTarget > warningLevel) {
      warningLevel += (warningTarget - warningLevel) * Math.min(1, dtSec * 10);
    } else {
      warningLevel += (warningTarget - warningLevel) * Math.min(1, dtSec * 3);
    }
    if (warningLevel < 0.005) warningLevel = 0;
  }

  // 音效控制
  {
    const inDetonation = detonationTime >= 0;
    const inRadiation = radiationTime >= 0;
    const radAlarm = inRadiation && radReading > 1000;

    if (warningLevel > 0.08 || inDetonation || radAlarm) {
      playWarningSound();
    } else {
      stopWarningSound();
    }
  }

  if (radiationTime >= 0) {
    radiationTime += dtSec;
    const restoreTime = Math.max(DETONATION_DURATION, radDuration);
    if (radiationTime > restoreTime) {
      radiationTime = -1;
      radParticles = null;
    }
  }

  if (detonationTime < 0 && radiationTime < 0 && debris) {
    debris = null;
  }

  updatePowerMonitor(t, dtSec);
  updateRadMonitor(t, dtSec);

  if (bgDirty ||
      bgW !== viewW || bgH !== viewH || bgDpr !== dpr ||
      bgAngle !== angle || bgTilt !== tilt || bgZoom !== zoom) {
    renderBackground();
  }
  g.drawImage(bgCanvas, 0, 0, viewW, viewH);

  if (detonationTime >= 0 || (debris && radiationTime >= 0)) {
    let rem = dtSec;
    while (rem > 1e-4) {
      const step = Math.min(rem, 0.03);
      if (explosion) updateSparks3D(step);
      if (debris) updateDebris(step);
      rem -= step;
    }
  }

  if (detonationTime >= 0) {
    drawDebris3D();
    drawDetonation(detonationTime);
  } else if (debris && radiationTime >= 0) {
    drawDebris3D();
  } else {
    if (meltLevel > 0.05) {
      for (let ci = 0; ci < cracks.length; ci++) {
        const cr = cracks[ci];
        const vis = Math.max(0, Math.min(1, (meltLevel - cr.threshold) / 0.35));
        if (vis <= 0.001) continue;
        g.beginPath();
        const first = point(cr.pts[0][0], cr.pts[0][1], 0.02);
        g.moveTo(first[0], first[1]);
        for (let k = 1; k < cr.pts.length; k++) {
          const p = point(cr.pts[k][0], cr.pts[k][1], 0.02);
          g.lineTo(p[0], p[1]);
        }
        g.strokeStyle = `rgba(2,2,2,${vis * 0.85})`;
        g.lineWidth = 1.4 + cr.seed * 1.2;
        g.stroke();
      }
    }

    if (!sortedRods || lastSortAngle !== angle) {
      sortedRods = [...rods].sort((a, b) =>
        (a.x * sa + a.z * ca) - (b.x * sa + b.z * ca)
      );
      lastSortAngle = angle;
    }

    const unit = viewScale;

    const cxS = viewW / 2;
    const cyS = viewH * .55;
    const halfW_fuel = 0.40;
    const halfW_ctrl = 0.42;

    const showBoss = unit > 13;
    const showNub = unit > 20;

    for (let i = 0, n = sortedRods.length; i < n; i++) {
      const rod = sortedRods[i];
      const normR = rod.r / 13.0;
      const idx = Math.min(BINS - 1, Math.round(normR * (BINS - 1)));

      const b0 = bins[idx > 0 ? idx - 1 : 0],
        b1 = bins[idx],
        b2 = bins[idx < BINS - 1 ? idx + 1 : BINS - 1];
      let amp = (b0 + b1 + b2) * 0.001307;
      amp = Math.pow(amp, 1.7) * gain;

      const isControl = rod.isControl;
      const baseH = (isControl ? 0.35 : 0.25) + rod.heightOffset;
      const ampScale = isControl ? 2.4 : 3.8;

      let ejectBoost = 0;
      if (meltLevel > 0.05 && rod.ejectCandidate) {
        const k = Math.max(0, Math.min(1,
          (meltLevel - 0.05) / 0.55)) * rod.ejectBias;
        ejectBoost = k * 8.5;
      }

      let target = baseH + amp * ampScale + ejectBoost;
      target += Math.sin(t * 0.008 + rod.seed * 137) * energySmooth * 0.15;

      rod.h += (target - rod.h) * smoothFactor;

      const rx = rod.x;
      const rz = rod.z;
      const h = rod.h;

      const halfW = isControl ? halfW_ctrl : halfW_fuel;

      const ss = unit;
      const aT_rx = rx - halfW, aT_rz = rz - halfW;
      const bT_rx = rx + halfW, bT_rz = rz - halfW;
      const cT_rx = rx + halfW, cT_rz = rz + halfW;
      const dT_rx = rx - halfW, dT_rz = rz + halfW;

      const aT_x = cxS + (aT_rx * ca - aT_rz * sa) * ss;
      const aT_y = cyS + (aT_rx * sa + aT_rz * ca) * ss * tilt - h * ss;
      const bT_x = cxS + (bT_rx * ca - bT_rz * sa) * ss;
      const bT_y = cyS + (bT_rx * sa + bT_rz * ca) * ss * tilt - h * ss;
      const cT_x = cxS + (cT_rx * ca - cT_rz * sa) * ss;
      const cT_y = cyS + (cT_rx * sa + cT_rz * ca) * ss * tilt - h * ss;
      const dT_x = cxS + (dT_rx * ca - dT_rz * sa) * ss;
      const dT_y = cyS + (dT_rx * sa + dT_rz * ca) * ss * tilt - h * ss;

      const a0_x = cxS + (aT_rx * ca - aT_rz * sa) * ss;
      const a0_y = cyS + (aT_rx * sa + aT_rz * ca) * ss * tilt;
      const b0_x = cxS + (bT_rx * ca - bT_rz * sa) * ss;
      const b0_y = cyS + (bT_rx * sa + bT_rz * ca) * ss * tilt;
      const c0_x = cxS + (cT_rx * ca - cT_rz * sa) * ss;
      const c0_y = cyS + (cT_rx * sa + cT_rz * ca) * ss * tilt;
      const d0_x = cxS + (dT_rx * ca - dT_rz * sa) * ss;
      const d0_y = cyS + (dT_rx * sa + dT_rz * ca) * ss * tilt;

      const dyn = amp * 55;
      const dynR = dyn;
      const dynG = dyn * 0.9;
      const dynB = dyn * 0.8;

      const meltHeat = meltLevel * (rod.ejectCandidate ? 1 : 0.4);
      const tintR = meltHeat * 70;
      const tintG = -meltHeat * 30;
      const tintB = -meltHeat * 45;

      g.fillStyle = `rgb(${Math.max(0,(rod.colBack[0] + dynR + tintR))|0},${Math.max(0,(rod.colBack[1] + dynG + tintG))|0},${Math.max(0,(rod.colBack[2] + dynB + tintB))|0})`;
      g.beginPath();
      g.moveTo(aT_x, aT_y); g.lineTo(a0_x, a0_y); g.lineTo(b0_x, b0_y); g.lineTo(bT_x, bT_y);
      g.closePath(); g.fill();

      g.fillStyle = `rgb(${Math.max(0,(rod.colRight[0] + dynR + tintR))|0},${Math.max(0,(rod.colRight[1] + dynG + tintG))|0},${Math.max(0,(rod.colRight[2] + dynB + tintB))|0})`;
      g.beginPath();
      g.moveTo(bT_x, bT_y); g.lineTo(b0_x, b0_y); g.lineTo(c0_x, c0_y); g.lineTo(cT_x, cT_y);
      g.closePath(); g.fill();

      g.fillStyle = `rgb(${Math.max(0,(rod.colFront[0] + dynR + tintR))|0},${Math.max(0,(rod.colFront[1] + dynG + tintG))|0},${Math.max(0,(rod.colFront[2] + dynB + tintB))|0})`;
      g.beginPath();
      g.moveTo(cT_x, cT_y); g.lineTo(c0_x, c0_y); g.lineTo(d0_x, d0_y); g.lineTo(dT_x, dT_y);
      g.closePath(); g.fill();

      g.fillStyle = `rgb(${Math.max(0,(rod.colLeft[0] + dynR + tintR))|0},${Math.max(0,(rod.colLeft[1] + dynG + tintG))|0},${Math.max(0,(rod.colLeft[2] + dynB + tintB))|0})`;
      g.beginPath();
      g.moveTo(dT_x, dT_y); g.lineTo(d0_x, d0_y); g.lineTo(a0_x, a0_y); g.lineTo(aT_x, aT_y);
      g.closePath(); g.fill();

      g.fillStyle = `rgb(${Math.max(0,(rod.colTop[0] + dynR + tintR))|0},${Math.max(0,(rod.colTop[1] + dynG + tintG))|0},${Math.max(0,(rod.colTop[2] + dynB + tintB))|0})`;
      g.beginPath();
      g.moveTo(aT_x, aT_y); g.lineTo(bT_x, bT_y); g.lineTo(cT_x, cT_y); g.lineTo(dT_x, dT_y);
      g.closePath(); g.fill();

      if (showBoss) {
        const cxRod = (aT_x + bT_x + cT_x + dT_x) * 0.25;
        const cyRod = (aT_y + bT_y + cT_y + dT_y) * 0.25;
        const R = (isControl ? 0.26 : 0.24) * ss;
        const R_tilt = R * tilt;

        g.fillStyle = `rgb(${Math.max(0,(rod.colBoss[0] + dynR * 0.7 + tintR * 0.7))|0},${Math.max(0,(rod.colBoss[1] + dynG * 0.7 + tintG * 0.7))|0},${Math.max(0,(rod.colBoss[2] + dynB * 0.7 + tintB * 0.7))|0})`;
        g.beginPath();
        for (let k = 0; k < 6; k++) {
          const ang = k / 6 * Math.PI * 2 + Math.PI / 6;
          const px = cxRod + Math.cos(ang) * R;
          const py = cyRod + Math.sin(ang) * R_tilt;
          k ? g.lineTo(px, py) : g.moveTo(px, py);
        }
        g.closePath();
        g.fill();

        if (showNub) {
          const R2 = 0.09 * ss;
          const R2_tilt = R2 * tilt;
          g.fillStyle = `rgb(${Math.max(0,(rod.colBoss[0] * 1.35 + dynR * 0.9 + tintR))|0},${Math.max(0,(rod.colBoss[1] * 1.35 + dynG * 0.9 + tintG))|0},${Math.max(0,(rod.colBoss[2] * 1.35 + dynB * 0.9 + tintB))|0})`;
          g.beginPath();
          for (let k = 0; k < 6; k++) {
            const ang = k / 6 * Math.PI * 2 + Math.PI / 6;
            const px = cxRod + Math.cos(ang) * R2;
            const py = cyRod + Math.sin(ang) * R2_tilt;
            k ? g.lineTo(px, py) : g.moveTo(px, py);
          }
          g.closePath();
          g.fill();
        }
      }
    }

    if (meltLevel > 0.05) {
      const steamAlpha = Math.min(1, (meltLevel - 0.05) / 0.5) * 0.16;
      g.globalAlpha = steamAlpha;
      for (let i = 0; i < steamParticles.length; i++) {
        const p = steamParticles[i];
        const lifeT = ((t * 0.001 * p.speed + p.phase) % 1);
        const hh = lifeT * p.maxH;
        const sz = p.size * (0.6 + lifeT * 0.9);
        const drift = lifeT * 0.4;
        const px = p.ax * (1 - drift * 0.2);
        const pz = p.az * (1 - drift * 0.2);
        const sc = point(px, pz, hh);

        const R = sz * unit;
        const Rt = R * tilt;
        g.fillStyle = '#0a0806';
        g.beginPath();
        for (let k = 0; k < 6; k++) {
          const ang = k / 6 * Math.PI * 2 + p.seed * 6;
          const qx = sc[0] + Math.cos(ang) * R;
          const qy = sc[1] + Math.sin(ang) * Rt;
          k ? g.lineTo(qx, qy) : g.moveTo(qx, qy);
        }
        g.closePath();
        g.fill();
      }
      g.globalAlpha = 1;
    }

    if (meltLevel > 0.08) {
      const tAlpha = Math.min(1, (meltLevel - 0.08) / 0.4);
      const r0 = 107, g0 = 92, b0 = 26;
      const r1 = 120, g1 = 24, b1 = 16;
      const rM = Math.round(r0 + (r1 - r0) * tAlpha);
      const gM = Math.round(g0 + (g1 - g0) * tAlpha);
      const bM = Math.round(b0 + (b1 - b0) * tAlpha);
      const col = `rgb(${rM},${gM},${bM})`;

      for (let i = 0; i < 4; i++) {
        const a = i * Math.PI / 2 + Math.PI / 4;
        const p = point(Math.cos(a) * 14.35, Math.sin(a) * 14.35);
        drawTrefoil(g, p[0], p[1], viewScale * 0.28, a, col);
      }
    }

    if (warningLevel > 0.015) {
      drawWarningOverlay(t, dtSec);
    }
  }

  if (radiationTime >= 0) {
    drawRadiationOverlay(radiationTime);
  }

  const sw = spec.clientWidth, sh = spec.clientHeight;
  sg.clearRect(0, 0, sw, sh);
  for (let i = 0; i < 48; i++) {
    const fi = Math.pow(i / 47, 2) * (BINS - 1);
    const v = bins[Math.min(BINS - 1, Math.round(fi))] / 255;
    sg.fillStyle = i < 12 ? '#b09540' : i < 30 ? '#95a058' : '#6f8880';
    sg.fillRect(i * sw / 48, sh - Math.max(2, v * sh),
      sw / 48 - 3, Math.max(2, v * sh));
  }

  if (t - lastReadoutTime >= READOUT_INTERVAL) {
    lastReadoutTime = t;
    const live = performance.now() - lastAudioTime < AUDIO_TIMEOUT;

    const lvText = live
      ? String(Math.round(20 * Math.log10(Math.max(energy, .001))))
      : '—';
    if (lvText !== lastLevelText) {
      lastLevelText = lvText;
      $('level').innerHTML = lvText + '<small>dB</small>';
    }

    const fqText = (live && peak > 0)
      ? String(Math.round(binToHz(peakIndex)))
      : '—';
    if (fqText !== lastFreqText) {
      lastFreqText = fqText;
      $('freq').innerHTML = fqText + '<small>Hz</small>';
    }

    const cls = alarmLevel > 0.6 ? 'alarm' : alarmLevel > 0.3 ? 'warn' : '';
    if (cls !== lastAlarmClass) {
      lastAlarmClass = cls;
      const lv = $('level'), fq = $('freq');
      lv.classList.remove('alarm', 'warn');
      fq.classList.remove('alarm', 'warn');
      if (cls) { lv.classList.add(cls); fq.classList.add(cls); }
    }
  }
}

// ── 环境检测与初始化 ────────────────────────────────────
function initAudio() {
  if (typeof window.wallpaperRegisterAudioListener === 'function') {
    isWallpaperEnv = true;
    window.wallpaperRegisterAudioListener(wallpaperAudioListener);
    $('source-name').textContent = '系统音频';
    $('source-sub').textContent = '监听系统全局音频输出';
    $('message').textContent = '音频由系统提供，仅在本机处理。';
  } else {
    isWallpaperEnv = false;
    $('source-name').textContent = '预览模式';
    $('source-sub').textContent = '浏览器无音频输入，画面保持静止';
    $('message').textContent = '请在 Wallpaper Engine 中查看音频响应效果。';
  }
  update();
}

function update() {
  if (!isWallpaperEnv) {
    $('status').textContent = '预览模式 · 无音频输入';
    return;
  }
  $('status').textContent = hasInput ? '音频响应 · 运行中' : '等待音频…';
}

// ── 数值展示（只读） ────────────────────────────────────
const gainEl = $('gain'), smoothEl = $('smooth');

function makeReadonly(el) {
  el.readOnly = true;
  el.tabIndex = -1;
  el.setAttribute('aria-readonly', 'true');
  el.addEventListener('keydown', e => e.preventDefault());
  el.addEventListener('focus', () => el.blur());
  el.addEventListener('selectstart', e => e.preventDefault());
  el.addEventListener('mousedown', e => e.preventDefault());
  el.addEventListener('wheel', e => e.preventDefault(), { passive: false });
}
makeReadonly(gainEl);
makeReadonly(smoothEl);
makeReadonly($('threshold'));
makeReadonly($('melthold'));
makeReadonly($('radduration'));

// ── Wallpaper Engine 属性监听 ───────────────────────────
window.wallpaperPropertyListener = {
  applyUserProperties: function (p) {
    if (p.gain !== undefined) {
      gain = +p.gain.value;
      gainEl.value = gain.toFixed(1);
    }
    if (p.smoothing !== undefined) {
      smoothing = +p.smoothing.value / 100;
      smoothEl.value = Math.round(smoothing * 100);
    }
    if (p.readoutonstage !== undefined) {
      setReadoutOnStage(!!p.readoutonstage.value);
    }
    if (p.detonationthreshold !== undefined) {
      chorusThreshold = Math.max(0.00, Math.min(1.00, +p.detonationthreshold.value / 100));
      const thEl = $('threshold');
      if (thEl) thEl.value = Math.round(chorusThreshold * 100);
    }
    if (p.meltholdtime !== undefined) {
      meltHoldThreshold = Math.max(0.5, Math.min(6, +p.meltholdtime.value / 10));
      const mhEl = $('melthold');
      if (mhEl) mhEl.value = Math.round(meltHoldThreshold * 10);
    }
    if (p.radiationduration !== undefined) {
      radDuration = Math.max(5, Math.min(60, +p.radiationduration.value));
      const rdEl = $('radduration');
      if (rdEl) rdEl.value = Math.round(radDuration);
    }
    if (p.enablewarning !== undefined) {
      enableWarning = !!p.enablewarning.value;
    }
    if (p.warningadvance !== undefined) {
      warningAdvance = Math.max(0, Math.min(1, +p.warningadvance.value / 100));
    }
    if (p.enablewarningsound !== undefined) {
      const on = !!p.enablewarningsound.value;
      if (on !== enableWarningSound) {
        enableWarningSound = on;
        loadWarningAudio();
      }
    }
    if (p.enableexplosionsound !== undefined) {
      const on = !!p.enableexplosionsound.value;
      if (on !== enableExplosionSound) {
        enableExplosionSound = on;
        loadExplosionAudio();
      }
    }
    if (p.warningsoundvolume !== undefined) {
      setWarningVolume(+p.warningsoundvolume.value / 100);
    }
    if (p.explosionsoundvolume !== undefined) {
      setExplosionVolume(+p.explosionsoundvolume.value / 100);
    }
  },
  applyUserPropertiesOnReady: function (p) {
    this.applyUserProperties(p);
  }
};

// ── 隐藏式控制台 ────────────────────────────────────────
(function initPanel(){
  const handle = $('panel-handle');
  const aside = document.querySelector('aside');
  const canHover = matchMedia('(hover:hover) and (pointer:fine)').matches;
  const isNarrow = matchMedia('(max-width:700px)');
  let hideTimer = 0;

  const isOpen = () => document.body.classList.contains('panel-open');

  function open(){
    document.body.classList.add('panel-open');
    handle.setAttribute('aria-expanded','true');
    handle.textContent = '✕';
  }
  function close(){
    document.body.classList.remove('panel-open');
    handle.setAttribute('aria-expanded','false');
    handle.textContent = '控';
  }
  function cancelHide(){ clearTimeout(hideTimer); }

  function scheduleHide(){
    if (!canHover || isNarrow.matches) return;
    cancelHide();
    hideTimer = setTimeout(close, 600);
  }

  handle.addEventListener('click', e => {
    e.stopPropagation();
    isOpen() ? close() : open();
  });

  if (canHover){
    handle.addEventListener('mouseenter', () => {
      cancelHide();
      open();
    });
    handle.addEventListener('mouseleave', scheduleHide);

    aside.addEventListener('mouseenter', () => {
      cancelHide();
    });
    aside.addEventListener('mouseleave', scheduleHide);
  }

  window.addEventListener('keydown', e => {
    if (e.key === 'Escape' && isOpen()) close();
  });

  isNarrow.addEventListener?.('change', close);
})();

// ── 交互：拖动旋转 ──────────────────────────────────────
canvas.addEventListener('dragstart', e => e.preventDefault());
canvas.addEventListener('selectstart', e => e.preventDefault());

canvas.onpointerdown = e => {
  e.preventDefault();
  drag = { x: e.clientX, y: e.clientY };
  canvas.setPointerCapture(e.pointerId);
};
canvas.onpointermove = e => {
  if (!drag) return;
  angle += (e.clientX - drag.x) * .006;
  tilt = Math.max(.25, Math.min(.85, tilt + (e.clientY - drag.y) * .002));
  drag = { x: e.clientX, y: e.clientY };
};
canvas.onpointerup = canvas.onpointercancel = () => drag = null;

// ── 交互：缩放 / 重置 ───────────────────────────────────
$('zoom-in').onclick = () => zoom = Math.min(1.5, zoom + .1);
$('zoom-out').onclick = () => zoom = Math.max(.65, zoom - .1);
$('reset').onclick = () => {
  angle = -.32;
  tilt = .58;
  zoom = 1;
  bgDirty = true;
};

// ── 交互：手动引爆 ──────────────────────────────────────
const detonateBtn = $('detonate-btn');
detonateBtn.onclick = () => {
  if (detonationTime >= 0 || radiationTime >= 0) return;
  detonationTime = 0;
  radiationTime = 0;
  radParticles = null;
  meltHoldTime = 0;
  warningLevel = 0;
  initExplosion();
  initDebris();
  playExplosionSound();
  stopWarningSound();
};

// ── 启动 ────────────────────────────────────────────────
initAudio();
initSounds();
size();
requestAnimationFrame(frame);