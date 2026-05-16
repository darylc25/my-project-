'use strict';

/**
 * ================================================================
 *  TETRIS — Complete Production Implementation
 * ================================================================
 *
 *  Architecture:
 *    Bag      — 7-bag randomizer (Fisher-Yates shuffle)
 *    Board    — Grid state, collision detection, line clearing
 *    Piece    — Active tetromino with SRS rotation + wall kicks
 *    Renderer — Canvas drawing (board, ghost, active, next-piece)
 *    Game     — Master controller: loop, physics, input, scoring
 *
 *  Controls:
 *    ← → Arrow   Move left / right (with DAS auto-repeat)
 *    ↑ Arrow / X  Rotate clockwise
 *    Z            Rotate counter-clockwise
 *    ↓ Arrow      Soft drop (+1 pt/row)
 *    Space        Hard drop (+2 pts/row)
 *    P            Pause / resume
 *    Enter/Space  Start / resume from overlay
 *
 *  Scoring (× level):
 *    1 line = 100   2 lines = 300   3 lines = 500   4 lines = 800
 *
 * ================================================================
 */

// ── SECTION 1 ── Constants ────────────────────────────────────

const COLS       = 10;          // board width  (columns)
const ROWS       = 20;          // board height (rows)
const BLOCK      = 30;          // px — main board cell size
const NB         = 24;          // px — next-piece preview cell size
const NB_GRID    = 4;           // next-piece preview bounding box dimension

/** Points awarded per simultaneous line clear, multiplied by current level. */
const SCORE_TABLE = [0, 100, 300, 500, 800];

/** Lines cleared before levelling up. */
const LINES_PER_LEVEL = 10;

/**
 * Gravity drop interval in milliseconds for each level (index 0 = level 1).
 * Capped at level 15 (index 14).
 */
const GRAVITY_MS = [
  800, 720, 630, 550, 470,
  380, 300, 220, 130,  80,
   80,  80,  80,  80,  80,
];

/** Delayed Auto Shift: time (ms) before horizontal auto-repeat begins. */
const DAS_DELAY = 170;
/** DAS repeat interval (ms) — how fast the piece slides while key is held. */
const DAS_RATE  =  50;

/** Time (ms) before a landed piece locks into the board. */
const LOCK_DELAY_MS  = 500;
/** Maximum move/rotate resets to the lock timer before it ignores resets. */
const LOCK_RESET_MAX =  15;

// ── SECTION 2 ── Tetromino Definitions ───────────────────────

/**
 * Each type defines `color` and `states` (4 rotation matrices).
 * Matrices are [row][col] with 1 = filled.
 * Rotation states: 0 = spawn, 1 = CW, 2 = 180°, 3 = CCW.
 */
const PIECES = {
  I: {
    color: '#00CFCF',
    states: [
      [[0,0,0,0], [1,1,1,1], [0,0,0,0], [0,0,0,0]],
      [[0,0,1,0], [0,0,1,0], [0,0,1,0], [0,0,1,0]],
      [[0,0,0,0], [0,0,0,0], [1,1,1,1], [0,0,0,0]],
      [[0,1,0,0], [0,1,0,0], [0,1,0,0], [0,1,0,0]],
    ],
  },
  O: {
    color: '#CFCF00',
    // O-piece does not rotate; all four states are identical
    states: [
      [[0,1,1,0], [0,1,1,0], [0,0,0,0], [0,0,0,0]],
      [[0,1,1,0], [0,1,1,0], [0,0,0,0], [0,0,0,0]],
      [[0,1,1,0], [0,1,1,0], [0,0,0,0], [0,0,0,0]],
      [[0,1,1,0], [0,1,1,0], [0,0,0,0], [0,0,0,0]],
    ],
  },
  T: {
    color: '#9F00CF',
    states: [
      [[0,1,0], [1,1,1], [0,0,0]],
      [[0,1,0], [0,1,1], [0,1,0]],
      [[0,0,0], [1,1,1], [0,1,0]],
      [[0,1,0], [1,1,0], [0,1,0]],
    ],
  },
  S: {
    color: '#00CF00',
    states: [
      [[0,1,1], [1,1,0], [0,0,0]],
      [[0,1,0], [0,1,1], [0,0,1]],
      [[0,0,0], [0,1,1], [1,1,0]],
      [[1,0,0], [1,1,0], [0,1,0]],
    ],
  },
  Z: {
    color: '#CF2020',
    states: [
      [[1,1,0], [0,1,1], [0,0,0]],
      [[0,0,1], [0,1,1], [0,1,0]],
      [[0,0,0], [1,1,0], [0,1,1]],
      [[0,1,0], [1,1,0], [1,0,0]],
    ],
  },
  J: {
    color: '#2040CF',
    states: [
      [[1,0,0], [1,1,1], [0,0,0]],
      [[0,1,1], [0,1,0], [0,1,0]],
      [[0,0,0], [1,1,1], [0,0,1]],
      [[0,1,0], [0,1,0], [1,1,0]],
    ],
  },
  L: {
    color: '#CF7F00',
    states: [
      [[0,0,1], [1,1,1], [0,0,0]],
      [[0,1,0], [0,1,0], [0,1,1]],
      [[0,0,0], [1,1,1], [1,0,0]],
      [[1,1,0], [0,1,0], [0,1,0]],
    ],
  },
};

// ── SECTION 3 ── SRS Wall-Kick Tables ────────────────────────

/**
 * Kick offsets are [Δcol, Δrow] in screen-space (+col=right, +row=down).
 * Derived from the Tetris Guideline (y-axis is inverted vs. the spec).
 *
 * Key format: '<fromState>><toState>'
 */
const KICKS_JLSTZ = {
  '0>1': [[ 0, 0], [-1, 0], [-1,-1], [ 0, 2], [-1, 2]],
  '1>0': [[ 0, 0], [ 1, 0], [ 1, 1], [ 0,-2], [ 1,-2]],
  '1>2': [[ 0, 0], [ 1, 0], [ 1, 1], [ 0,-2], [ 1,-2]],
  '2>1': [[ 0, 0], [-1, 0], [-1,-1], [ 0, 2], [-1, 2]],
  '2>3': [[ 0, 0], [ 1, 0], [ 1,-1], [ 0, 2], [ 1, 2]],
  '3>2': [[ 0, 0], [-1, 0], [-1, 1], [ 0,-2], [-1,-2]],
  '3>0': [[ 0, 0], [-1, 0], [-1, 1], [ 0,-2], [-1,-2]],
  '0>3': [[ 0, 0], [ 1, 0], [ 1,-1], [ 0, 2], [ 1, 2]],
};

const KICKS_I = {
  '0>1': [[ 0, 0], [-2, 0], [ 1, 0], [-2, 1], [ 1,-2]],
  '1>0': [[ 0, 0], [ 2, 0], [-1, 0], [ 2,-1], [-1, 2]],
  '1>2': [[ 0, 0], [-1, 0], [ 2, 0], [-1,-2], [ 2, 1]],
  '2>1': [[ 0, 0], [ 1, 0], [-2, 0], [ 1, 2], [-2,-1]],
  '2>3': [[ 0, 0], [ 2, 0], [-1, 0], [ 2,-1], [-1, 2]],
  '3>2': [[ 0, 0], [-2, 0], [ 1, 0], [-2, 1], [ 1,-2]],
  '3>0': [[ 0, 0], [ 1, 0], [-2, 0], [ 1, 2], [-2,-1]],
  '0>3': [[ 0, 0], [-1, 0], [ 2, 0], [-1,-2], [ 2, 1]],
};

// ── SECTION 4 ── Sound Engine ─────────────────────────────────

/**
 * Procedural audio using the Web Audio API.
 * Generates all sound effects programmatically — no audio files needed.
 * Lazy-initialises AudioContext on the first user gesture to comply
 * with browser autoplay policies.
 */
class SoundEngine {
  constructor() {
    this._audioCtx = null;
    this.muted     = false;
  }

  /** Lazily create (and resume) the AudioContext. */
  _getCtx() {
    if (!this._audioCtx) {
      this._audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    }
    if (this._audioCtx.state === 'suspended') this._audioCtx.resume();
    return this._audioCtx;
  }

  /**
   * Schedules a single synthesised tone.
   *
   * @param {number}      freq     Hz at start
   * @param {string}      type     OscillatorType: 'sine'|'square'|'sawtooth'|'triangle'
   * @param {number}      dur      Duration in seconds
   * @param {number}      vol      Peak gain (0–1)
   * @param {number}      delay    Start offset from now (seconds)
   * @param {number|null} freqEnd  Optional end frequency for pitch sweep
   */
  _tone(freq, type, dur, vol = 0.25, delay = 0, freqEnd = null) {
    if (this.muted) return;
    const ctx = this._getCtx();
    const t   = ctx.currentTime + delay;

    const osc  = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.connect(gain);
    gain.connect(ctx.destination);

    osc.type = type;
    osc.frequency.setValueAtTime(freq, t);
    if (freqEnd !== null) {
      osc.frequency.linearRampToValueAtTime(freqEnd, t + dur);
    }

    // Quick attack → exponential decay
    gain.gain.setValueAtTime(0, t);
    gain.gain.linearRampToValueAtTime(vol, t + 0.008);
    gain.gain.exponentialRampToValueAtTime(0.001, t + dur);

    osc.start(t);
    osc.stop(t + dur + 0.02);
  }

  // ── Public sound effects ──────────────────────────────────────

  /** Short blip when piece moves left or right. */
  move() {
    this._tone(160, 'square', 0.04, 0.07);
  }

  /** Quick pitch-rise when piece rotates. */
  rotate() {
    this._tone(280, 'square', 0.07, 0.12, 0, 380);
  }

  /** Subtle tick on soft drop. */
  softDrop() {
    this._tone(140, 'square', 0.04, 0.06);
  }

  /** Heavy impact on hard drop (two-layer thud). */
  hardDrop() {
    this._tone(130, 'square', 0.07, 0.35);
    this._tone(80,  'square', 0.14, 0.30, 0.05);
  }

  /** Solid thud when piece locks onto the board. */
  lock() {
    this._tone(200, 'square', 0.06, 0.20);
    this._tone(130, 'square', 0.10, 0.15, 0.04);
  }

  /**
   * Chime sequence — scales with lines cleared.
   * 4 lines (Tetris) plays a special triumphant jingle.
   *
   * @param {number} count Lines cleared (1–4)
   */
  lineClear(count) {
    if (count >= 4) {
      // Tetris! — ascending fanfare
      [523, 659, 784, 1047, 784, 1047].forEach((f, i) =>
        this._tone(f, 'sine', 0.20, 0.55, i * 0.09),
      );
    } else {
      // 1–3 lines: ascending chimes (more notes for more lines)
      [523, 659, 784, 1047].slice(0, count + 1).forEach((f, i) =>
        this._tone(f, 'sine', 0.22, 0.48, i * 0.10),
      );
    }
  }

  /** Ascending arpeggio on level-up. */
  levelUp() {
    [392, 523, 659, 784, 1047].forEach((f, i) =>
      this._tone(f, 'sine', 0.16, 0.42, i * 0.09),
    );
  }

  /** Descending sad melody on game over. */
  gameOver() {
    [523, 494, 440, 392, 349, 294, 262].forEach((f, i) =>
      this._tone(f, 'sawtooth', 0.28, 0.38, i * 0.18),
    );
  }
}

// ── SECTION 5 ── Bag Randomizer ───────────────────────────────

/**
 * Implements the 7-bag randomizer required by the Tetris Guideline.
 * Each "bag" contains exactly one copy of every piece type, shuffled.
 * When empty the bag is refilled, preventing long droughts.
 */
class Bag {
  constructor() {
    this._queue = [];
  }

  /** Returns the next piece type string (e.g. 'I', 'T'…). */
  next() {
    if (this._queue.length === 0) this._refill();
    return this._queue.pop();
  }

  /** Peek at the upcoming piece without consuming it. */
  peek() {
    if (this._queue.length === 0) this._refill();
    return this._queue[this._queue.length - 1];
  }

  _refill() {
    // Fisher-Yates shuffle of all 7 piece types
    const types = Object.keys(PIECES);
    for (let i = types.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [types[i], types[j]] = [types[j], types[i]];
    }
    this._queue = types;
  }
}

// ── SECTION 6 ── Board ────────────────────────────────────────

/**
 * Manages the locked-cell grid.  Each cell is `null` (empty) or a
 * CSS color string (filled).
 */
class Board {
  constructor() {
    /** @type {(string|null)[][]} grid[row][col] */
    this.grid = this._emptyGrid();
  }

  /** Returns a fresh empty ROWS×COLS grid. */
  _emptyGrid() {
    return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
  }

  /** Resets the board to all-empty. */
  reset() {
    this.grid = this._emptyGrid();
  }

  /**
   * Returns `true` if the given shape placed with its top-left at
   * (col, row) does not overlap walls, the floor, or locked cells.
   *
   * @param {number[][]} shape - 2-D bitmask
   * @param {number}     col   - left edge of bounding box
   * @param {number}     row   - top  edge of bounding box (may be negative)
   */
  isValid(shape, col, row) {
    for (let r = 0; r < shape.length; r++) {
      for (let c = 0; c < shape[r].length; c++) {
        if (!shape[r][c]) continue;
        const gc = col + c;
        const gr = row + r;
        if (gc < 0 || gc >= COLS)    return false; // wall collision
        if (gr >= ROWS)               return false; // floor collision
        if (gr >= 0 && this.grid[gr][gc]) return false; // cell collision
      }
    }
    return true;
  }

  /**
   * Stamps the piece's cells onto the grid using its colour.
   *
   * @param {Piece} piece
   * @returns {boolean} `true` if any cells were above row 0 (top-out).
   */
  lock(piece) {
    let topOut = false;
    for (let r = 0; r < piece.shape.length; r++) {
      for (let c = 0; c < piece.shape[r].length; c++) {
        if (!piece.shape[r][c]) continue;
        const gr = piece.row + r;
        const gc = piece.col + c;
        if (gr < 0) { topOut = true; continue; }
        this.grid[gr][gc] = piece.color;
      }
    }
    return topOut;
  }

  /**
   * Scans for and removes completed lines (all cells non-null).
   * Inserts empty rows at the top to replace cleared lines.
   *
   * @returns {number} Number of lines cleared.
   */
  clearLines() {
    let cleared = 0;
    for (let r = ROWS - 1; r >= 0; r--) {
      if (this.grid[r].every(cell => cell !== null)) {
        this.grid.splice(r, 1);                    // remove full row
        this.grid.unshift(Array(COLS).fill(null)); // add empty row at top
        cleared++;
        r++; // re-examine the same index (now contains the row that fell)
      }
    }
    return cleared;
  }
}

// ── SECTION 7 ── Piece ────────────────────────────────────────

/**
 * Represents the active falling tetromino.
 * Handles SRS rotation with wall kicks.
 */
class Piece {
  /** @param {string} type - Key into PIECES object. */
  constructor(type) {
    this.type       = type;
    this.color      = PIECES[type].color;
    this.stateIndex = 0;
    this.shape      = PIECES[type].states[0];

    // Spawn horizontally centred; I-piece starts one row higher so
    // the active row of its 4-wide bounding box appears at row 0.
    this.col = Math.floor((COLS - this.shape[0].length) / 2);
    this.row = (type === 'I') ? -1 : 0;
  }

  /**
   * Attempts to rotate the piece using SRS wall kicks.
   *
   * @param {number} dir  1 = clockwise,  -1 = counter-clockwise
   * @param {Board}  board
   * @returns {boolean} `true` if rotation succeeded.
   */
  rotate(dir, board) {
    const next      = (this.stateIndex + (dir === 1 ? 1 : 3)) % 4;
    const nextShape = PIECES[this.type].states[next];
    const key       = `${this.stateIndex}>${next}`;
    const kicks     = (this.type === 'I') ? KICKS_I : KICKS_JLSTZ;
    const table     = kicks[key] ?? [[0, 0]];

    for (const [dc, dr] of table) {
      if (board.isValid(nextShape, this.col + dc, this.row + dr)) {
        this.col        += dc;
        this.row        += dr;
        this.stateIndex  = next;
        this.shape       = nextShape;
        return true;
      }
    }
    return false; // all kick tests failed
  }

  /**
   * Computes the lowest row the piece can occupy (ghost piece row).
   *
   * @param {Board} board
   * @returns {number} Row of the ghost piece's bounding-box top edge.
   */
  ghostRow(board) {
    let gr = this.row;
    while (board.isValid(this.shape, this.col, gr + 1)) gr++;
    return gr;
  }
}

// ── SECTION 8 ── Renderer ─────────────────────────────────────

/**
 * All canvas drawing logic, fully separated from game state.
 * Draws: background grid, locked cells, ghost piece, active piece,
 *        and the next-piece preview.
 */
class Renderer {
  /**
   * @param {HTMLCanvasElement} canvas     - Main 10×20 board canvas
   * @param {HTMLCanvasElement} nextCanvas - 4×4 next-piece preview canvas
   */
  constructor(canvas, nextCanvas) {
    this.ctx     = canvas.getContext('2d');
    this.nextCtx = nextCanvas.getContext('2d');

    // Set canvas pixel dimensions
    canvas.width      = COLS * BLOCK;
    canvas.height     = ROWS * BLOCK;
    nextCanvas.width  = NB_GRID * NB;
    nextCanvas.height = NB_GRID * NB;
  }

  /**
   * Full redraw every frame.
   *
   * @param {Board}      board
   * @param {Piece|null} current - Active piece (null before game starts)
   * @param {Piece|null} next    - Next piece preview
   */
  draw(board, current, next) {
    this._drawBoard(board, current);
    this._drawNextPreview(next);
  }

  // ── Private drawing methods ───────────────────────────────────

  _drawBoard(board, current) {
    const { ctx } = this;
    const W = COLS * BLOCK;
    const H = ROWS * BLOCK;

    // ── Background
    ctx.fillStyle = '#080818';
    ctx.fillRect(0, 0, W, H);

    // ── Subtle grid lines
    ctx.strokeStyle = 'rgba(255,255,255,0.035)';
    ctx.lineWidth   = 0.5;
    for (let c = 0; c <= COLS; c++) {
      ctx.beginPath();
      ctx.moveTo(c * BLOCK, 0);
      ctx.lineTo(c * BLOCK, H);
      ctx.stroke();
    }
    for (let r = 0; r <= ROWS; r++) {
      ctx.beginPath();
      ctx.moveTo(0, r * BLOCK);
      ctx.lineTo(W, r * BLOCK);
      ctx.stroke();
    }

    // ── Locked cells
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        if (board.grid[r][c]) {
          this._drawBlock(ctx, c, r, board.grid[r][c], BLOCK);
        }
      }
    }

    // ── Ghost piece & active piece
    if (current) {
      const gr = current.ghostRow(board);
      this._drawShapeAt(ctx, current.shape, current.col, gr,    BLOCK, 'ghost');
      this._drawShapeAt(ctx, current.shape, current.col, current.row, BLOCK, current.color);
    }
  }

  _drawNextPreview(piece) {
    const { nextCtx: ctx } = this;
    const size = NB_GRID * NB;

    ctx.fillStyle = '#10102a';
    ctx.fillRect(0, 0, size, size);

    if (!piece) return;

    const { shape } = piece;

    // Find bounding box of non-empty cells to perfectly centre the piece
    let minR = shape.length, maxR = -1, minC = shape[0].length, maxC = -1;
    for (let r = 0; r < shape.length; r++) {
      for (let c = 0; c < shape[r].length; c++) {
        if (shape[r][c]) {
          if (r < minR) minR = r;
          if (r > maxR) maxR = r;
          if (c < minC) minC = c;
          if (c > maxC) maxC = c;
        }
      }
    }
    const pieceH = maxR - minR + 1;
    const pieceW = maxC - minC + 1;
    const offCol  = (NB_GRID - pieceW) / 2 - minC;
    const offRow  = (NB_GRID - pieceH) / 2 - minR;

    this._drawShapeAt(ctx, shape, offCol, offRow, NB, piece.color);
  }

  /**
   * Draws all filled cells of a shape at the given board offset.
   *
   * @param {CanvasRenderingContext2D} ctx
   * @param {number[][]} shape
   * @param {number}     col       - Bounding-box left in grid units (may be fractional)
   * @param {number}     row       - Bounding-box top  in grid units (may be fractional / negative)
   * @param {number}     blockSize - Pixel size of one cell
   * @param {string}     color     - CSS colour or 'ghost'
   */
  _drawShapeAt(ctx, shape, col, row, blockSize, color) {
    for (let r = 0; r < shape.length; r++) {
      for (let c = 0; c < shape[r].length; c++) {
        if (!shape[r][c]) continue;
        const gr = row + r;
        if (gr < 0) continue; // cell is above the visible board
        this._drawBlock(ctx, col + c, gr, color, blockSize);
      }
    }
  }

  /**
   * Draws a single cell at grid position (col, row) using a 3-D bevel style.
   *
   * @param {CanvasRenderingContext2D} ctx
   * @param {number} col
   * @param {number} row
   * @param {string} color - CSS colour string or 'ghost'
   * @param {number} size  - Cell size in px
   */
  _drawBlock(ctx, col, row, color, size) {
    const x   = col * size;
    const y   = row * size;
    const pad = 1; // gap between neighbouring blocks
    const bx  = x + pad;
    const by  = y + pad;
    const bw  = size - pad * 2;
    const bh  = size - pad * 2;

    if (color === 'ghost') {
      // Ghost: outlined semi-transparent block
      ctx.fillStyle   = 'rgba(255,255,255,0.08)';
      ctx.fillRect(bx, by, bw, bh);
      ctx.strokeStyle = 'rgba(255,255,255,0.22)';
      ctx.lineWidth   = 1;
      ctx.strokeRect(bx + 0.5, by + 0.5, bw - 1, bh - 1);
      return;
    }

    // ── Main fill with subtle vertical gradient
    const grad = ctx.createLinearGradient(bx, by, bx, by + bh);
    grad.addColorStop(0,   lighten(color, 0.25));
    grad.addColorStop(0.5, color);
    grad.addColorStop(1,   darken(color,  0.30));
    ctx.fillStyle = grad;
    ctx.fillRect(bx, by, bw, bh);

    // ── Top-left highlight (bevel)
    ctx.fillStyle = 'rgba(255,255,255,0.28)';
    ctx.fillRect(bx,          by,          bw,  3); // top edge
    ctx.fillRect(bx,          by,          3,  bh); // left edge

    // ── Bottom-right shadow (bevel)
    ctx.fillStyle = 'rgba(0,0,0,0.32)';
    ctx.fillRect(bx,          by + bh - 3, bw,  3); // bottom edge
    ctx.fillRect(bx + bw - 3, by,          3,  bh); // right edge
  }
}

// ── Colour helpers ────────────────────────────────────────────

/** Lightens a hex colour by mixing it toward white. */
function lighten(hex, amount) { return blendHex(hex, '#ffffff', amount); }

/** Darkens a hex colour by mixing it toward black. */
function darken(hex, amount)  { return blendHex(hex, '#000000', amount); }

/** Linear interpolation between two hex colours. */
function blendHex(hex1, hex2, t) {
  const parse = h => [
    parseInt(h.slice(1,3), 16),
    parseInt(h.slice(3,5), 16),
    parseInt(h.slice(5,7), 16),
  ];
  const [r1,g1,b1] = parse(hex1);
  const [r2,g2,b2] = parse(hex2);
  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);
  return `rgb(${r},${g},${b})`;
}

// ── SECTION 9 ── Game Controller ─────────────────────────────

/**
 * Master game controller.  Owns the RAF loop, input handling,
 * gravity, lock delay, DAS, scoring, and UI state.
 */
class Game {
  constructor() {
    // ── DOM references
    this.$score     = document.getElementById('score');
    this.$level     = document.getElementById('level');
    this.$lines     = document.getElementById('lines');
    this.$highScore = document.getElementById('high-score');
    this.$overlay   = document.getElementById('overlay');
    this.$ovTitle   = document.getElementById('overlay-title');
    this.$ovMsg     = document.getElementById('overlay-message');
    this.$ovBtn     = document.getElementById('overlay-btn');

    // ── Core objects
    this.board    = new Board();
    this.renderer = new Renderer(
      document.getElementById('game-canvas'),
      document.getElementById('next-canvas'),
    );
    this.bag   = new Bag();
    this.sound = new SoundEngine();

    // ── Game state  ('idle' | 'playing' | 'paused' | 'gameover')
    this.state     = 'idle';
    this.score     = 0;
    this.level     = 1;
    this.lines     = 0;
    this.highScore = parseInt(localStorage.getItem('tetrisHigh') || '0', 10);
    this.$highScore.textContent = this.highScore;

    // ── Active pieces
    this.current = null;
    this.next    = null;

    // ── Timing & physics
    this.lastTimestamp    = 0;
    this.gravityAccum     = 0;   // accumulated ms since last gravity tick
    this.lockTimer        = 0;   // accumulated ms while piece is on surface
    this.lockResetsLeft   = LOCK_RESET_MAX;
    this.isLocking        = false;

    // ── Delayed Auto Shift state for left & right
    this.das = {
      left:  { active: false, held: 0, repeating: false },
      right: { active: false, held: 0, repeating: false },
    };

    // ── Mobile HUD elements
    this.$mScore = document.getElementById('m-score');
    this.$mLevel = document.getElementById('m-level');
    this.$mLines = document.getElementById('m-lines');

    // ── Mobile next-piece preview renderer
    const mNextCanvas = document.getElementById('m-next-canvas');
    mNextCanvas.width  = NB_GRID * NB;
    mNextCanvas.height = NB_GRID * NB;
    this._mNextCtx = mNextCanvas.getContext('2d');

    // ── Mute button (desktop)
    this.$muteBtn = document.getElementById('mute-btn');
    this.$muteBtn.addEventListener('click', () => this._toggleMute());

    // ── Bind keyboard, overlay button, and touch controls
    document.addEventListener('keydown', e => this._onKeyDown(e));
    document.addEventListener('keyup',   e => this._onKeyUp(e));
    this.$ovBtn.addEventListener('click', () => this._overlayAction());
    this._initTouchControls();

    // Show start screen
    this._showOverlay('TETRIS', 'Press Enter or Space to Start', 'START GAME');
  }

  // ── PUBLIC: Start / Restart ───────────────────────────────────

  startGame() {
    this.board.reset();
    this.bag   = new Bag();
    this.score = 0;
    this.level = 1;
    this.lines = 0;
    this._updateHUD();

    // Pre-draw first next piece, then spawn current
    this.next    = this._drawFromBag();
    this.current = this._spawnFromNext();

    this.state          = 'playing';
    this.lastTimestamp  = performance.now();
    this.gravityAccum   = 0;
    this.isLocking      = false;
    this.lockTimer      = 0;

    this._hideOverlay();
    requestAnimationFrame(ts => this._loop(ts));
  }

  // ── PRIVATE: Game Loop ────────────────────────────────────────

  _loop(timestamp) {
    const dt = Math.min(timestamp - this.lastTimestamp, 100); // cap dt at 100ms
    this.lastTimestamp = timestamp;

    if (this.state === 'playing') {
      this._tickDAS(dt);
      this._tickGravity(dt);
      this._tickLock(dt);
    }

    // Always render (board visible behind pause / game-over overlays)
    this.renderer.draw(this.board, this.current, this.next);

    // Continue loop only while game is alive
    if (this.state !== 'gameover') {
      requestAnimationFrame(ts => this._loop(ts));
    }
  }

  // ── PRIVATE: Physics ticks ────────────────────────────────────

  /**
   * Applies gravity: drops the piece by one row each gravity interval.
   */
  _tickGravity(dt) {
    const interval = GRAVITY_MS[Math.min(this.level - 1, GRAVITY_MS.length - 1)];
    this.gravityAccum += dt;
    while (this.gravityAccum >= interval) {
      this.gravityAccum -= interval;
      this._dropOneRow(false); // gravity drop — no soft-drop points
    }
  }

  /**
   * Manages lock delay countdown once a piece has landed.
   */
  _tickLock(dt) {
    if (!this.isLocking) return;
    this.lockTimer += dt;
    if (this.lockTimer >= LOCK_DELAY_MS) {
      this._lockPiece();
    }
  }

  /**
   * Attempts to move the current piece down by one row.
   * Starts the lock-delay timer if it has landed.
   *
   * @param {boolean} scored - Awards 1 pt per row when true (soft drop).
   */
  _dropOneRow(scored) {
    if (this.board.isValid(this.current.shape, this.current.col, this.current.row + 1)) {
      this.current.row++;
      this.isLocking = false;
      this.lockTimer = 0;
      if (scored) { this._addScore(1); this.sound.softDrop(); }
    } else {
      // Piece has hit a surface — engage lock delay
      if (!this.isLocking) {
        this.isLocking      = true;
        this.lockTimer      = 0;
        this.lockResetsLeft = LOCK_RESET_MAX;
      }
    }
  }

  /**
   * Instantly drops the piece to the lowest valid row and locks it.
   * Awards 2 pts per row dropped.
   */
  _hardDrop() {
    let rows = 0;
    while (this.board.isValid(this.current.shape, this.current.col, this.current.row + 1)) {
      this.current.row++;
      rows++;
    }
    this._addScore(rows * 2);
    this.sound.hardDrop();
    this._lockPiece();
  }

  /**
   * Locks the current piece onto the board, clears lines, levels up,
   * and spawns the next piece.  Triggers game over if the board is topped out.
   */
  _lockPiece() {
    const topOut = this.board.lock(this.current);

    if (topOut) {
      this._triggerGameOver();
      return;
    }

    this.sound.lock(); // piece locked onto board

    const cleared = this.board.clearLines();
    if (cleared > 0) {
      this.sound.lineClear(cleared); // chime (overwrites lock sound intentionally)
      this._addScore(SCORE_TABLE[cleared] * this.level);
      this.lines += cleared;

      // Level up every LINES_PER_LEVEL cleared lines (max level 15)
      const newLevel = Math.min(Math.floor(this.lines / LINES_PER_LEVEL) + 1, 15);
      if (newLevel > this.level) {
        this.level = newLevel;
        this.sound.levelUp();
      }

      this._updateHUD();
    }

    // Reset lock/gravity state for next piece
    this.isLocking    = false;
    this.lockTimer    = 0;
    this.gravityAccum = 0;

    this.current = this._spawnFromNext();

    // Block-out check: spawn position itself is occupied
    if (!this.board.isValid(this.current.shape, this.current.col, this.current.row)) {
      this._triggerGameOver();
    }
  }

  // ── PRIVATE: Piece management ─────────────────────────────────

  /** Creates a new Piece object for the given type. */
  _drawFromBag() {
    return new Piece(this.bag.next());
  }

  /** Promotes `this.next` to `this.current` and draws a new next piece. */
  _spawnFromNext() {
    const spawned = this.next;
    this.next     = this._drawFromBag();
    return spawned;
  }

  // ── PRIVATE: Movement ─────────────────────────────────────────

  _moveLeft() {
    if (this.board.isValid(this.current.shape, this.current.col - 1, this.current.row)) {
      this.current.col--;
      this._resetLockOnMove();
      this.sound.move();
    }
  }

  _moveRight() {
    if (this.board.isValid(this.current.shape, this.current.col + 1, this.current.row)) {
      this.current.col++;
      this._resetLockOnMove();
      this.sound.move();
    }
  }

  _rotateCW()  { if (this.current.rotate( 1, this.board)) { this._resetLockOnMove(); this.sound.rotate(); } }
  _rotateCCW() { if (this.current.rotate(-1, this.board)) { this._resetLockOnMove(); this.sound.rotate(); } }

  /**
   * Resets the lock-delay timer on a successful move or rotate, up to
   * LOCK_RESET_MAX times — prevents infinite stalling on a surface.
   */
  _resetLockOnMove() {
    if (this.isLocking && this.lockResetsLeft > 0) {
      this.lockTimer = 0;
      this.lockResetsLeft--;
    }
  }

  // ── PRIVATE: DAS (Delayed Auto Shift) ─────────────────────────

  /**
   * Updates the DAS state for left/right, triggering auto-repeat moves
   * once DAS_DELAY elapses and then every DAS_RATE ms thereafter.
   */
  _tickDAS(dt) {
    for (const dir of ['left', 'right']) {
      const d = this.das[dir];
      if (!d.active) continue;

      d.held += dt;

      if (!d.repeating && d.held >= DAS_DELAY) {
        d.repeating = true;
        d.held      = 0;
      }

      if (d.repeating) {
        while (d.held >= DAS_RATE) {
          d.held -= DAS_RATE;
          if (dir === 'left') this._moveLeft();
          else                this._moveRight();
        }
      }
    }
  }

  // ── PRIVATE: Scoring & HUD ────────────────────────────────────

  _addScore(pts) {
    this.score += pts;
    this.$score.textContent = this.score;

    if (this.score > this.highScore) {
      this.highScore = this.score;
      localStorage.setItem('tetrisHigh', this.highScore);
      this.$highScore.textContent = this.highScore;
    }
  }

  _updateHUD() {
    this.$score.textContent  = this.score;
    this.$level.textContent  = this.level;
    this.$lines.textContent  = this.lines;
    // Mirror to mobile HUD
    this.$mScore.textContent = this.score;
    this.$mLevel.textContent = this.level;
    this.$mLines.textContent = this.lines;
  }

  /** Draws the next-piece preview on the mobile HUD canvas. */
  _drawMobileNext(piece) {
    const ctx  = this._mNextCtx;
    const size = NB_GRID * NB;
    ctx.fillStyle = '#10102a';
    ctx.fillRect(0, 0, size, size);
    if (!piece) return;
    // Reuse renderer's shape-drawing logic
    this.renderer._drawNextPreview.call({ nextCtx: ctx, renderer: this.renderer }, piece);
  }

  // ── PRIVATE: State transitions ────────────────────────────────

  _triggerGameOver() {
    this.state = 'gameover';
    this.sound.gameOver();
    this._showOverlay(
      'GAME OVER',
      `Score: ${this.score}\nLevel: ${this.level}\nLines: ${this.lines}`,
      'PLAY AGAIN',
    );
  }

  /** Toggles mute on/off and updates both desktop and mobile buttons. */
  _toggleMute() {
    this.sound.muted = !this.sound.muted;
    const on = !this.sound.muted;
    this.$muteBtn.textContent = on ? '🔊 SOUND ON' : '🔇 MUTED';
    this.$muteBtn.classList.toggle('muted', !on);
    const tcMute = document.getElementById('tc-mute');
    if (tcMute) tcMute.textContent = on ? '🔊' : '🔇';
  }

  _pause() {
    if (this.state !== 'playing') return;
    this.state = 'paused';
    this._showOverlay('PAUSED', 'Press P or click Resume\nto continue', 'RESUME');
  }

  _resume() {
    if (this.state !== 'paused') return;
    this.state         = 'playing';
    this.lastTimestamp = performance.now(); // prevent dt spike after pause
    this._hideOverlay();
  }

  /** Called by the overlay button and by Enter/Space when not playing. */
  _overlayAction() {
    if (this.state === 'idle' || this.state === 'gameover') this.startGame();
    else if (this.state === 'paused')                       this._resume();
  }

  // ── PRIVATE: Overlay helpers ──────────────────────────────────

  _showOverlay(title, msg, btnText) {
    this.$ovTitle.textContent = title;
    this.$ovMsg.textContent   = msg;
    this.$ovBtn.textContent   = btnText;
    this.$overlay.classList.remove('hidden');
  }

  _hideOverlay() {
    this.$overlay.classList.add('hidden');
  }

  // ── PRIVATE: Input handling ───────────────────────────────────

  // ── PRIVATE: Touch Controls ───────────────────────────────────

  /**
   * Wires up all on-screen touch buttons and canvas swipe gestures.
   * Auto-repeat (DAS) is implemented for left/right via setInterval.
   */
  _initTouchControls() {
    // Helper: bind touchstart + touchend safely (prevents ghost clicks)
    const onTouch = (id, startFn, endFn = null) => {
      const el = document.getElementById(id);
      if (!el) return;
      el.addEventListener('touchstart', e => { e.preventDefault(); startFn(); }, { passive: false });
      el.addEventListener('touchend',   e => { e.preventDefault(); if (endFn) endFn(); }, { passive: false });
      el.addEventListener('touchcancel',e => { if (endFn) endFn(); });
      // Also support mouse for testing on desktop
      el.addEventListener('mousedown', startFn);
      el.addEventListener('mouseup',   endFn || (() => {}));
    };

    // Hold-to-repeat helper (mirrors DAS behaviour)
    let _holdTimer    = null;
    let _holdInterval = null;
    const startHold = action => {
      if (this.state !== 'playing') return;
      action();
      _holdTimer = setTimeout(() => {
        _holdInterval = setInterval(() => {
          if (this.state === 'playing') action();
        }, DAS_RATE);
      }, DAS_DELAY);
    };
    const stopHold = () => {
      clearTimeout(_holdTimer);
      clearInterval(_holdInterval);
    };

    // ── Left / Right (with auto-repeat)
    onTouch('tc-left',
      () => startHold(() => this._moveLeft()),
      () => stopHold(),
    );
    onTouch('tc-right',
      () => startHold(() => this._moveRight()),
      () => stopHold(),
    );

    // ── Soft drop (with auto-repeat)
    onTouch('tc-down',
      () => startHold(() => { if (this.state === 'playing') { this._dropOneRow(true); this.gravityAccum = 0; } }),
      () => stopHold(),
    );

    // ── Rotate CW / CCW
    onTouch('tc-cw',  () => { if (this.state === 'playing') this._rotateCW(); });
    onTouch('tc-ccw', () => { if (this.state === 'playing') this._rotateCCW(); });

    // ── Hard drop
    onTouch('tc-drop', () => { if (this.state === 'playing') this._hardDrop(); });

    // ── Pause
    onTouch('tc-pause', () => {
      if      (this.state === 'playing') this._pause();
      else if (this.state === 'paused')  this._resume();
      else                               this._overlayAction();
    });

    // ── Mute (mobile)
    const tcMute = document.getElementById('tc-mute');
    if (tcMute) {
      tcMute.addEventListener('touchstart', e => {
        e.preventDefault();
        this._toggleMute();
        tcMute.textContent = this.sound.muted ? '🔇' : '🔊';
      }, { passive: false });
    }

    // ── Swipe gestures on the canvas
    const canvas = document.getElementById('game-canvas');
    let swipeX = 0, swipeY = 0, swipeTime = 0;

    canvas.addEventListener('touchstart', e => {
      e.preventDefault();
      swipeX    = e.touches[0].clientX;
      swipeY    = e.touches[0].clientY;
      swipeTime = Date.now();
    }, { passive: false });

    canvas.addEventListener('touchend', e => {
      e.preventDefault();
      if (this.state !== 'playing') { this._overlayAction(); return; }

      const dx   = e.changedTouches[0].clientX - swipeX;
      const dy   = e.changedTouches[0].clientY - swipeY;
      const dt   = Date.now() - swipeTime;
      const dist = Math.sqrt(dx * dx + dy * dy);

      // Tap (small movement, quick) → rotate CW
      if (dist < 20 && dt < 300) {
        this._rotateCW();
        return;
      }

      // Swipe: determine dominant direction
      if (Math.abs(dx) > Math.abs(dy)) {
        // Horizontal swipe
        if (dx > 25)       this._moveRight();
        else if (dx < -25) this._moveLeft();
      } else {
        // Vertical swipe
        if (dy > 25)       this._dropOneRow(true);   // swipe down = soft drop
        else if (dy < -50) this._hardDrop();          // swipe up   = hard drop
      }
    }, { passive: false });
  }

  _onKeyDown(e) {
    // ── Global keys (work in any state) ──────────────────────────

    if (e.key === 'm' || e.key === 'M') {
      this._toggleMute();
      return;
    }

    if (e.key === 'p' || e.key === 'P') {
      if      (this.state === 'playing') this._pause();
      else if (this.state === 'paused')  this._resume();
      return;
    }

    // Enter or Space activates the overlay button when not in play
    if ((e.key === 'Enter' || e.key === ' ') && this.state !== 'playing') {
      e.preventDefault();
      this._overlayAction();
      return;
    }

    // All remaining keys only apply during active play
    if (this.state !== 'playing') return;

    switch (e.key) {
      case 'ArrowLeft':
        e.preventDefault();
        // Trigger one immediate move, then let DAS handle the rest
        if (!this.das.left.active) {
          this.das.left = { active: true, held: 0, repeating: false };
          this._moveLeft();
        }
        break;

      case 'ArrowRight':
        e.preventDefault();
        if (!this.das.right.active) {
          this.das.right = { active: true, held: 0, repeating: false };
          this._moveRight();
        }
        break;

      case 'ArrowDown':
        e.preventDefault();
        this._dropOneRow(true);     // soft drop (scored)
        this.gravityAccum = 0;      // reset gravity so it doesn't double-drop
        break;

      case 'ArrowUp':
      case 'x':
      case 'X':
        e.preventDefault();
        this._rotateCW();
        break;

      case 'z':
      case 'Z':
        e.preventDefault();
        this._rotateCCW();
        break;

      case ' ':
        e.preventDefault();
        this._hardDrop();
        break;
    }
  }

  _onKeyUp(e) {
    if (e.key === 'ArrowLeft')  this.das.left  = { active: false, held: 0, repeating: false };
    if (e.key === 'ArrowRight') this.das.right = { active: false, held: 0, repeating: false };
  }
}

// ── SECTION 9 ── Bootstrap ────────────────────────────────────

document.addEventListener('DOMContentLoaded', () => {
  // Expose globally for debugging convenience
  window.game = new Game();
});
