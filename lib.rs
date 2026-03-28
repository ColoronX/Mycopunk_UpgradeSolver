#![no_std]

// ── Constants ──────────────────────────────────────────────────────────────
const MAX_SHAPES: usize = 32;
const MAX_PLACEMENTS: usize = 1024;
const MAX_CELLS: usize = 128;
const MAX_SOLUTIONS: usize = 50;

// ── Shared buffer (JS reads/writes here) ──────────────────────────────────
static mut DATA_BUFFER: [u8; 65536] = [0; 65536];

// ── Global solver state (avoids large stack allocations) ──────────────────
static mut G_NEIGHBOR:   [u128; MAX_CELLS]                        = [0; MAX_CELLS];
static mut G_P_MASK:     [[u128; MAX_PLACEMENTS]; MAX_SHAPES]     = [[0; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_P_ADJ:      [[u128; MAX_PLACEMENTS]; MAX_SHAPES]     = [[0; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_P_COUNT:    [usize; MAX_SHAPES]                      = [0; MAX_SHAPES];
static mut G_SIZE:       [u32;   MAX_SHAPES]                      = [0; MAX_SHAPES];
static mut G_PRISM:      [bool;  MAX_SHAPES]                      = [false; MAX_SHAPES];
static mut G_ADJ_TO:     [i32;   MAX_SHAPES]                      = [0; MAX_SHAPES];
static mut G_SOLUTIONS:  [[u128; MAX_SHAPES]; MAX_SOLUTIONS]      = [[0; MAX_SHAPES]; MAX_SOLUTIONS];
static mut G_CURRENT:    [u128;  MAX_SHAPES]                      = [0; MAX_SHAPES];
static mut G_SOL_COUNT:  usize                                    = 0;
static mut G_MAX_SOLS:   usize                                    = 0;
static mut G_SHAPE_COUNT: usize                                   = 0;
static mut G_TOTAL_CELLS: i32                                     = 0;
// scratch space for placement dedup (avoids 16KB on stack)
static mut G_SEEN:       [u128; MAX_PLACEMENTS]                   = [0; MAX_PLACEMENTS];

// ── Coordinate helpers ─────────────────────────────────────────────────────
#[derive(Clone, Copy)]
struct Axial { q: i32, r: i32 }

fn oddq_to_axial(col: i32, row: i32) -> Axial {
    Axial { q: col, r: row - (col + (col & 1)) / 2 }
}

fn axial_to_oddq(a: Axial) -> (i32, i32) {
    (a.q, a.r + (a.q + (a.q & 1)) / 2)
}

fn rotate_axial(a: Axial) -> Axial {
    Axial { q: -a.r, r: a.q + a.r }
}

// ── Bit helpers ────────────────────────────────────────────────────────────
fn count_bits(mut n: u128) -> u32 {
    let mut c = 0u32;
    while n > 0 { n &= n - 1; c += 1; }
    c
}

fn full_mask() -> u128 {
    let tc = unsafe { G_TOTAL_CELLS };
    if tc >= 128 { u128::MAX } else { (1u128 << tc) - 1 }
}

unsafe fn neighbor_of_mask(mut m: u128) -> u128 {
    let mut res = 0u128;
    while m > 0 {
        let lsb = m & m.wrapping_neg();
        let idx = lsb.trailing_zeros() as usize;
        if idx < MAX_CELLS { res |= G_NEIGHBOR[idx]; }
        m ^= lsb;
    }
    res
}

unsafe fn get_island(occupied: u128, start_bit: usize) -> u128 {
    let fm   = full_mask();
    let empty = fm & !occupied;
    let mut island = 1u128 << start_bit;
    let mut last   = 0u128;
    while island != last {
        last = island;
        let mut spread = island;
        let mut temp   = island;
        while temp > 0 {
            let lsb = temp & temp.wrapping_neg();
            let idx = lsb.trailing_zeros() as usize;
            if idx < MAX_CELLS { spread |= G_NEIGHBOR[idx]; }
            temp ^= lsb;
        }
        island = spread & empty;
    }
    island
}

// ── Recursive solver (MRV + area pruning + island pruning) ────────────────
//
// rem[0..rem_count) holds the indices of shapes not yet placed.
// We pick the shape with the fewest valid (non-overlapping) placements (MRV),
// swap it to the end, recurse, then restore.
unsafe fn solve(rem: &mut [u8; MAX_SHAPES], rem_count: usize, occupied: u128, prism_adj: u128) {
    if G_SOL_COUNT >= G_MAX_SOLS { return; }

    if rem_count == 0 {
        G_SOLUTIONS[G_SOL_COUNT] = G_CURRENT;
        G_SOL_COUNT += 1;
        return;
    }

    let fm    = full_mask();
    let avail = count_bits(fm & !occupied);

    // ── Area pruning ──────────────────────────────────────────────────────
    let mut req = 0u32;
    for i in 0..rem_count { req += G_SIZE[rem[i] as usize]; }
    if avail < req { return; }

    // ── Island pruning ────────────────────────────────────────────────────
    let mut min_size = u32::MAX;
    for i in 0..rem_count {
        let s = G_SIZE[rem[i] as usize];
        if s < min_size { min_size = s; }
    }
    let mut unvisited = fm & !occupied;
    while unvisited > 0 {
        let start = unvisited.trailing_zeros() as usize;
        let island = get_island(occupied, start);
        if count_bits(island) < min_size { return; }
        unvisited ^= island;
    }

    // ── MRV: pick shape with fewest valid placements ──────────────────────
    let mut best_i     = 0usize;
    let mut best_count = u32::MAX;
    for i in 0..rem_count {
        let sid = rem[i] as usize;
        let mut valid = 0u32;
        for j in 0..G_P_COUNT[sid] {
            if G_P_MASK[sid][j] & occupied == 0 { valid += 1; }
        }
        if valid == 0 { return; }
        if valid < best_count {
            best_count = valid;
            best_i = i;
            if valid == 1 { break; }
        }
    }

    // Remove chosen shape from remaining (swap-with-last trick)
    let shape_idx      = rem[best_i] as usize;
    rem[best_i]        = rem[rem_count - 1];

    let pc      = G_P_COUNT[shape_idx];
    let prism   = G_PRISM[shape_idx];
    let adj_to  = G_ADJ_TO[shape_idx];

    for i in 0..pc {
        let mask = G_P_MASK[shape_idx][i];
        let adj  = G_P_ADJ[shape_idx][i];

        if mask & occupied != 0 { continue; }

        // Adjacency constraint
        if adj_to >= 0 {
            let target = G_CURRENT[adj_to as usize];
            if target != 0 && mask & neighbor_of_mask(target) == 0 { continue; }
        }

        // Prism constraint
        if prism && prism_adj != 0 && mask & prism_adj == 0 { continue; }

        G_CURRENT[shape_idx] = mask;
        let next_prism = if prism { prism_adj | adj } else { prism_adj };
        solve(rem, rem_count - 1, occupied | mask, next_prism);
        if G_SOL_COUNT >= G_MAX_SOLS {
            rem[best_i] = shape_idx as u8;
            return;
        }
    }

    // Restore remaining
    rem[best_i] = shape_idx as u8;
}

// ── Public WASM exports ───────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn get_buffer_ptr() -> *const u8 {
    unsafe { DATA_BUFFER.as_ptr() }
}

/// Returns 1 if this grid size is supported (fits in u128), 0 otherwise.
#[no_mangle]
pub extern "C" fn check_supported(w: i32, h: i32) -> i32 {
    if w * h <= 127 { 1 } else { 0 }
}

/// Main entry point called from JavaScript.
///
/// Buffer input layout (written by JS before this call):
///   For each shape:
///     [+0]  prism    : u8  (0 or 1)
///     [+1]  adj_to   : u8  (0xFF = none, else shape index 0-31)
///     [+2]  no_edge  : u8  (0 or 1)
///     [+3]  n_cells  : u8
///     [+4…] (col, row) pairs as u8 each
///
/// Buffer output layout (written by Rust, starting at offset 0):
///   [0]       n_solutions : u8
///   For each solution, for each shape (in original index order):
///     mask_low  : u64 little-endian (8 bytes)
///     mask_high : u64 little-endian (8 bytes)
#[no_mangle]
pub unsafe extern "C" fn run_solver(
    w: i32, h: i32,
    shape_count: i32,
    max_sols: i32,
    disable_rotation: i32,
) -> i32 {
    G_TOTAL_CELLS  = w * h;
    G_SHAPE_COUNT  = shape_count as usize;
    G_MAX_SOLS     = max_sols as usize;
    G_SOL_COUNT    = 0;
    G_CURRENT      = [0u128; MAX_SHAPES];

    // ── Precompute hex neighbour lookup ───────────────────────────────────
    for i in 0..(G_TOTAL_CELLS as usize) {
        let x = (i as i32) % w;
        let y = (i as i32) / w;
        let offsets: [(i32, i32); 6] = if x % 2 == 0 {
            [(0,-1),(1,-1),(1,0),(0,1),(-1,0),(-1,-1)]
        } else {
            [(0,-1),(1,0),(1,1),(0,1),(-1,1),(-1,0)]
        };
        let mut m = 0u128;
        for (dx, dy) in offsets {
            let nx = x + dx; let ny = y + dy;
            if nx >= 0 && nx < w && ny >= 0 && ny < h {
                m |= 1u128 << (ny * w + nx);
            }
        }
        if i < MAX_CELLS { G_NEIGHBOR[i] = m; }
    }

    // Forbidden mask: right column (x == W-1) and top row (y == 0)
    let forbidden: u128 = {
        let mut m = 0u128;
        for i in 0..G_TOTAL_CELLS {
            if i % w == w - 1 || i / w == 0 { m |= 1u128 << i; }
        }
        m
    };

    // ── Read shapes and generate placements ───────────────────────────────
    let mut buf_off = 0usize;

    // We'll use a fixed-size local array for base cells (stack-safe: 32 * 8 = 256 bytes)
    let mut base: [Axial; 32] = [Axial { q: 0, r: 0 }; 32];
    let mut cur:  [Axial; 32] = [Axial { q: 0, r: 0 }; 32];

    for s_idx in 0..G_SHAPE_COUNT {
        let prism      = DATA_BUFFER[buf_off] == 1;           buf_off += 1;
        let adj_to_raw = DATA_BUFFER[buf_off] as i8 as i32;  buf_off += 1;
        let no_edge    = DATA_BUFFER[buf_off] == 1;           buf_off += 1;
        let n_cells    = DATA_BUFFER[buf_off] as usize;       buf_off += 1;

        for c in 0..n_cells {
            let col = DATA_BUFFER[buf_off] as i32; buf_off += 1;
            let row = DATA_BUFFER[buf_off] as i32; buf_off += 1;
            base[c] = oddq_to_axial(col, row);
        }

        G_PRISM[s_idx]  = prism;
        G_ADJ_TO[s_idx] = adj_to_raw;
        G_SIZE[s_idx]   = n_cells as u32;

        // Copy base to cur for rotation
        for c in 0..n_cells { cur[c] = base[c]; }

        let mut p_idx      = 0usize;
        let mut seen_count = 0usize;
        let rotations      = if disable_rotation != 0 { 1 } else { 6 };

        for _rot in 0..rotations {
            for py in 0..h {
                for px in 0..w {
                    let tgt = oddq_to_axial(px, py);
                    let src = cur[0];
                    let dq  = tgt.q - src.q;
                    let dr  = tgt.r - src.r;

                    let mut mask = 0u128;
                    let mut ok   = true;
                    for c in 0..n_cells {
                        let (cx, cy) = axial_to_oddq(Axial { q: cur[c].q + dq, r: cur[c].r + dr });
                        if cx >= 0 && cx < w && cy >= 0 && cy < h {
                            mask |= 1u128 << (cy * w + cx);
                        } else { ok = false; break; }
                    }

                    if ok && (!no_edge || mask & forbidden == 0) {
                        // Dedup by mask
                        let mut dup = false;
                        for k in 0..seen_count {
                            if G_SEEN[k] == mask { dup = true; break; }
                        }
                        if !dup && p_idx < MAX_PLACEMENTS {
                            G_SEEN[seen_count] = mask;
                            seen_count += 1;
                            G_P_MASK[s_idx][p_idx] = mask;
                            G_P_ADJ[s_idx][p_idx]  = neighbor_of_mask(mask);
                            p_idx += 1;
                        }
                    }
                }
            }
            // Rotate for next iteration
            for c in 0..n_cells { cur[c] = rotate_axial(cur[c]); }
        }
        G_P_COUNT[s_idx] = p_idx;
    }

    // ── Run backtracking solver ───────────────────────────────────────────
    let mut rem = [0u8; MAX_SHAPES];
    for i in 0..G_SHAPE_COUNT { rem[i] = i as u8; }
    solve(&mut rem, G_SHAPE_COUNT, 0, 0);

    // ── Write solutions to buffer (overwrites input — that's intentional) ─
    let mut out = 0usize;
    DATA_BUFFER[out] = G_SOL_COUNT as u8; out += 1;

    for s in 0..G_SOL_COUNT {
        for m in 0..G_SHAPE_COUNT {
            let val  = G_SOLUTIONS[s][m];
            let low  = val as u64;
            let high = (val >> 64) as u64;
            core::ptr::copy_nonoverlapping(
                &low  as *const u64 as *const u8,
                DATA_BUFFER.as_mut_ptr().add(out),     8,
            );
            core::ptr::copy_nonoverlapping(
                &high as *const u64 as *const u8,
                DATA_BUFFER.as_mut_ptr().add(out + 8), 8,
            );
            out += 16;
        }
    }

    G_SOL_COUNT as i32
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
