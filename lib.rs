#![no_std]

const MAX_SHAPES: usize = 32;
const MAX_PLACEMENTS: usize = 1024;
const MAX_CELLS: usize = 256;
const MAX_SOLUTIONS: usize = 50;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Mask256 {
    lo: u128,
    hi: u128,
}

impl Mask256 {
    const ZERO: Self = Self { lo: 0, hi: 0 };
    const FULL: Self = Self { lo: u128::MAX, hi: u128::MAX };

    #[inline(always)]
    fn from_bit(index: usize) -> Self {
        if index < 128 {
            Self {
                lo: 1u128 << index,
                hi: 0,
            }
        } else {
            Self {
                lo: 0,
                hi: 1u128 << (index - 128),
            }
        }
    }

    #[inline(always)]
    fn is_zero(self) -> bool {
        self.lo == 0 && self.hi == 0
    }

    #[inline(always)]
    fn and(self, other: Self) -> Self {
        Self {
            lo: self.lo & other.lo,
            hi: self.hi & other.hi,
        }
    }

    #[inline(always)]
    fn or(self, other: Self) -> Self {
        Self {
            lo: self.lo | other.lo,
            hi: self.hi | other.hi,
        }
    }

    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        Self {
            lo: self.lo ^ other.lo,
            hi: self.hi ^ other.hi,
        }
    }

    #[inline(always)]
    fn without(self, other: Self) -> Self {
        Self {
            lo: self.lo & !other.lo,
            hi: self.hi & !other.hi,
        }
    }

    #[inline(always)]
    fn intersects(self, other: Self) -> bool {
        (self.lo & other.lo) != 0 || (self.hi & other.hi) != 0
    }

    #[inline(always)]
    fn count_bits(self) -> u32 {
        self.lo.count_ones() + self.hi.count_ones()
    }

    #[inline(always)]
    fn trailing_index(self) -> usize {
        if self.lo != 0 {
            self.lo.trailing_zeros() as usize
        } else {
            128 + self.hi.trailing_zeros() as usize
        }
    }

    #[inline(always)]
    fn clear_lsb(self) -> Self {
        if self.lo != 0 {
            Self {
                lo: self.lo & (self.lo - 1),
                hi: self.hi,
            }
        } else {
            Self {
                lo: 0,
                hi: self.hi & (self.hi - 1),
            }
        }
    }

    #[inline(always)]
    fn with_bit(self, index: usize) -> Self {
        self.or(Self::from_bit(index))
    }
}

// Shared buffer (JS reads/writes here)
static mut DATA_BUFFER: [u8; 65536] = [0; 65536];

// Global solver state (avoids large stack allocations)
static mut G_NEIGHBOR: [Mask256; MAX_CELLS] = [Mask256::ZERO; MAX_CELLS];
static mut G_P_MASK: [[Mask256; MAX_PLACEMENTS]; MAX_SHAPES] =
    [[Mask256::ZERO; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_P_ADJ: [[Mask256; MAX_PLACEMENTS]; MAX_SHAPES] =
    [[Mask256::ZERO; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_P_COUNT: [usize; MAX_SHAPES] = [0; MAX_SHAPES];
static mut G_SIZE: [u32; MAX_SHAPES] = [0; MAX_SHAPES];
static mut G_PRISM: [bool; MAX_SHAPES] = [false; MAX_SHAPES];
static mut G_ADJ_TO: [i32; MAX_SHAPES] = [0; MAX_SHAPES];
static mut G_SOLUTIONS: [[Mask256; MAX_SHAPES]; MAX_SOLUTIONS] =
    [[Mask256::ZERO; MAX_SHAPES]; MAX_SOLUTIONS];
static mut G_CURRENT: [Mask256; MAX_SHAPES] = [Mask256::ZERO; MAX_SHAPES];
static mut G_CURRENT_ADJ: [Mask256; MAX_SHAPES] = [Mask256::ZERO; MAX_SHAPES];
static mut G_SOL_COUNT: usize = 0;
static mut G_MAX_SOLS: usize = 0;
static mut G_SHAPE_COUNT: usize = 0;
static mut G_TOTAL_CELLS: i32 = 0;
static mut G_SEEN: [Mask256; MAX_PLACEMENTS] = [Mask256::ZERO; MAX_PLACEMENTS];
static mut G_NEIGHBOR128: [u128; 128] = [0; 128];
static mut G_P_MASK128: [[u128; MAX_PLACEMENTS]; MAX_SHAPES] = [[0; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_P_ADJ128: [[u128; MAX_PLACEMENTS]; MAX_SHAPES] = [[0; MAX_PLACEMENTS]; MAX_SHAPES];
static mut G_SOLUTIONS128: [[u128; MAX_SHAPES]; MAX_SOLUTIONS] = [[0; MAX_SHAPES]; MAX_SOLUTIONS];
static mut G_CURRENT128: [u128; MAX_SHAPES] = [0; MAX_SHAPES];
static mut G_CURRENT_ADJ128: [u128; MAX_SHAPES] = [0; MAX_SHAPES];
static mut G_SEEN128: [u128; MAX_PLACEMENTS] = [0; MAX_PLACEMENTS];

#[derive(Clone, Copy)]
struct Axial {
    q: i32,
    r: i32,
}

fn oddq_to_axial(col: i32, row: i32) -> Axial {
    Axial {
        q: col,
        r: row - (col + (col & 1)) / 2,
    }
}

fn axial_to_oddq(a: Axial) -> (i32, i32) {
    (a.q, a.r + (a.q + (a.q & 1)) / 2)
}

fn rotate_axial(a: Axial) -> Axial {
    Axial {
        q: -a.r,
        r: a.q + a.r,
    }
}

fn full_mask() -> Mask256 {
    let tc = unsafe { G_TOTAL_CELLS as usize };
    if tc == 0 {
        Mask256::ZERO
    } else if tc < 128 {
        Mask256 {
            lo: (1u128 << tc) - 1,
            hi: 0,
        }
    } else if tc == 128 {
        Mask256 {
            lo: u128::MAX,
            hi: 0,
        }
    } else if tc < 256 {
        Mask256 {
            lo: u128::MAX,
            hi: (1u128 << (tc - 128)) - 1,
        }
    } else {
        Mask256::FULL
    }
}

unsafe fn neighbor_of_mask(mut m: Mask256) -> Mask256 {
    let mut res = Mask256::ZERO;
    while !m.is_zero() {
        let idx = m.trailing_index();
        if idx < MAX_CELLS {
            res = res.or(G_NEIGHBOR[idx]);
        }
        m = m.clear_lsb();
    }
    res
}

unsafe fn get_island(occupied: Mask256, start_bit: usize) -> Mask256 {
    let fm = full_mask();
    let empty = fm.without(occupied);
    let mut island = Mask256::from_bit(start_bit);
    let mut last = Mask256::ZERO;
    while island != last {
        last = island;
        let mut spread = island;
        let mut temp = island;
        while !temp.is_zero() {
            let idx = temp.trailing_index();
            if idx < MAX_CELLS {
                spread = spread.or(G_NEIGHBOR[idx]);
            }
            temp = temp.clear_lsb();
        }
        island = spread.and(empty);
    }
    island
}

#[inline(always)]
fn count_bits128(n: u128) -> u32 {
    n.count_ones()
}

fn full_mask128() -> u128 {
    let tc = unsafe { G_TOTAL_CELLS };
    if tc >= 128 {
        u128::MAX
    } else {
        (1u128 << tc) - 1
    }
}

unsafe fn neighbor_of_mask128(mut m: u128) -> u128 {
    let mut res = 0u128;
    while m > 0 {
        let lsb = m & m.wrapping_neg();
        let idx = lsb.trailing_zeros() as usize;
        res |= G_NEIGHBOR128[idx];
        m ^= lsb;
    }
    res
}

unsafe fn get_island128(occupied: u128, start_bit: usize) -> u128 {
    let fm = full_mask128();
    let empty = fm & !occupied;
    let mut island = 1u128 << start_bit;
    let mut last = 0u128;
    while island != last {
        last = island;
        let mut spread = island;
        let mut temp = island;
        while temp > 0 {
            let lsb = temp & temp.wrapping_neg();
            let idx = lsb.trailing_zeros() as usize;
            spread |= G_NEIGHBOR128[idx];
            temp ^= lsb;
        }
        island = spread & empty;
    }
    island
}

unsafe fn solve128(rem: &mut [u8; MAX_SHAPES], rem_count: usize, occupied: u128, prism_adj: u128) {
    if G_SOL_COUNT >= G_MAX_SOLS {
        return;
    }

    if rem_count == 0 {
        G_SOLUTIONS128[G_SOL_COUNT] = G_CURRENT128;
        G_SOL_COUNT += 1;
        return;
    }

    let fm = full_mask128();
    let avail = count_bits128(fm & !occupied);

    let mut req = 0u32;
    for i in 0..rem_count {
        req += G_SIZE[rem[i] as usize];
    }
    if avail < req {
        return;
    }

    let mut min_size = u32::MAX;
    for i in 0..rem_count {
        let s = G_SIZE[rem[i] as usize];
        if s < min_size {
            min_size = s;
        }
    }

    if min_size > 1 {
        let mut unvisited = fm & !occupied;
        while unvisited > 0 {
            let start = unvisited.trailing_zeros() as usize;
            let island = get_island128(occupied, start);
            if count_bits128(island) < min_size {
                return;
            }
            unvisited ^= island;
        }
    }

    if avail == req {
        // When the remaining pieces must fill all remaining cells, branch on
        // one uncovered cell and only consider placements that cover it.
        let anchor = 1u128 << ((fm & !occupied).trailing_zeros() as usize);
        let mut found = false;

        for i in 0..rem_count {
            let shape_idx = rem[i] as usize;
            let pc = G_P_COUNT[shape_idx];
            let prism = G_PRISM[shape_idx];
            let adj_to = G_ADJ_TO[shape_idx];
            let mut target_adj = 0u128;
            if adj_to >= 0 {
                let target = adj_to as usize;
                if G_CURRENT128[target] != 0 {
                    target_adj = G_CURRENT_ADJ128[target];
                }
            }

            rem[i] = rem[rem_count - 1];

            for j in 0..pc {
                let mask = G_P_MASK128[shape_idx][j];
                if mask & anchor == 0 {
                    continue;
                }
                if mask & occupied != 0 {
                    continue;
                }
                if target_adj != 0 && mask & target_adj == 0 {
                    continue;
                }
                if prism && prism_adj != 0 && mask & prism_adj == 0 {
                    continue;
                }

                found = true;
                let adj = G_P_ADJ128[shape_idx][j];
                G_CURRENT128[shape_idx] = mask;
                G_CURRENT_ADJ128[shape_idx] = adj;
                let next_prism = if prism { prism_adj | adj } else { prism_adj };
                solve128(rem, rem_count - 1, occupied | mask, next_prism);
                G_CURRENT128[shape_idx] = 0;
                G_CURRENT_ADJ128[shape_idx] = 0;

                if G_SOL_COUNT >= G_MAX_SOLS {
                    rem[i] = shape_idx as u8;
                    return;
                }
            }

            rem[i] = shape_idx as u8;
        }

        if !found {
            return;
        }
        return;
    }

    let mut best_i = 0usize;
    let mut best_count = u32::MAX;
    for i in 0..rem_count {
        let sid = rem[i] as usize;
        let mut valid = 0u32;
        for j in 0..G_P_COUNT[sid] {
            let mask = G_P_MASK128[sid][j];
            if mask & occupied == 0 {
                valid += 1;
            }
        }

        if valid == 0 {
            return;
        }
        if valid < best_count {
            best_count = valid;
            best_i = i;
            if valid == 1 {
                break;
            }
        }
    }

    let shape_idx = rem[best_i] as usize;
    rem[best_i] = rem[rem_count - 1];

    let pc = G_P_COUNT[shape_idx];
    let prism = G_PRISM[shape_idx];
    let adj_to = G_ADJ_TO[shape_idx];
    let mut target_adj = 0u128;
    if adj_to >= 0 {
        let target = adj_to as usize;
        if G_CURRENT128[target] != 0 {
            target_adj = G_CURRENT_ADJ128[target];
        }
    }

    for i in 0..pc {
        let mask = G_P_MASK128[shape_idx][i];
        if mask & occupied != 0 {
            continue;
        }
        if target_adj != 0 && mask & target_adj == 0 {
            continue;
        }
        if prism && prism_adj != 0 && mask & prism_adj == 0 {
            continue;
        }

        let adj = G_P_ADJ128[shape_idx][i];
        G_CURRENT128[shape_idx] = mask;
        G_CURRENT_ADJ128[shape_idx] = adj;
        let next_prism = if prism { prism_adj | adj } else { prism_adj };
        solve128(rem, rem_count - 1, occupied | mask, next_prism);
        G_CURRENT128[shape_idx] = 0;
        G_CURRENT_ADJ128[shape_idx] = 0;

        if G_SOL_COUNT >= G_MAX_SOLS {
            rem[best_i] = shape_idx as u8;
            return;
        }
    }

    rem[best_i] = shape_idx as u8;
}

unsafe fn solve(rem: &mut [u8; MAX_SHAPES], rem_count: usize, occupied: Mask256, prism_adj: Mask256) {
    if G_SOL_COUNT >= G_MAX_SOLS {
        return;
    }

    if rem_count == 0 {
        G_SOLUTIONS[G_SOL_COUNT] = G_CURRENT;
        G_SOL_COUNT += 1;
        return;
    }

    let fm = full_mask();
    let avail = fm.without(occupied).count_bits();

    // Area pruning.
    let mut req = 0u32;
    for i in 0..rem_count {
        req += G_SIZE[rem[i] as usize];
    }
    if avail < req {
        return;
    }

    // Island pruning. Skip when a single-cell shape remains (it can fit any island >= 1).
    let mut min_size = u32::MAX;
    for i in 0..rem_count {
        let s = G_SIZE[rem[i] as usize];
        if s < min_size {
            min_size = s;
        }
    }

    if min_size > 1 {
        let mut unvisited = fm.without(occupied);
        while !unvisited.is_zero() {
            let start = unvisited.trailing_index();
            let island = get_island(occupied, start);
            if island.count_bits() < min_size {
                return;
            }
            unvisited = unvisited.xor(island);
        }
    }

    if avail == req {
        // Exact-cover style branching for dense states.
        let anchor_idx = fm.without(occupied).trailing_index();
        let anchor = Mask256::from_bit(anchor_idx);
        let mut found = false;

        for i in 0..rem_count {
            let shape_idx = rem[i] as usize;
            let pc = G_P_COUNT[shape_idx];
            let prism = G_PRISM[shape_idx];
            let adj_to = G_ADJ_TO[shape_idx];
            let mut target_adj = Mask256::ZERO;
            if adj_to >= 0 {
                let target = adj_to as usize;
                if !G_CURRENT[target].is_zero() {
                    target_adj = G_CURRENT_ADJ[target];
                }
            }

            rem[i] = rem[rem_count - 1];

            for j in 0..pc {
                let mask = G_P_MASK[shape_idx][j];
                if !mask.intersects(anchor) {
                    continue;
                }
                if mask.intersects(occupied) {
                    continue;
                }
                if !target_adj.is_zero() && !mask.intersects(target_adj) {
                    continue;
                }
                if !prism_adj.is_zero() && prism && !mask.intersects(prism_adj) {
                    continue;
                }

                found = true;
                let adj = G_P_ADJ[shape_idx][j];
                G_CURRENT[shape_idx] = mask;
                G_CURRENT_ADJ[shape_idx] = adj;

                let next_occ = occupied.or(mask);
                let next_prism = if prism { prism_adj.or(adj) } else { prism_adj };
                solve(rem, rem_count - 1, next_occ, next_prism);

                G_CURRENT[shape_idx] = Mask256::ZERO;
                G_CURRENT_ADJ[shape_idx] = Mask256::ZERO;

                if G_SOL_COUNT >= G_MAX_SOLS {
                    rem[i] = shape_idx as u8;
                    return;
                }
            }

            rem[i] = shape_idx as u8;
        }

        if !found {
            return;
        }
        return;
    }

    // MRV: pick shape with fewest non-overlapping placements.
    let mut best_i = 0usize;
    let mut best_count = u32::MAX;
    for i in 0..rem_count {
        let sid = rem[i] as usize;
        let mut valid = 0u32;
        for j in 0..G_P_COUNT[sid] {
            let mask = G_P_MASK[sid][j];
            if mask.intersects(occupied) {
                continue;
            }
            valid += 1;
        }

        if valid == 0 {
            return;
        }
        if valid < best_count {
            best_count = valid;
            best_i = i;
            if valid == 1 {
                break;
            }
        }
    }

    // Remove chosen shape from remaining (swap-with-last trick).
    let shape_idx = rem[best_i] as usize;
    rem[best_i] = rem[rem_count - 1];

    let pc = G_P_COUNT[shape_idx];
    let prism = G_PRISM[shape_idx];
    let adj_to = G_ADJ_TO[shape_idx];
    let mut target_adj = Mask256::ZERO;
    if adj_to >= 0 {
        let target = adj_to as usize;
        if !G_CURRENT[target].is_zero() {
            target_adj = G_CURRENT_ADJ[target];
        }
    }

    for i in 0..pc {
        let mask = G_P_MASK[shape_idx][i];
        if mask.intersects(occupied) {
            continue;
        }
        if !target_adj.is_zero() && !mask.intersects(target_adj) {
            continue;
        }
        if prism && !prism_adj.is_zero() && !mask.intersects(prism_adj) {
            continue;
        }

        let adj = G_P_ADJ[shape_idx][i];
        G_CURRENT[shape_idx] = mask;
        G_CURRENT_ADJ[shape_idx] = adj;

        let next_occ = occupied.or(mask);
        let next_prism = if prism { prism_adj.or(adj) } else { prism_adj };
        solve(rem, rem_count - 1, next_occ, next_prism);

        G_CURRENT[shape_idx] = Mask256::ZERO;
        G_CURRENT_ADJ[shape_idx] = Mask256::ZERO;

        if G_SOL_COUNT >= G_MAX_SOLS {
            rem[best_i] = shape_idx as u8;
            return;
        }
    }

    rem[best_i] = shape_idx as u8;
}

#[no_mangle]
pub extern "C" fn get_buffer_ptr() -> *const u8 {
    unsafe { DATA_BUFFER.as_ptr() }
}

/// Returns 1 if this grid size is supported by the WASM bitmask solver, 0 otherwise.
#[no_mangle]
pub extern "C" fn check_supported(w: i32, h: i32) -> i32 {
    if w <= 0 || h <= 0 {
        return 0;
    }
    let total = w.saturating_mul(h);
    if total > 0 && (total as usize) <= MAX_CELLS {
        1
    } else {
        0
    }
}

unsafe fn write_mask128(value: u128, out: &mut usize) {
    let words = [value as u64, (value >> 64) as u64, 0u64, 0u64];
    for w64 in words {
        core::ptr::copy_nonoverlapping(
            &w64 as *const u64 as *const u8,
            DATA_BUFFER.as_mut_ptr().add(*out),
            8,
        );
        *out += 8;
    }
}

unsafe fn write_mask256(value: Mask256, out: &mut usize) {
    let words = [
        value.lo as u64,
        (value.lo >> 64) as u64,
        value.hi as u64,
        (value.hi >> 64) as u64,
    ];
    for w64 in words {
        core::ptr::copy_nonoverlapping(
            &w64 as *const u64 as *const u8,
            DATA_BUFFER.as_mut_ptr().add(*out),
            8,
        );
        *out += 8;
    }
}

unsafe fn run_solver_128(w: i32, h: i32, disable_rotation: i32) -> i32 {
    G_CURRENT128 = [0; MAX_SHAPES];
    G_CURRENT_ADJ128 = [0; MAX_SHAPES];

    for i in 0..128 {
        G_NEIGHBOR128[i] = 0;
    }

    for i in 0..(G_TOTAL_CELLS as usize) {
        let x = (i as i32) % w;
        let y = (i as i32) / w;
        let offsets: [(i32, i32); 6] = if x % 2 == 0 {
            [(0, -1), (1, -1), (1, 0), (0, 1), (-1, 0), (-1, -1)]
        } else {
            [(0, -1), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0)]
        };

        let mut m = 0u128;
        for (dx, dy) in offsets {
            let nx = x + dx;
            let ny = y + dy;
            if nx >= 0 && nx < w && ny >= 0 && ny < h {
                m |= 1u128 << (ny * w + nx);
            }
        }
        G_NEIGHBOR128[i] = m;
    }

    let mut forbidden = 0u128;
    for i in 0..G_TOTAL_CELLS {
        if i % w == w - 1 || i / w == 0 {
            forbidden |= 1u128 << i;
        }
    }

    let mut buf_off = 0usize;
    let mut base: [Axial; 32] = [Axial { q: 0, r: 0 }; 32];
    let mut cur: [Axial; 32] = [Axial { q: 0, r: 0 }; 32];

    for s_idx in 0..G_SHAPE_COUNT {
        let prism = DATA_BUFFER[buf_off] == 1;
        buf_off += 1;
        let adj_to_raw = DATA_BUFFER[buf_off] as i8 as i32;
        buf_off += 1;
        let no_edge = DATA_BUFFER[buf_off] == 1;
        buf_off += 1;
        let n_cells = DATA_BUFFER[buf_off] as usize;
        buf_off += 1;

        if n_cells == 0 || n_cells > base.len() {
            DATA_BUFFER[0] = 0;
            return 0;
        }

        for c in 0..n_cells {
            let col = DATA_BUFFER[buf_off] as i32;
            buf_off += 1;
            let row = DATA_BUFFER[buf_off] as i32;
            buf_off += 1;
            base[c] = oddq_to_axial(col, row);
        }

        let adj_to = if adj_to_raw >= 0 && (adj_to_raw as usize) < G_SHAPE_COUNT {
            adj_to_raw
        } else {
            -1
        };

        G_PRISM[s_idx] = prism;
        G_ADJ_TO[s_idx] = adj_to;
        G_SIZE[s_idx] = n_cells as u32;

        for c in 0..n_cells {
            cur[c] = base[c];
        }

        let mut p_idx = 0usize;
        let mut seen_count = 0usize;
        let rotations = if disable_rotation != 0 { 1 } else { 6 };

        for _rot in 0..rotations {
            for py in 0..h {
                for px in 0..w {
                    let tgt = oddq_to_axial(px, py);
                    let src = cur[0];
                    let dq = tgt.q - src.q;
                    let dr = tgt.r - src.r;

                    let mut mask = 0u128;
                    let mut ok = true;
                    for c in 0..n_cells {
                        let (cx, cy) = axial_to_oddq(Axial {
                            q: cur[c].q + dq,
                            r: cur[c].r + dr,
                        });
                        if cx >= 0 && cx < w && cy >= 0 && cy < h {
                            mask |= 1u128 << (cy * w + cx);
                        } else {
                            ok = false;
                            break;
                        }
                    }

                    if ok && (!no_edge || mask & forbidden == 0) {
                        let mut dup = false;
                        for k in 0..seen_count {
                            if G_SEEN128[k] == mask {
                                dup = true;
                                break;
                            }
                        }
                        if !dup && p_idx < MAX_PLACEMENTS && seen_count < MAX_PLACEMENTS {
                            G_SEEN128[seen_count] = mask;
                            seen_count += 1;
                            G_P_MASK128[s_idx][p_idx] = mask;
                            G_P_ADJ128[s_idx][p_idx] = neighbor_of_mask128(mask);
                            p_idx += 1;
                        }
                    }
                }
            }
            for c in 0..n_cells {
                cur[c] = rotate_axial(cur[c]);
            }
        }

        G_P_COUNT[s_idx] = p_idx;
    }

    let mut rem = [0u8; MAX_SHAPES];
    for i in 0..G_SHAPE_COUNT {
        rem[i] = i as u8;
    }
    solve128(&mut rem, G_SHAPE_COUNT, 0, 0);

    let mut out = 0usize;
    DATA_BUFFER[out] = G_SOL_COUNT as u8;
    out += 1;

    for s in 0..G_SOL_COUNT {
        for m in 0..G_SHAPE_COUNT {
            write_mask128(G_SOLUTIONS128[s][m], &mut out);
        }
    }

    G_SOL_COUNT as i32
}

unsafe fn run_solver_256(w: i32, h: i32, disable_rotation: i32) -> i32 {
    G_CURRENT = [Mask256::ZERO; MAX_SHAPES];
    G_CURRENT_ADJ = [Mask256::ZERO; MAX_SHAPES];

    for i in 0..MAX_CELLS {
        G_NEIGHBOR[i] = Mask256::ZERO;
    }

    // Precompute hex neighbor lookup.
    for i in 0..(G_TOTAL_CELLS as usize) {
        let x = (i as i32) % w;
        let y = (i as i32) / w;
        let offsets: [(i32, i32); 6] = if x % 2 == 0 {
            [(0, -1), (1, -1), (1, 0), (0, 1), (-1, 0), (-1, -1)]
        } else {
            [(0, -1), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0)]
        };

        let mut m = Mask256::ZERO;
        for (dx, dy) in offsets {
            let nx = x + dx;
            let ny = y + dy;
            if nx >= 0 && nx < w && ny >= 0 && ny < h {
                let idx = (ny * w + nx) as usize;
                m = m.with_bit(idx);
            }
        }
        G_NEIGHBOR[i] = m;
    }

    let mut forbidden = Mask256::ZERO;
    for i in 0..G_TOTAL_CELLS {
        if i % w == w - 1 || i / w == 0 {
            forbidden = forbidden.with_bit(i as usize);
        }
    }

    let mut buf_off = 0usize;
    let mut base: [Axial; 32] = [Axial { q: 0, r: 0 }; 32];
    let mut cur: [Axial; 32] = [Axial { q: 0, r: 0 }; 32];

    for s_idx in 0..G_SHAPE_COUNT {
        let prism = DATA_BUFFER[buf_off] == 1;
        buf_off += 1;
        let adj_to_raw = DATA_BUFFER[buf_off] as i8 as i32;
        buf_off += 1;
        let no_edge = DATA_BUFFER[buf_off] == 1;
        buf_off += 1;
        let n_cells = DATA_BUFFER[buf_off] as usize;
        buf_off += 1;

        if n_cells == 0 || n_cells > base.len() {
            DATA_BUFFER[0] = 0;
            return 0;
        }

        for c in 0..n_cells {
            let col = DATA_BUFFER[buf_off] as i32;
            buf_off += 1;
            let row = DATA_BUFFER[buf_off] as i32;
            buf_off += 1;
            base[c] = oddq_to_axial(col, row);
        }

        let adj_to = if adj_to_raw >= 0 && (adj_to_raw as usize) < G_SHAPE_COUNT {
            adj_to_raw
        } else {
            -1
        };

        G_PRISM[s_idx] = prism;
        G_ADJ_TO[s_idx] = adj_to;
        G_SIZE[s_idx] = n_cells as u32;

        for c in 0..n_cells {
            cur[c] = base[c];
        }

        let mut p_idx = 0usize;
        let mut seen_count = 0usize;
        let rotations = if disable_rotation != 0 { 1 } else { 6 };

        for _rot in 0..rotations {
            for py in 0..h {
                for px in 0..w {
                    let tgt = oddq_to_axial(px, py);
                    let src = cur[0];
                    let dq = tgt.q - src.q;
                    let dr = tgt.r - src.r;

                    let mut mask = Mask256::ZERO;
                    let mut ok = true;
                    for c in 0..n_cells {
                        let (cx, cy) = axial_to_oddq(Axial {
                            q: cur[c].q + dq,
                            r: cur[c].r + dr,
                        });
                        if cx >= 0 && cx < w && cy >= 0 && cy < h {
                            let bit = (cy * w + cx) as usize;
                            mask = mask.with_bit(bit);
                        } else {
                            ok = false;
                            break;
                        }
                    }

                    if ok && (!no_edge || !mask.intersects(forbidden)) {
                        let mut dup = false;
                        for k in 0..seen_count {
                            if G_SEEN[k] == mask {
                                dup = true;
                                break;
                            }
                        }
                        if !dup && p_idx < MAX_PLACEMENTS && seen_count < MAX_PLACEMENTS {
                            G_SEEN[seen_count] = mask;
                            seen_count += 1;
                            G_P_MASK[s_idx][p_idx] = mask;
                            G_P_ADJ[s_idx][p_idx] = neighbor_of_mask(mask);
                            p_idx += 1;
                        }
                    }
                }
            }
            for c in 0..n_cells {
                cur[c] = rotate_axial(cur[c]);
            }
        }

        G_P_COUNT[s_idx] = p_idx;
    }

    let mut rem = [0u8; MAX_SHAPES];
    for i in 0..G_SHAPE_COUNT {
        rem[i] = i as u8;
    }
    solve(&mut rem, G_SHAPE_COUNT, Mask256::ZERO, Mask256::ZERO);

    let mut out = 0usize;
    DATA_BUFFER[out] = G_SOL_COUNT as u8;
    out += 1;

    for s in 0..G_SOL_COUNT {
        for m in 0..G_SHAPE_COUNT {
            write_mask256(G_SOLUTIONS[s][m], &mut out);
        }
    }

    G_SOL_COUNT as i32
}

/// Main entry point called from JavaScript.
///
/// Buffer input layout (written by JS before this call):
///   For each shape:
///     [+0]  prism    : u8  (0 or 1)
///     [+1]  adj_to   : u8  (0xFF = none, else shape index 0-31)
///     [+2]  no_edge  : u8  (0 or 1)
///     [+3]  n_cells  : u8
///     [+4..] (col, row) pairs as u8 each
///
/// Buffer output layout (written by Rust, starting at offset 0):
///   [0]       n_solutions : u8
///   For each solution, for each shape (in original index order):
///     word0 : low  64 bits of lo u128
///     word1 : high 64 bits of lo u128
///     word2 : low  64 bits of hi u128
///     word3 : high 64 bits of hi u128
#[no_mangle]
pub unsafe extern "C" fn run_solver(
    w: i32,
    h: i32,
    shape_count: i32,
    max_sols: i32,
    disable_rotation: i32,
) -> i32 {
    if w <= 0 || h <= 0 {
        DATA_BUFFER[0] = 0;
        return 0;
    }

    let total_cells = w.saturating_mul(h);
    if total_cells <= 0 || (total_cells as usize) > MAX_CELLS {
        DATA_BUFFER[0] = 0;
        return 0;
    }

    if shape_count < 0 || (shape_count as usize) > MAX_SHAPES {
        DATA_BUFFER[0] = 0;
        return 0;
    }

    let max_sols_clamped = if max_sols <= 0 {
        1usize
    } else {
        core::cmp::min(max_sols as usize, MAX_SOLUTIONS)
    };

    G_TOTAL_CELLS = total_cells;
    G_SHAPE_COUNT = shape_count as usize;
    G_MAX_SOLS = max_sols_clamped;
    G_SOL_COUNT = 0;
    if total_cells <= 128 {
        run_solver_128(w, h, disable_rotation)
    } else {
        run_solver_256(w, h, disable_rotation)
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
