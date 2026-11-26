"""Round 9, Task 5: tail distributions of coarea ratios with dyadic velocity classes.

Model (round 7): H_L(α,θ) is L×L, off-diagonal 1, diagonal d_i = 2cos(2π(θ+iα)), i = 1..L.
P_L: (θ, α) uniform on [0,1)², k uniform in {1..L}; E = E_k(α,θ), v = ∂_α E_k(α,θ).
Crossings of the level E at fixed θ: all (α', k') with E_{k'}(α',θ) = E (found by Sturm counts
on an α-grid of size G = g·L², then bisection); M_L(θ,E) = their number.
Velocity at a crossing: v = -∂_α p / ∂_E p with p(α,E) = det(E - H_L(α,θ)) (three-term
recurrence with derivatives, jointly rescaled).
Ratios
  plain : R_L = M_L / (L |v|)
  class : j(c) = floor(log2(|v_c| / L)), M_{L,j} = #crossings of class j,
          a_j = budget ∝ 1/(1+|j|)^2 on j ∈ [-40, 10], Σ a_j = 1,
          R_{L,j} = M_{L,j} / (a_j L |v|) for the sampled crossing's class j.
Prints P_L(R > K) for K ∈ {10,20,50,100,200,500,1000}, globally and on |E| ≥ ε.
This is numerical evidence only: no tightness claim is inferred from finite samples.
Usage: python3 velocity_classes.py L samples [g]
"""
import sys, numpy as np
L = int(sys.argv[1]); S = int(sys.argv[2]); g = int(sys.argv[3]) if len(sys.argv) > 3 else 24
rng = np.random.default_rng(1000 + L)
idx = np.arange(1, L + 1)
JR = np.arange(-40, 11)
aw = 1.0 / (1 + np.abs(JR)) ** 2; aw /= aw.sum()
def a_of(j): return aw[np.clip(j, -40, 10) + 40]
KS = [10, 20, 50, 100, 200, 500, 1000]

def H(a, t):
    return np.diag(2 * np.cos(2 * np.pi * (t + idx * a))) + np.diag(np.ones(L - 1), 1) + np.diag(np.ones(L - 1), -1)

def count_below(E, al, t):
    out = np.empty(len(al), dtype=np.int64)
    for s in range(0, len(al), 16384):
        a = al[s:s + 16384]
        q = 2 * np.cos(2 * np.pi * (t + a * 1)) - E
        n = (q < 0).astype(np.int64)
        for i in range(2, L + 1):
            q = np.where(q == 0, 1e-300, q)
            q = 2 * np.cos(2 * np.pi * (t + a * i)) - E - 1.0 / q
            n += (q < 0)
        out[s:s + 16384] = n
    return out

def velocity(E, al, t):
    """-∂α p / ∂E p at (al, E), p = det(E - H), vectorized over al."""
    p0 = np.ones_like(al); p1 = np.zeros_like(al)        # p_{i-1}, p_{i-2}
    e0 = np.zeros_like(al); e1 = np.zeros_like(al)       # ∂E
    a0 = np.zeros_like(al); a1 = np.zeros_like(al)       # ∂α
    for i in range(1, L + 1):
        ph = 2 * np.pi * (t + i * al)
        d = 2 * np.cos(ph); dd = -4 * np.pi * i * np.sin(ph)
        p = (E - d) * p0 - p1
        e = p0 + (E - d) * e0 - e1
        a = -dd * p0 + (E - d) * a0 - a1
        p1, p0, e1, e0, a1, a0 = p0, p, e0, e, a0, a
        sc = np.maximum.reduce([np.abs(p0), np.abs(p1), np.abs(e0), np.abs(e1), np.abs(a0), np.abs(a1)]) + 1e-300
        p0, p1, e0, e1, a0, a1 = p0 / sc, p1 / sc, e0 / sc, e1 / sc, a0 / sc, a1 / sc
    return -a0 / e0

G = g * L * L
grid = np.arange(G + 1) / G
rows = []
for s in range(S):
    t, a = rng.random(2); k = rng.integers(L)
    Ev, U = np.linalg.eigh(H(a, t))
    E = Ev[k]
    v = -4 * np.pi * ((idx * np.sin(2 * np.pi * (t + idx * a))) @ (U[:, k] ** 2))
    n = count_below(E, grid, t)
    jumps = np.nonzero(n[1:] != n[:-1])[0]
    lo, hi = grid[jumps].copy(), grid[jumps + 1].copy()
    nlo = n[jumps]
    mult = np.abs(n[jumps + 1] - n[jumps])
    for _ in range(18):
        mid = (lo + hi) / 2
        nm = count_below(E, mid, t)
        left = nm != nlo
        hi = np.where(left, mid, hi); lo = np.where(left, lo, mid)
    vel = velocity(E, (lo + hi) / 2, t)
    vel = np.repeat(vel, mult)
    M = len(vel)
    cls = np.floor(np.log2(np.abs(vel) / L + 1e-300)).astype(int)
    js = int(np.floor(np.log2(abs(v) / L + 1e-300)))
    Mj = int(np.sum(cls == js))
    Rp = M / (L * abs(v))
    Rc = max(Mj, 1) / (a_of(js) * L * abs(v))
    rows.append((E, v, M, Mj, js, Rp, Rc))
R = np.array(rows)
E, M = R[:, 0], R[:, 2]
print(f"L = {L}, samples = {S}, α-grid = {G}, L(L+1) = {L*(L+1)}, mean M = {M.mean():.1f}, max M = {M.max():.0f}")
for name, col in (("plain R_L", 5), ("class R_L,j", 6)):
    for eps in (0.0, 0.5, 1.0):
        sel = np.abs(E) >= eps
        tail = " ".join(f"{np.mean((R[:, col] > K) & sel):.4f}" for K in KS)
        print(f"  {name:12s} P(R>K, |E|≥{eps:.1f}) K={KS}: {tail}")
print(f"  class index of sampled crossing: min {R[:,4].min():.0f}, median {np.median(R[:,4]):.0f}, max {R[:,4].max():.0f}")
print(f"  median plain R {np.median(R[:,5]):.3f}, median class R {np.median(R[:,6]):.3f}, max class R {R[:,6].max():.3g}")
