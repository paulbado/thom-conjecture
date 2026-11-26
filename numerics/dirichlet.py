"""Round 7: the continuous-flux Dirichlet Harper model.

H_L(α,θ): L×L, off-diagonal 1, diagonal 2cos(2π(θ+jα)), j = 1..L.
Hellmann–Feynman (simple eigenvalues): ∂α E = -4π Σ j sin(2π(θ+jα)) u_j²,
                                       ∂θ E = -4π Σ   sin(2π(θ+jα)) u_j².
Outputs (Task 5):
 (1) median of max(|∂θE|, |∂αE|/L) at random (α,θ,k)  [reproduces the reported decay];
 (2) the actual number M_L(θ,E) of α ∈ [0,1) with E ∈ spec H_L(α,θ), against L(L+1);
 (3) the coarea entropy bound  R_L(θ) = (1/L) Σ_k ∫ log(M_L(θ,E_k)/(L|∂αE_k|)) dα  (Monte Carlo),
     its θ-average, and the actual entropy ∫ g log g of the α-averaged density g_{L,θ};
 (4) exceptional sets: share of (α,k) with L|∂αE|/M small, and their energies.
Usage: python3 dirichlet.py L [samples]
"""
import sys, numpy as np
rng = np.random.default_rng(7)
L = int(sys.argv[1]); S = int(sys.argv[2]) if len(sys.argv) > 2 else 400
j = np.arange(1, L + 1)

def H(a, t):
    return np.diag(2 * np.cos(2 * np.pi * (t + j * a))) + np.diag(np.ones(L - 1), 1) + np.diag(np.ones(L - 1), -1)

def eig_der(a, t):
    E, U = np.linalg.eigh(H(a, t))
    s = np.sin(2 * np.pi * (t + j * a))
    dA = -4 * np.pi * ((j * s) @ (U ** 2))
    dT = -4 * np.pi * (s @ (U ** 2))
    return E, dA, dT

def count_below(E, agrid, t):
    """Sturm count #{eigenvalues < E} of H_L(α,θ) for every α in agrid (vectorized LDLᵀ)."""
    if len(agrid) > 8192:
        return np.concatenate([count_below(E, agrid[i:i + 8192], t) for i in range(0, len(agrid), 8192)])
    d = 2 * np.cos(2 * np.pi * (t + np.outer(agrid, j)))   # G × L
    q = d[:, 0] - E
    n = (q < 0).astype(int)
    for i in range(1, L):
        q = np.where(q == 0, 1e-300, q)
        q = d[:, i] - E - 1.0 / q
        n += (q < 0)
    return n

G = int(sys.argv[3]) * L * L if len(sys.argv) > 3 else 40 * L * L   # α-grid for preimage counts
agrid = (np.arange(G) + 0.5) / G
def M_count(E, t):
    n = count_below(E, agrid, t)
    return int(np.sum(n != np.roll(n, 1)))   # crossings of the level E (periodic in α)

# (1) derivatives
vals = []
for _ in range(128):
    a, t = rng.random(2)
    E, dA, dT = eig_der(a, t)
    k = rng.integers(L)
    vals.append(max(abs(dT[k]), abs(dA[k]) / L))
print(f"L = {L}")
print(f"(1) median max(|dθE|, |dαE|/L) over 128 random (α,θ,k): {np.median(vals):.4f}")

# (2)-(4) Monte Carlo over θ, α, k
thetas = rng.random(8)
Rs, ratios, Ms, Es = [], [], [], []
for t in thetas:
    acc = []
    for _ in range(S // len(thetas)):
        a = rng.random(); k = rng.integers(L)
        E, dA, dT = eig_der(a, t)
        M = M_count(E[k], t)
        r = M / (L * abs(dA[k]))
        acc.append(np.log(r)); ratios.append(r); Ms.append(M); Es.append(E[k])
    Rs.append(np.mean(acc))
Ms = np.array(Ms); ratios = np.array(ratios); Es = np.array(Es)
print(f"(2) M_L(θ,E): mean {Ms.mean():.1f}, median {np.median(Ms):.0f}, max {Ms.max()}, "
      f"L = {L}, L(L+1) = {L*(L+1)}; mean M/L = {Ms.mean()/L:.3f}")
print(f"(3) R_L(θ) for 8 random θ: " + " ".join(f"{r:.3f}" for r in Rs) + f"   θ-mean {np.mean(Rs):.3f}")
qs = np.quantile(ratios, [0.5, 0.9, 0.99])
print(f"    ratio M/(L|∂αE|): median {qs[0]:.3f}, 90% {qs[1]:.3f}, 99% {qs[2]:.3f}, max {ratios.max():.3g}")
big = ratios > 10
print(f"(4) exceptional share ratio > 10: {big.mean():.4f}; their mean |E| {np.abs(Es[big]).mean() if big.any() else float('nan'):.3f} "
      f"vs overall {np.abs(Es).mean():.3f}; share with |E| < 0.25 among them "
      f"{np.mean(np.abs(Es[big]) < 0.25) if big.any() else float('nan'):.3f} (overall {np.mean(np.abs(Es) < 0.25):.3f})")
# actual entropy of g_{L,θ} (α-average at fixed θ), histogram estimate
t = thetas[0]
Ag = (np.arange(4000) + 0.5) / 4000
allE = np.concatenate([np.linalg.eigvalsh(H(a, t)) for a in Ag])
hist, edges = np.histogram(allE, bins=800, range=(-4, 4), density=True)
w = edges[1] - edges[0]
h = hist[hist > 0]
print(f"    ∫ g log g dE at θ = {t:.3f} (histogram, 800 bins): {np.sum(h * np.log(h)) * w:.3f}  vs R_L = {Rs[0]:.3f}")
