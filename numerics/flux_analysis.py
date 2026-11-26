"""Dyadic L^p(arcsine) norms and local scaling exponents of mu_A from the exact flux averages
nu_Q (flux_average.py).  Usage: python3 flux_analysis.py Q1 Q2 ... (files nu_cdf_Q*_M32768.npy)"""
import sys, numpy as np
M = 32768
grid = np.linspace(-4, 4, M + 1)
rho = 0.5 + np.arcsin(np.clip(grid / 4, -1, 1)) / np.pi      # arcsine CDF
Qs = [int(a) for a in sys.argv[1:]]
cdfs = {Q: np.load(f"nu_cdf_Q{Q}_M{M}.npy") for Q in Qs}

def binned_norm(cdf, k, p):
    """(sum_bins rho(I) (nu(I)/rho(I))^p) with 2^k bins."""
    step = M // 2 ** k
    m = np.diff(cdf[::step]); r = np.diff(rho[::step])
    return np.sum(r * (m / r) ** p)

print("binned ∫ f^p dρ at 2^k bins (resolution 8/2^k)")
for p in [1.5, 2.0, 3.0]:
    print(f"p = {p}")
    print("   k " + " ".join(f"  Q={Q:4d}" for Q in Qs))
    for k in range(4, 16):
        print(f"  {k:2d} " + " ".join(f"{binned_norm(cdfs[Q], k, p):9.4f}" for Q in Qs))

def local(cdf, E0, hs):
    out = []
    for h in hs:
        a, b = np.searchsorted(grid, [E0 - h, E0 + h]); b = min(b, M)
        out.append(cdf[b] - cdf[a])
    return np.array(out)

hs = 8 / 2 ** np.arange(3, 14)
print("\nlocal mass ν_Q([E0-h,E0+h]) and slopes d log mass / d log h (1 = bounded density)")
Q = Qs[-1]
for E0 in [0.0, 0.7, 0.72, 0.75, 1.95, 2.0, 2.57, 3.0, 3.9]:
    m = local(cdfs[Q], E0, hs)
    sl = np.diff(np.log(m)) / np.diff(np.log(hs))
    print(f"E0={E0:5.2f} slopes: " + " ".join(f"{s:5.2f}" for s in sl))
