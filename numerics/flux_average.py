"""Exact rational-flux averages nu_Q = (1/Q) sum_{p<Q} N_{p/Q} of the Harper densities of states.

N_alpha is the integrated density of states of H = u + u* + v + v*, (Hψ)_j = ψ_{j+1} + ψ_{j-1}
+ 2cos(2π(αj+θ))ψ_j, averaged over θ.  mu_A = ∫_0^1 N_alpha dα (centre decomposition), and by the
Lean theorem ThomHeisenberg.avg_fluxTrace_opA_pow the moments of nu_Q equal τ(A^n) for n < N_Q.
For α = p/q in lowest terms, Chambers' relation gives the spectrum condition
D(E) = 2cos k + 2cos(2πqθ), so the eigenvalue in band j is D_j^{-1}(X) with X = 2cosφ1 + 2cosφ2
uniform-angle distributed.  Hence on band j the IDS increases by G(D(E)) (or 1 - G(D(E))) where
G is the distribution function of X.  Everything below is exact up to floating point and the
tabulation of G.  Output: CDF of nu_Q on a uniform grid of [-4,4].
Usage: python3 flux_average.py Q M  (M = number of bins)"""
import sys, numpy as np
from math import gcd

def G_table(n=40001, m=8000):
    t = np.linspace(-4, 4, n)
    phi = (np.arange(m) + 0.5) * np.pi / m
    out = np.empty(n)
    for i in range(0, n, 1000):
        s = (t[i:i + 1000, None] - 2 * np.cos(phi)[None, :]) / 2
        out[i:i + 1000] = (1 - np.arccos(np.clip(s, -1, 1)) / np.pi).mean(axis=1)
    return t, out
GT, GV = G_table()
G = lambda x: np.interp(x, GT, GV)

def D(E, p, q):
    """Discriminant at θ0 = 1/(4q) (where cos(2πqθ0) = 0)."""
    a, b, c, d = np.ones_like(E), np.zeros_like(E), np.zeros_like(E), np.ones_like(E)
    for j in range(q):
        v = E - 2 * np.cos(2 * np.pi * (p * j / q + 1 / (4 * q)))
        a, b, c, d = v * a - c, v * b - d, a, b
    return a + d

def bloch(p, q, theta, k):
    H = np.zeros((q, q), complex)
    for j in range(q):
        H[j, j] += 2 * np.cos(2 * np.pi * (p * j / q + theta))
        H[j, (j + 1) % q] += np.exp(1j * k * (j == q - 1))
        H[(j + 1) % q, j] += np.exp(-1j * k * (j == q - 1))
    return H

def ids(p, q, grid):
    """IDS of N_{p/q} at the points of grid."""
    if q == 1:
        return G(grid)
    # band edges: eigenvalues at D = +4 (θ = 0, k = 0) and D = -4 (θ = 1/(2q), k = π)
    ep = np.linalg.eigvalsh(bloch(p, q, 0.0, 0.0))
    em = np.linalg.eigvalsh(bloch(p, q, 1 / (2 * q), np.pi))
    allE = np.concatenate([ep, em]); lab = np.concatenate([np.ones(q), -np.ones(q)])
    o = np.argsort(allE, kind="stable"); allE, lab = allE[o], lab[o]
    out = np.zeros_like(grid)
    for j in range(q):
        a, b = allE[2 * j], allE[2 * j + 1]
        up = lab[2 * j] < 0          # D goes from -4 to +4 on the band
        i0, i1 = np.searchsorted(grid, [a, b])
        x = grid[i0:i1]
        g = G(np.clip(D(x, p, q), -4, 4))
        out[i0:i1] += g if up else 1 - g
        out[i1:] += 1
    return out / q

def nu_cdf(Q, grid):
    tot = np.zeros_like(grid)
    for p in range(Q):
        g = gcd(p, Q); tot += ids(p // g, Q // g, grid)
    return tot / Q

if __name__ == "__main__":
    Q, M = int(sys.argv[1]), int(sys.argv[2])
    grid = np.linspace(-4, 4, M + 1)
    cdf = nu_cdf(Q, grid)
    np.save(f"nu_cdf_Q{Q}_M{M}.npy", cdf)
    print("total mass", cdf[-1], "min increment", np.diff(cdf).min())
