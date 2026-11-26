"""Round 8, Task 6: Fejér entropies of the Dirichlet model at its own scale.

Lean (ThomStrip.fejEnt_two_scale_le) proves
    H_n(mu_A) <= 2 H_n(sigma_{2W}) + 2 log 2 + 1     (n <= 2W),
where H_n(mu) = ∫ F_n log F_n dρ is the Fejér entropy. So a uniform bound on
H_n(sigma_{2n+2}) would give FejerEntropyTarget. This script estimates H_n(sigma_L) by
sampling (α,θ) on a randomly shifted grid. It also checks the two-scale identity
c_m(mu_A) = 2 c_m(sigma_{2W}) - c_m(sigma_W) against the exact c_m(mu_A) (cheb_coeffs_n256.txt).
Usage: python3 strip_entropy.py [samples]
"""
import sys, numpy as np
from common import load

S = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
rng = np.random.default_rng(8)
cA = load('cheb_coeffs_n256.txt')

def cheb_coeffs(L, mmax, S):
    """c_m(sigma_L) = average over eigenvalues of T_m(E/4), m <= mmax."""
    j = np.arange(1, L + 1)
    g = int(np.sqrt(S)); u0, v0 = rng.random(2)
    acc = np.zeros(mmax + 1); cnt = 0
    for a_i in range(g):
        a = (a_i + u0) / g
        t = (np.arange(g) + v0) / g
        H = np.zeros((g, L, L))
        H[:, j - 1, j - 1] = 2 * np.cos(2 * np.pi * (t[:, None] + j[None, :] * a))
        H[:, j[:-1] - 1, j[:-1]] = 1; H[:, j[:-1], j[:-1] - 1] = 1
        ev = np.linalg.eigvalsh(H).ravel()
        phi = np.arccos(np.clip(ev / 4, -1, 1))
        acc += np.cos(np.outer(np.arange(mmax + 1), phi)).sum(axis=1); cnt += ev.size
    return acc / cnt

def fejer_entropy(c, n, P=20000):
    phi = (np.arange(P) + 0.5) * np.pi / P
    F = np.ones(P)
    for m in range(1, n + 1):
        F += 2 * (1 - m / (n + 1)) * c[m] * np.cos(m * phi)
    F = np.maximum(F, 1e-300)
    return float(np.mean(F * np.log(F))), float(F.min())

print(f"samples per L: {int(np.sqrt(S))**2}")
print(" n   W    H_n(mu_A)   H_n(sig_2W)  bound 2H+2log2+1   max|c_A - (2c_2W - c_W)| (m<=n)")
for n in [8, 16, 32, 64, 128]:
    W = n // 2 if n >= 2 else 1
    W = max(W, 1)
    c2 = cheb_coeffs(2 * W, n, S)
    c1 = cheb_coeffs(W, n, S)
    ca = np.array([cA.get(m, 0.0) for m in range(n + 1)])
    HA, _ = fejer_entropy(ca, n)
    H2, _ = fejer_entropy(c2, n)
    err = np.max(np.abs(ca[1:] - (2 * c2[1:] - c1[1:])))
    print(f"{n:3d} {W:3d}  {HA:10.4f}  {H2:10.4f}   {2*H2+2*np.log(2)+1:10.4f}        {err:.2e}")
