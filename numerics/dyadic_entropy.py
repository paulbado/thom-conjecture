"""Round 5: dyadic entropy, discrepancies, weighted energies and Fejer entropy of nu_Q.

lambda = theta_* nu_Q with theta(E) = arccos(E/4)/pi on [0,1] (Lean: ThomDyadicTarget.lam is the
same map applied to mu_A).  Cell masses at level K are exact differences of the exact distribution
function of nu_Q (flux_average.nu_cdf) at E_j = 4cos(pi j / 2^K).

Output, for each Q:
* H_k = sum_I lam(I) log(2^k lam(I)), increments H_{k+1}-H_k, discrepancies
  D_k = sum_I (lam(I-) - lam(I+))^2 / lam(I) (Lean: ThomDyadic.dyEnt, dyDisc), k^2 D_k, and the
  share of D_k coming from the two cells touching theta = 1/2 (E = 0) and from the cells within
  2^-6 of theta = 1/2;
* binned L^p energies 2^{k(p-1)} sum_I lam(I)^p (unweighted) and the same for the weighted
  measure cos^2(pi theta) lam = (E^2/16) nu_Q, p = 3/2, 2;
* Fejer relative entropy H_N = int F_N log F_N d theta (Lean: ThomEntropy), F_N built from the
  Chebyshev coefficients of nu_Q (equal to those of mu_A only for n < N_Q = 2 ceil(2 sqrt Q)).
Usage: python3 dyadic_entropy.py K Q1 Q2 ...
"""
import sys, time, math
import numpy as np
from flux_average import nu_cdf

K = int(sys.argv[1]); Qs = [int(a) for a in sys.argv[2:]]
n = 2 ** K
th = np.arange(n + 1) / n
E = 4 * np.cos(np.pi * th)            # decreasing
NQ = lambda Q: 2 * math.ceil(2 * math.sqrt(Q))

def xlogx(x):
    out = np.zeros_like(x); m = x > 0; out[m] = x[m] * np.log(x[m]); return out

for Q in Qs:
    t0 = time.time()
    cdf = nu_cdf(Q, E[::-1].copy())[::-1]   # cdf at E_j (computed on an increasing grid)
    m = cdf[:-1] - cdf[1:]                  # lam(cell j) = nu_Q((E_{j+1}, E_j])
    m = np.clip(m, 0, None); m /= m.sum()
    mid = (np.arange(n) + 0.5) / n
    wfine = np.cos(np.pi * mid) ** 2 * m     # weighted masses (midpoint rule inside fine cells)
    print(f"=== Q = {Q}  (N_Q = {NQ(Q)}, level K = {K}, {time.time() - t0:.0f}s)")
    print(" k   H_k      H_{k+1}-H_k   D_k        k^2 D_k   D_k share: 2 cells at E=0 / |theta-1/2|<2^-6"
          "   L^{3/2}   L^2   | weighted L^{3/2}  L^2")
    levels = []
    for k in range(0, K):
        mk = m.reshape(2 ** k, -1).sum(axis=1)
        mk1 = m.reshape(2 ** (k + 1), -1).sum(axis=1)
        wk = wfine.reshape(2 ** k, -1).sum(axis=1)
        H = (xlogx(2 ** k * mk) / 2 ** k).sum()
        H1 = (xlogx(2 ** (k + 1) * mk1) / 2 ** (k + 1)).sum()
        a, b = mk1[0::2], mk1[1::2]
        terms = np.where(mk > 0, (a - b) ** 2 / np.where(mk > 0, mk, 1), 0)
        Dk = terms.sum()
        c = (np.arange(2 ** k) + 0.5) / 2 ** k
        near0 = np.abs(c - 0.5) <= 0.5 / 2 ** k + 1e-15
        near6 = np.abs(c - 0.5) < 2.0 ** -6
        lp = lambda x, p: (2 ** k) ** (p - 1) * (x ** p).sum()
        print(f"{k:2d} {H:8.5f}  {H1 - H:10.3e}  {Dk:10.3e}  {k * k * Dk:8.4f}   "
              f"{terms[near0].sum() / Dk if Dk > 0 else 0:6.3f} / {terms[near6].sum() / Dk if Dk > 0 else 0:6.3f}"
              f"   {lp(mk, 1.5):7.4f} {lp(mk, 2):8.3f} | {lp(wk, 1.5):7.4f} {lp(wk, 2):7.4f}")
    # Fejer relative entropy; Chebyshev coefficients c_j = int cos(j pi theta) dlam, computed with
    # the exact antiderivative over fine cells (error O(j 2^-K) relative).
    jmax = 1024
    edges = th
    cs = [1.0]
    for j in range(1, jmax + 1):
        S = np.sin(j * np.pi * edges)
        dens = m * n                       # piecewise-constant density on fine cells
        cs.append(float((dens * (S[1:] - S[:-1]) / (j * np.pi)).sum()))
    cs = np.array(cs)
    grid = (np.arange(8192) + 0.5) / 8192
    print(" Fejer entropy H_N = int F_N log F_N dtheta (N > N_Q: nu_Q, not mu_A)")
    for N in [16, 32, 64, 128, 256, 512, 1024]:
        F = np.ones_like(grid)
        for j in range(1, N + 1):
            F += 2 * (1 - j / (N + 1)) * cs[j] * np.cos(j * np.pi * grid)
        HN = xlogx(np.clip(F, 0, None)).mean()
        flag = "" if N < NQ(Q) else "  (N >= N_Q)"
        print(f"   N = {N:5d}  H_N = {HN:.5f}  min F_N = {F.min():.2e}  "
              f"int F^2 = {(F ** 2).mean():.4f}{flag}")
    sys.stdout.flush()
