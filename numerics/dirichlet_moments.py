"""Round 7, Task 2: exact (α,θ)-averaged moments of the Dirichlet model.

m_k(L) = ∫∫ (1/L) tr H_L(α,θ)^k dα dθ. The integrand is a trigonometric polynomial of degree ≤ k
in θ and ≤ kL in α, so the product midpoint rule with (k+1) × (kL+1) nodes is exact (up to
rounding). Compares with τ(A^k) (zero-area closed walks) and the bound |m_k(L) − τ(A^k)| ≤ 2k·4^k/L.
Usage: python3 dirichlet_moments.py L kmax
"""
import sys, numpy as np
L = int(sys.argv[1]); K = int(sys.argv[2]); j = np.arange(1, L + 1)
import ast
tau = dict(enumerate(ast.literal_eval(open(__file__.replace("dirichlet_moments.py", "moments_exact_n120.txt")).read())))
nt, na = K + 1, K * L + 1
pw = np.zeros(K + 1)
for t in (np.arange(nt) + 0.5) / nt:
    for a in (np.arange(na) + 0.5) / na:
        ev = np.linalg.eigvalsh(np.diag(2*np.cos(2*np.pi*(t + j*a))) + np.diag(np.ones(L-1), 1) + np.diag(np.ones(L-1), -1))
        pw += np.array([np.sum(ev ** k) for k in range(K + 1)])
pw /= nt * na * L
print(f"L = {L}")
for k in range(2, K + 1, 2):
    print(f"k = {k:2d}: m_k(L) = {pw[k]:14.4f}   τ(A^k) = {tau.get(k, float('nan')):10}   "
          f"|diff| = {abs(pw[k] - tau.get(k, np.nan)):10.4f}   bound 2k4^k/L = {2*k*4**k/L:.3g}   "
          f"L·(τ − m_k) = {L*(tau[k]-pw[k]):.3f}")
