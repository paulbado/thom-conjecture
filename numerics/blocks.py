"""Dyadic block energies of c_n and d_n, partial sums, Cesaro atom means.
Usage: python3 blocks.py cheb_coeffs_n256.txt"""
import sys, numpy as np
from common import load, weighted
c = load(sys.argv[1]); d = weighted(c); N = max(c)
print("| j | block | sum c_n^2 | sum d_n^2 | D_j/D_{j-1} |")
print("|---|---|---|---|---|")
j, prev = 2, None
while 2 ** j <= N - 2:
    hi = min(2 ** (j + 1), N - 1); ks = range(2 ** j, hi)
    C = sum(c[k] ** 2 for k in ks); D = sum(d[k] ** 2 for k in ks)
    tag = "" if hi == 2 ** (j + 1) else " (partial)"
    print(f"| {j} | [{2**j},{hi}){tag} | {C:.5f} | {D:.3e} | {'' if prev is None else f'{D/prev:.3f}'} |")
    prev = D; j += 1
print("\n| n | sum c_k^2 (1<=k<=n) | sum d_k^2 (1<=k<=n) | n^-1 sum_{k<n} c_k^2 | atom Cesaro mean A_{n/2} |")
print("|---|---|---|---|---|")
for n in [20, 40, 80, 120, 160, 200, 240, N - 2]:
    if n > N - 2: continue
    S = sum(c[k] ** 2 for k in range(1, n + 1)); Sd = sum(d[k] ** 2 for k in range(1, n + 1))
    E = sum(c[k] ** 2 for k in range(n)) / n
    M = n // 2; A = sum((-1) ** i * c[2 * i] for i in range(M + 1)) / (M + 1)
    print(f"| {n} | {S:.6f} | {Sd:.6f} | {E:.5f} | {A:+.5f} |")
