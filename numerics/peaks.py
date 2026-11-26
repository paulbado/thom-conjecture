"""Local maxima of Jackson-smoothed densities of mu_A and their growth with the degree.
Usage: python3 peaks.py cheb_coeffs_n256.txt"""
import sys, numpy as np
from common import load, weighted, density
c = load(sys.argv[1]); Nmax = max(c)
cc = np.array([c[n] for n in range(Nmax + 1)])
E = np.linspace(-3.99, 3.99, 7981)
Ns = [63, 126, 252]
F = {N: density(cc, N, E) for N in Ns}
f = F[Ns[-1]]
print("E | f_63 | f_126 | f_252")
for i in range(1, len(E) - 1):
    if E[i] >= -0.001 and f[i] > f[i - 1] and f[i] > f[i + 1] and f[i] > 0.5:
        print(f"{E[i]:.3f} | " + " | ".join(f"{F[N][i]:.3f}" for N in Ns))
