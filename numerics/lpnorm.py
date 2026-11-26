"""L^p(arcsine) norms of Jackson-smoothed densities of mu_A and of nu/nu(R).
Usage: python3 lpnorm.py cheb_coeffs_n256.txt"""
import sys, numpy as np
from common import load, weighted, density
c = load(sys.argv[1]); Nmax = max(c); dw = weighted(c)
cc = np.array([c[n] for n in range(Nmax + 1)])
dd = np.array([dw[n] for n in range(Nmax - 1)]); dd = dd / dd[0]
th = np.linspace(1e-6, np.pi - 1e-6, 40001); E = 4 * np.cos(th)
nrm = lambda h, p: (np.trapezoid(h ** p, th) / np.pi) ** (1 / p)
print("N | mu: p=1.25 | 1.5 | 1.75 | 2 | entropy | nu: p=1.5 | 2")
for N in [24, 48, 96, 192, 252]:
    if N > len(dd) - 1: continue
    f = np.maximum(density(cc, N, E), 0); g = np.maximum(density(dd, N, E), 0)
    ent = np.trapezoid(np.where(f > 0, f * np.log(np.maximum(f, 1e-300)), 0), th) / np.pi
    print(N, "|", " | ".join(f"{nrm(f, p):.4f}" for p in [1.25, 1.5, 1.75, 2.0]), f"| {ent:.4f} |",
          f"{nrm(g, 1.5):.4f} | {nrm(g, 2.0):.4f}")
