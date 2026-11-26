"""Local masses nu_Q([E0-h, E0+h]) for dyadic h, from the exact flux averages (flux_average.py).
Usage: python3 flux_local.py E0 Q1 Q2 ..."""
import sys, time, numpy as np
from flux_average import nu_cdf
E0 = float(sys.argv[1]); Qs = [int(a) for a in sys.argv[2:]]
hs = 2.0 ** -np.arange(0, 19)
grid = np.sort(np.concatenate([E0 - hs, E0 + hs]))
print(f"E0 = {E0}: average density m/(2h) for h = 2^-j, j = 0..18")
for Q in Qs:
    t = time.time()
    cdf = nu_cdf(Q, grid)
    m = cdf[len(hs):][::1] - cdf[:len(hs)][::-1]          # pairs (E0-h, E0+h), h descending
    m = m[::-1] if False else m
    # grid order: E0-h for h descending ... then E0+h for h ascending
    lo = cdf[:len(hs)]; hi = cdf[len(hs):][::-1]
    m = hi - lo
    print(f"Q={Q:4d} ({time.time()-t:5.1f}s): " + " ".join(f"{x:.3f}" for x in m / (2 * hs)))
