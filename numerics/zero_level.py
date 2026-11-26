"""Zero Landau level of the Harper operator near half flux.
For α = p/q = 1/2 + δ, count the bands within distance w of E = 0 and measure the spread w(δ)
of the central cluster of ≈ 2|δ|q bands.  Usage: python3 zero_level.py q"""
import sys, numpy as np
from flux_average import bloch
q = int(sys.argv[1])
print(" p    δ        2|δ|q  spread w of the 2|δ|q central bands   log w    1/|δ|")
for p in range((q - 1) // 2, (q - 1) // 2 - 40, -1):
    d = p / q - 0.5
    ep = np.linalg.eigvalsh(bloch(p, q, 0.0, 0.0))
    em = np.linalg.eigvalsh(bloch(p, q, 1 / (2 * q), np.pi))
    edges = np.sort(np.concatenate([ep, em]))
    bands = edges.reshape(-1, 2)
    k = int(round(2 * abs(d) * q))          # expected size of the zero level (odd q: k odd)
    dist = np.max(np.abs(bands), axis=1)      # farthest point of each band from 0
    o = np.sort(dist)
    w = o[k - 1]; gap = o[k] if k < len(o) else np.nan
    print(f"{p:3d} {d:+.4f} {2*abs(d)*q:6.2f}  w = {w:.3e}  next band at {gap:.3e}  {np.log(w):7.2f} {1/abs(d):7.1f}")
