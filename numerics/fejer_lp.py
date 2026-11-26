"""L^p(arcsine) norms of the Fejér densities F_N of mu_A (Lean: ThomFejer.fejerA).
F_N(θ) = 1 + 2 sum_{n=1}^N (1 - n/(N+1)) c_n cos nθ,  c_n = τ(T_n(A/4)).
Usage: python3 fejer_lp.py cheb_coeffs_n256.txt"""
import sys, numpy as np
from common import load
c = load(sys.argv[1]); Nmax = max(c)
cc = np.array([c[n] for n in range(Nmax + 1)])
th = np.linspace(0, np.pi, 200001)
def F(N):
    s = np.ones_like(th)
    for n in range(1, N + 1):
        s += 2 * (1 - n / (N + 1)) * cc[n] * np.cos(n * th)
    return s
print("N | min F_N | ‖F_N‖_{1.5}^{1.5} | ‖F_N‖_2^2 | ‖F_N‖_3^3 | max F_N")
for N in [16, 32, 64, 128, 192, 256]:
    if N > Nmax: continue
    f = F(N)
    I = lambda p: np.trapezoid(np.abs(f) ** p, th) / np.pi
    print(f"{N:4d} | {f.min():+.2e} | {I(1.5):.5f} | {I(2):.5f} | {I(3):.4f} | {f.max():.3f}")
