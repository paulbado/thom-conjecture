"""Shared helpers: load c_n, weighted coefficients d_n, Jackson-damped (KPM) densities."""
import numpy as np

def load(path):
    c = {}
    for line in open(path):
        n, v = line.split()
        c[int(n)] = float(v)
    c.setdefault(1, 0.0)
    return c

def weighted(c):
    """d_n = (c_{n-2} + 2 c_n + c_{n+2}) / 4, with c_{-k} = c_k; valid for n <= max-2."""
    N = max(c)
    cs = lambda n: c[abs(n)]
    return {n: (cs(n - 2) + 2 * cs(n) + cs(n + 2)) / 4 for n in range(0, N - 1)}

def jackson(N):
    n = np.arange(N + 1); a = np.pi / (N + 2)
    return ((N - n + 2) * np.cos(n * a) + np.sin(n * a) / np.tan(a)) / (N + 2)

def density(coef, N, E):
    """Jackson-smoothed density w.r.t. the arcsine law: coef_0 + 2 sum g_n coef_n T_n(E/4)."""
    g = jackson(N); th = np.arccos(np.clip(E / 4, -1, 1))
    s = np.ones_like(E) * coef[0] * g[0]
    for n in range(1, N + 1):
        s += 2 * g[n] * coef[n] * np.cos(n * th)
    return s
