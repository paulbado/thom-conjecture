"""Round 6, Task 5: cross-flux structure of the finite chiral model.

For N odd, H3(Z/N) decomposes into the N^2 chain operators H_{p,t} on Z/N (ThomZeroLevel.Chain):
  (H xi)(l) = c(l-1) xi(l-1) + conj(c(l)) xi(l+1),   c(n) = 1 + exp(2 pi i (t + p(n+1))/N).
For gcd(p,N)=1 the spectrum of H_{p,t} does not depend on t (translation by one site maps
t -> t+p), so the vertex measure is the flux average  sigma_N = (1/N) sum_p nu_p,
nu_p = normalized eigenvalue counting measure of H_{p,0}  (p = 0 averaged over t).

Outputs
 (A) moment check against the exact zero-area walk counts;
 (B) mass of [-h,h]: total, and the share coming from fluxes near rationals a/q;
 (C) Fejer entropy of flux-window mixtures.  By convexity of x log x, for a partition of the
     fluxes into windows W_b of width eta,
        Ent_K(sigma_N) <= sum_b w_b Ent_K(sigma_b),   sigma_b = average of nu_p over W_b,
     an exact inequality (Fejer smoothing is linear).  eta = 1/N is the flux-wise bound,
     eta = 1 is the full average.  We report how wide the windows must be.
Usage: python3 cross_flux.py N [Kmax]
"""
import sys, numpy as np
from math import gcd

N = int(sys.argv[1])
assert N % 2 == 1

def chain(p, t):
    n = np.arange(N)
    c = 1 + np.exp(2j * np.pi * (t + p * (n + 1)) / N)
    H = np.zeros((N, N), complex)
    H[(n + 1) % N, n] = c                 # H[l, l-1] = c(l-1)
    H[n, (n + 1) % N] = np.conj(c)        # H[l, l+1] = conj(c(l))
    return H

# ev[p] = spectrum of H_{p,0} for p >= 1; p = 0 is averaged over t (ev0, N^2 values)
import os
cache = os.environ.get("CROSS_FLUX_CACHE")   # optional .npz cache of the spectra
if cache and os.path.exists(cache):
    z = np.load(cache); ev, ev0 = z["ev"], z["ev0"]
else:
    ev = np.zeros((N, N))
    for p in range(1, N):
        assert gcd(p, N) == 1
        ev[p] = np.linalg.eigvalsh(chain(p, 0))
    ev0 = np.concatenate([np.linalg.eigvalsh(chain(0, t)) for t in range(N)])
    if cache:
        np.savez(cache, ev=ev, ev0=ev0)
def per_flux(f):  # per-flux mean of f(eigenvalue), p = 0 averaged over t
    out = np.mean(f(ev), axis=1)
    out[0] = np.mean(f(ev0))
    return out

MOM = [1, 0, 4, 0, 28, 0, 232, 0, 2156, 0, 21944, 0, 240280]
print(f"N = {N}")
print("(A) moments of sigma_N vs zero-area walk counts (exact for (k+1)^2 <= N)")
for k in range(0, 13, 2):
    print(f"   k={k:2d}  sigma_N: {per_flux(lambda x: x ** k).mean():14.4f}   exact: {MOM[k]}")

alpha = np.arange(N) / N
def near(q):  # distance of the flux to the nearest primitive a/q (gcd(a,q) = 1)
    pts = np.array([a / q for a in range(q + 1) if gcd(a, q) == 1])
    return np.min(np.abs(alpha[:, None] - pts[None, :]), axis=1)

print("(B) sigma_N([-h,h]) and the share from flux windows |alpha - a/q| <= eta (primitive a/q)")
for q, eta in ((2, 0.05), (4, 0.02), (6, 0.01)):
    print(f"   window q={q}, eta={eta} holds {np.mean(near(q) <= eta):.3f} of the fluxes")
for h in [2.0 ** -k for k in (3, 4, 5, 6, 7, 8, 9, 10)]:
    m = per_flux(lambda x: np.abs(x) <= h)          # per-flux mass nu_p([-h,h])
    tot = m.mean()
    L = np.log(1 / h)
    row = f"   h=2^{int(-np.log2(h)):d}  mass={tot:.4e}  mass*log^2(1/h)={tot * L * L:.4f}"
    for q, eta in ((2, 0.05), (4, 0.02), (6, 0.01)):
        sel = near(q) <= eta
        row += f"  q={q},eta={eta}: {m[sel].sum() / m.sum():.3f}"
    print(row)

print("(C) Fejer entropy Ent_K of flux-window mixtures (degree K Fejer density of theta_* sigma)")
grid = (np.arange(4000) + 0.5) / 4000
Kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 66
th = lambda x: np.arccos(np.clip(x / 4, -1, 1)) / np.pi
A = np.stack([per_flux(lambda x: np.cos(np.pi * n * th(x))) for n in range(Kmax)], axis=1)  # N x Kmax
C = np.cos(np.pi * np.outer(np.arange(Kmax), grid))     # Kmax x grid
def ent(a, K):
    w = np.zeros(Kmax); w[:K] = 1 - np.arange(K) / K
    g = 1 + 2 * ((a[1:] * w[1:]) @ C[1:])
    g = np.maximum(g, 1e-300)
    return np.mean(g * np.log(g))
for K in [k for k in (8, 16, 32, 64, 128) if k <= Kmax - 2]:
    row = f"   K={K:2d}  full average: {ent(A.mean(0), K):.4f}  windows:"
    for B in (2, 4, 8, 16, 32, 64, 128):
        bins = (np.arange(N) * B) // N
        tot = 0.0
        for b in range(B):
            s = bins == b
            tot += s.mean() * ent(A[s].mean(0), K)
        row += f"  eta=1/{B}: {tot:.3f}"
    flux = np.mean([ent(A[p], K) for p in range(N)])
    print(row + f"  flux-wise: {flux:.3f}")

print("(D) weighted Fejer energy  W_K = ||Fejer_K density of (E/4)^2 mu / arcsine||^2  (Jensen: same")
print("    window inequality W_K(sigma) <= sum_b w_b W_K(sigma_b); WeightedTarget <=> sup_K W_K < oo)")
def wen(a, K):
    n = np.arange(K)
    b = (2 * a[n] + a[n + 2] + a[np.abs(n - 2)]) / 4      # Chebyshev coefficients of x^2 mu
    f = (1 - n / K) ** 2 * b ** 2
    return f[0] + 2 * f[1:].sum()
for K in [k for k in (8, 16, 32, 64, 128) if k <= Kmax - 2]:
    row = f"   K={K:3d}  full average: {wen(A.mean(0), K):.4f}  windows:"
    for B in (4, 16, 64):
        bins = (np.arange(N) * B) // N
        row += f"  eta=1/{B}: {sum((bins == b).mean() * wen(A[bins == b].mean(0), K) for b in range(B)):.3f}"
    print(row + f"  flux-wise: {np.mean([wen(A[p], K) for p in range(N)]):.3f}")
