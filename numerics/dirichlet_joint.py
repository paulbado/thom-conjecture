"""Round 7, Task 5 (supplement): joint flux/phase transversality and energy-localized
coarea bounds for the Dirichlet model H_L(α,θ) (see dirichlet.py for the model).

For random (α,θ,k) it reports quantiles of |∂θE| and |∂αE|/L, their correlation, the joint
small-set share, and the coarea bound R_L split by energy band |E| < 0.25, 0.25 ≤ |E| < 1,
|E| ≥ 1 (each band's mean of log(M_L/(L|∂αE|)) and its mass share).
Usage: python3 dirichlet_joint.py L samples gridfactor
"""
import sys, numpy as np
sys.argv += []
L = int(sys.argv[1]); S = int(sys.argv[2]); gf = int(sys.argv[3])
import importlib.util
spec = importlib.util.spec_from_file_location("dm", __file__.replace("dirichlet_joint.py", "dirichlet.py"))
rng = np.random.default_rng(11)
j = np.arange(1, L + 1)
def H(a, t):
    return np.diag(2*np.cos(2*np.pi*(t + j*a))) + np.diag(np.ones(L-1), 1) + np.diag(np.ones(L-1), -1)
def eig_der(a, t):
    E, U = np.linalg.eigh(H(a, t)); s = np.sin(2*np.pi*(t + j*a))
    return E, -4*np.pi*((j*s) @ (U**2)), -4*np.pi*(s @ (U**2))
G = gf*L*L; agrid = (np.arange(G) + 0.5)/G
def count_below(E, ag, t):
    if len(ag) > 8192:
        return np.concatenate([count_below(E, ag[i:i+8192], t) for i in range(0, len(ag), 8192)])
    d = 2*np.cos(2*np.pi*(t + np.outer(ag, j))); q = d[:, 0] - E; n = (q < 0).astype(int)
    for i in range(1, L):
        q = np.where(q == 0, 1e-300, q); q = d[:, i] - E - 1.0/q; n += (q < 0)
    return n
def M_count(E, t):
    n = count_below(E, agrid, t); return int(np.sum(n != np.roll(n, 1)))
# joint transversality (cheap, many samples)
A, T = [], []
for _ in range(2000):
    a, t = rng.random(2); E, dA, dT = eig_der(a, t); k = rng.integers(L)
    A.append(abs(dA[k])/L); T.append(abs(dT[k]))
A = np.array(A); T = np.array(T)
qa = np.quantile(A, [.1, .5, .9]); qt = np.quantile(T, [.1, .5, .9])
c = np.corrcoef(np.log(A + 1e-300), np.log(T + 1e-300))[0, 1]
eps = np.median(np.maximum(A, T)) / 10
print(f"L = {L}")
print(f"  |∂αE|/L quantiles 10/50/90%: {qa[0]:.3g} {qa[1]:.3g} {qa[2]:.3g};  |∂θE|: {qt[0]:.3g} {qt[1]:.3g} {qt[2]:.3g}")
print(f"  |∂αE| median {np.median(A)*L:.3g};  corr(log|∂αE|, log|∂θE|) = {c:.3f}")
print(f"  share with both < median(max)/10: {np.mean((A < eps) & (T < eps)):.4f}  "
      f"(α alone {np.mean(A < eps):.4f}, θ alone {np.mean(T < eps):.4f})")
# energy-localized coarea bound
rows = []
for _ in range(S):
    a, t = rng.random(2); k = rng.integers(L); E, dA, dT = eig_der(a, t)
    rows.append((E[k], np.log(M_count(E[k], t)/(L*abs(dA[k])))))
rows = np.array(rows)
for lo, hi in [(0, .25), (.25, 1), (1, 9)]:
    m = (np.abs(rows[:, 0]) >= lo) & (np.abs(rows[:, 0]) < hi)
    print(f"  band {lo} ≤ |E| < {hi}: mass {m.mean():.3f}, mean log ratio {rows[m, 1].mean():.3f}, "
          f"contribution {rows[m, 1].sum()/len(rows):.3f}")
print(f"  total R_L (θ-averaged Monte Carlo): {rows[:, 1].mean():.3f}")
