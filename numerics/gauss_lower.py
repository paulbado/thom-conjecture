"""Certified lower bounds for mu_A near E = 0 from exact moments (Chebyshev-Markov-Stieltjes).

If a measure mu has moments m_0..m_{2n-1} and x_1 < ... < x_n, w_1..w_n is its n-point Gauss
rule, then for nodes x_a < x_b:  mu((x_a, x_b)) >= sum_{a<k<b} w_k  (Markov-Stieltjes).
For n odd the symmetric measure mu_A has the node 0, so  mu_A((-x_+, x_+)) >= w_0, where x_+ is the
smallest positive node.  The moments tau(A^n) are exact integers (moments_exact_n120.txt), the
recurrence coefficients are computed in exact rational arithmetic, and the nodes and weights are
computed with mpmath at 60 digits, so the bounds are rigorous up to that (tiny) rounding.
These certify mass only at the scale x_+ ~ 1/n: moments of degree <= 120 see nothing finer.
Usage: python3 gauss_lower.py [Q]  (Q: compare with nu_Q([-x_+, x_+]) from nu_cdf_Q{Q}_M32768.npy)
"""
import ast, sys
from fractions import Fraction
import mpmath as mp
import numpy as np

mp.mp.dps = 60
m = [Fraction(int(v)) for v in ast.literal_eval(open("moments_exact_n120.txt").read())]
NM = len(m) - 1  # 120

# Exact Stieltjes/Lanczos via the moment functional on polynomials (coefficient lists).
def ip(p, q):
    s = Fraction(0)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    s += a * b * m[i + j]
    return s

def xmul(p):
    return [Fraction(0)] + p

nmax = NM // 2  # Gauss rules with up to nmax nodes need moments up to 2*nmax - 1 <= NM
alpha, beta = [], []
p_prev, p_cur = [Fraction(0)], [Fraction(1)]
n_prev = Fraction(1)
norm_cur = ip(p_cur, p_cur)
for k in range(nmax):
    xp = xmul(p_cur)
    a = ip(xp, p_cur) / norm_cur
    alpha.append(a)
    if k + 1 == nmax:
        break
    b = norm_cur / n_prev if k > 0 else Fraction(0)
    nxt = [Fraction(0)] * (len(xp))
    for i, c in enumerate(xp):
        nxt[i] += c
    for i, c in enumerate(p_cur):
        nxt[i] -= a * c
    for i, c in enumerate(p_prev):
        nxt[i] -= b * c
    p_prev, p_cur, n_prev = p_cur, nxt, norm_cur
    norm_cur = ip(p_cur, p_cur)
    beta.append(norm_cur / n_prev)  # beta_{k+1} = ||p_{k+1}||^2 / ||p_k||^2

def gauss(n):
    J = mp.zeros(n, n)
    for i in range(n):
        J[i, i] = mp.mpf(alpha[i].numerator) / alpha[i].denominator
        if i + 1 < n:
            b = mp.sqrt(mp.mpf(beta[i].numerator) / beta[i].denominator)
            J[i, i + 1] = J[i + 1, i] = b
    E, Q = mp.eigsy(J)
    return [E[i] for i in range(n)], [Q[0, i] ** 2 for i in range(n)]

cdf = None
if len(sys.argv) > 1:
    Qf = int(sys.argv[1])
    cdf = np.load(f"nu_cdf_Q{Qf}_M32768.npy"); grid = np.linspace(-4, 4, cdf.size)
print("n  x_+ (smallest positive node)  w_0 = certified lower bound for mu_A((-x_+,x_+))"
      "  w_0*log^2(1/x_+)" + ("  nu_Q((-x_+,x_+))" if cdf is not None else ""))
for n in range(3, nmax + 1, 2):
    X, W = gauss(n)
    i0 = min(range(n), key=lambda i: abs(X[i]))
    xp = min(x for x in X if x > 1e-30)
    w0 = W[i0]
    line = f"{n:3d}  {float(xp):.5f}  {float(w0):.5f}  {float(w0 * mp.log(1 / xp) ** 2):.4f}"
    if cdf is not None:
        line += f"  {np.interp(float(xp), grid, cdf) - np.interp(-float(xp), grid, cdf):.5f}"
    print(line)
