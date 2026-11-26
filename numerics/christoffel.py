import sys, numpy as np
c={}
for line in open(sys.argv[1]):
    n,v=line.split(); c[int(n)]=float(v)
N=max(c)
print("deg  lambda_deg(0)  (upper bound for mu{0});  min eig of Gram")
for J in [1,2,4,6,8,10,12,16,20,25,30,35,40,45,49,55,60,63]:
    if 4*J>N: break
    G=np.array([[(c[2*i+2*k]+c[2*abs(i-k)])/2 for k in range(J+1)] for i in range(J+1)])
    v=np.array([(-1.0)**i for i in range(J+1)])
    lam=1/(v@np.linalg.solve(G,v))
    print(2*J, f"{lam:.6e}", f"{np.linalg.eigvalsh(G).min():.2e}")
