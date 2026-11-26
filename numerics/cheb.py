import sys, ast
from fractions import Fraction
m=ast.literal_eval(open(sys.argv[1]).read())
N=len(m)-1
# Chebyshev T coefficients
T=[[1],[0,1]]
for n in range(2,N+1):
    a=[0]+[2*c for c in T[n-1]]
    b=T[n-2]+[0]*(len(a)-len(T[n-2]))
    T.append([x-y for x,y in zip(a,b)])
c=[]
for n in range(N+1):
    s=sum(Fraction(T[n][k]*m[k],4**k) for k in range(len(T[n])))
    c.append(s)
S=0
for n in range(1,N+1):
    if n%2==0:
        S+=c[n]**2
        print(n, float(c[n]), float(S), float(c[n])*n**0.5 , float(c[n])*n)
