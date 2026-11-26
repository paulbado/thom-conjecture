import sys
from collections import defaultdict
from fractions import Fraction
N=int(sys.argv[1])
# state: (x,y,A) -> count ; U at x adds x, D subtracts x
cur={ (0,0,0):1 }
m=[1]
for n in range(1,N+1):
    nxt=defaultdict(int)
    for (x,y,A),c in cur.items():
        # prune: remaining steps must be able to return
        nxt[(x+1,y,A)]+=c; nxt[(x-1,y,A)]+=c
        nxt[(x,y+1,A+x)]+=c; nxt[(x,y-1,A-x)]+=c
    rem=N-n
    cur={k:v for k,v in nxt.items() if abs(k[0])+abs(k[1])<=rem}
    m.append(cur.get((0,0,0),0))
print(m)
