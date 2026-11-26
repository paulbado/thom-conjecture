"""Round 8: deficits b_k = sum of widths over zero-area closed walks of length k (brute force)."""
import itertools
steps={'R':(1,0),'L':(-1,0),'U':(0,1),'D':(0,-1)}
for k in range(2,11,2):
    b=0; t=0
    for w in itertools.product('RLUD',repeat=k):
        x=y=0; a=0; xsv=[0]
        for s in w:
            dx,dy=steps[s]; a+=x*dy; x+=dx; y+=dy; xsv.append(x)
        if x==0 and y==0 and a==0:
            t+=1; b+=max(xsv)-min(xsv)
    print(k,t,b)
