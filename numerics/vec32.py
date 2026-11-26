import numpy as np, sys
# float32, in-place variant of vec.py: c_n for n <= 2M
M=int(sys.argv[1])
R=M+1
C=(M*M)//4+M+2
sa=2*R+1; sc=2*C+1
dt=np.float32
def applyA(v,out):
    out[...]=0
    out[1:,:,:]+=v[:-1,:,:]; out[:-1,:,:]+=v[1:,:,:]
    for ia in range(sa):
        a=ia-R; sl=v[ia]; o=out[ia]
        if a>0:
            o[1:,a:]+=sl[:-1,:-a]; o[:-1,:-a]+=sl[1:,a:]
        elif a<0:
            k=-a
            o[1:,:-k]+=sl[:-1,k:]; o[:-1,k:]+=sl[1:,:-k]
        else:
            o[1:,:]+=sl[:-1,:]; o[:-1,:]+=sl[1:,:]
def dot(u,w):
    return float(sum(np.dot(u[i].ravel().astype(np.float64),w[i].ravel().astype(np.float64)) for i in range(sa)))
prev=np.zeros((sa,sa,sc),dt); prev[R,R,C]=1.0
cur=np.zeros((sa,sa,sc),dt); out=np.zeros((sa,sa,sc),dt)
applyA(prev,cur); cur*=0.25
res={0:1.0,1:0.0}
res[2]=2*dot(cur,cur)-1
for m in range(1,M):
    applyA(cur,out)
    prev*=-1; out*=0.5; prev+=out   # prev := A cur/2 - prev  (= next)
    nxt=prev
    res[2*(m+1)]=2*dot(nxt,nxt)-1
    res[2*m+1]=2*dot(cur,nxt)
    prev,cur=cur,nxt
    if m%8==0: print(m,flush=True,file=sys.stderr)
for n in sorted(res): print(n, repr(res[n]))
