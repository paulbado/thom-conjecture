import numpy as np, sys
M=int(sys.argv[1])
R=M+1           # a,b in [-R,R]
C=(M*M)//4+M+2  # c in [-C,C]
sa=2*R+1; sc=2*C+1
def zeros(): return np.zeros((sa,sa,sc))
def applyA(v):
    out=np.zeros_like(v)
    # right mult by x^{±1}: (a,b,c)->(a±1,b,c) ; value at h*g = v(h)
    out[1:,:,:]+=v[:-1,:,:]; out[:-1,:,:]+=v[1:,:,:]
    # right mult by y: (a,b,c)->(a,b+1,c+a); y^{-1}: (a,b,c)->(a,b-1,c-a)
    for ia in range(sa):
        a=ia-R
        sl=v[ia]
        if a>0:
            out[ia,1:,a:]+=sl[:-1,:-a]; out[ia,:-1,:-a]+=sl[1:,a:]
        elif a<0:
            k=-a
            out[ia,1:,:-k]+=sl[:-1,k:]; out[ia,:-1,k:]+=sl[1:,:-k]
        else:
            out[ia,1:,:]+=sl[:-1,:]; out[ia,:-1,:]+=sl[1:,:]
    return out
v0=zeros(); v0[R,R,C]=1.0
v1=applyA(v0)/4
res={0:1.0}
prev,cur=v0,v1
res[2]=2*np.vdot(v1,v1)-1
for m in range(1,M):
    nxt=applyA(cur)/2-prev
    res[2*(m+1)]=2*np.vdot(nxt,nxt)-1
    res[2*m+1]=2*np.vdot(cur,nxt)
    prev,cur=cur,nxt
    if m%10==0:
        print(m, flush=True, file=sys.stderr)
for n in sorted(res):
    print(n, repr(float(res[n])))
