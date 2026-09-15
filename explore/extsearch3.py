import sys, time
from math import isqrt

def factor(n):
    f={}
    d=2
    while d*d<=n:
        while n%d==0:
            f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f

def divs_from_fact(f):
    ds=[1]
    for p,e in f.items():
        ds=[a*p**k for a in ds for k in range(e+1)]
    return ds

def partners_of_square(n):
    """w>0 with n^4 + w^2 a perfect square: (z-w)(z+w)=n^4."""
    if n==0: return set()
    f=factor(n)
    f4={p:4*e for p,e in f.items()}
    N=n**4
    res=set()
    for d in divs_from_fact(f4):
        d2=N//d
        if d2<d: continue
        if (d2-d)%2==0:
            res.add((d2-d)//2)
    res.discard(0)
    return res

LMAX=int(sys.argv[1]) if len(sys.argv)>1 else 2000
t0=time.time()
cache={}
def P(n):
    v=cache.get(n)
    if v is None:
        v=partners_of_square(n); cache[n]=v
    return v

sols=[]
for L in range(1,LMAX+1):
    for p in range(-2*L, 3*L+1):
        if p==0 or p==L: continue
        S=P(abs(p)) & P(abs(L-p))
        if not S: continue
        for r in S:
            if r==0 or r==L: continue
            if (L-r) in S:
                sols.append((L,p,r))
    if L%200==0:
        print('L=%d sols=%d t=%.0fs'%(L,len(sols),time.time()-t0)); sys.stdout.flush()

print('DONE LMAX=%d non-boundary solutions found: %d'%(LMAX,len(sols)))
for L,p,r in sols[:60]:
    print('  L=%d x=%d/%d y=%d/%d interior=%s'%(L,p,L,r,L,(0<p<L) and (0<r<L)))
