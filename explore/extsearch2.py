from math import isqrt
import sys, time

def partners_of_square(n):
    """All w>0 with n^4 + w^2 a perfect square. Uses (z-w)(z+w)=n^4."""
    N = n**4
    res=set()
    # enumerate divisor pairs d1*d2=N, d1<=d2, same parity
    d=1
    while d*d<=N:
        if N % d == 0:
            d2=N//d
            if (d2-d)%2==0:
                w=(d2-d)//2
                if w>0: res.add(w)
        d+=1
    return res

LMAX=1000
t0=time.time()
cache={}
def P(n):
    if n not in cache: cache[n]=partners_of_square(n)
    return cache[n]

sols=[]
for L in range(1,LMAX+1):
    pmax=2*L
    for p in range(-L, pmax+1):
        if p==0 or p==L: continue      # boundary cases excluded
        S = P(abs(p)) & P(abs(L-p))
        if not S: continue
        for r in S:
            if r==0 or r==L: continue
            if (L-r) in S:
                sols.append((L,p,r))
    if L%100==0:
        print('L=',L,'sols',len(sols),'t=%.0fs'%(time.time()-t0)); sys.stdout.flush()

print('LMAX',LMAX,'TOTAL non-boundary solutions:',len(sols))
for L,p,r in sols[:50]:
    inter = (0<p<L) and (0<r<L)
    print('  L=%d  x=%d/%d  y=%d/%d  interior=%s'%(L,p,L,r,L,inter))
