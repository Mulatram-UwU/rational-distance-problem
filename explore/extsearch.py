from math import gcd, isqrt
from collections import defaultdict
import sys, time

LMAX = 400
LEG = 3*LMAX
t0=time.time()
partners = defaultdict(set)
mmax = isqrt(LEG)+1
# build partner relation: v*w with v^2+w^2 square, both <= LEG, w>0
for m in range(2, mmax+1):
    for n in range(1, m):
        if (m-n)%2==0: continue
        if gcd(m,n)!=1: continue
        l1=m*m-n*n; l2=2*m*n
        for k in range(1, LEG//max(l1,l2)+1):
            a=k*l1; b=k*l2
            if a>LEG or b>LEG: break
            partners[a].add(b); partners[b].add(a)
print('built partners up to',LEG,'legs:',len(partners),'t=%.1fs'%(time.time()-t0))
sys.stdout.flush()

sols=[]
for L in range(1,LMAX+1):
    # p from -L..2L ; legs A=p^2, B=(L-p)^2
    for p in range(-L, 2*L+1):
        if p==0 or p==L: continue
        A=p*p; B=(L-p)*(L-p)
        if A>LEG or B>LEG: continue
        S = partners[A] & partners[B]
        if not S: continue
        for r in S:
            if r==0 or r==L: continue
            if (L-r) in S:
                sols.append((L,p,r))
    if L%50==0:
        print('L=',L,'sols so far',len(sols),'t=%.0fs'%(time.time()-t0)); sys.stdout.flush()

print('LMAX=',LMAX,'non-boundary solutions:',len(sols))
seen=set()
for L,p,r in sols[:40]:
    print('  L=%d  x=%d/%d y=%d/%d   interior=%s'%(L,p,L,r,L,0<p<L and 0<r<L))
