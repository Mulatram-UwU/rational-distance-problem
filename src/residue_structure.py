#!/usr/bin/env python3
"""
residue_structure.py -- local (modular) structure of the four-square system.

The system:  integers A,B,C,D >= 1 with A+B = C+D = Q and
    A^2+C^2,  B^2+C^2,  A^2+D^2,  B^2+D^2   all perfect squares.
(This is the integer form of "point of the unit square at rational distance
from all four vertices"; see notes/reduction.md.)

For a modulus m we enumerate every quadruple (A,B,C,D) mod m satisfying
    A+B = C+D  (mod m)
    A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2  are quadratic residues mod m
and report
  * the set of possible Q = A+B mod m          -> what divides Q
  * whether p | A,B,C,D is forced for p | m    -> whether a p-descent exists
  * the possible parity patterns mod 4 and mod 8
This is a finite exact computation; the lemmas it confirms are proved by hand
in notes/reduction.md and formalised in lean/.
"""
from math import gcd

def qr_set(m):
    return { (x*x) % m for x in range(m) }

def analyse(m, verbose=True):
    QR = qr_set(m)
    possibleQ = set()
    forced_all_div = {}      # p -> True if p | A,B,C,D is forced
    primes = [p for p in range(2, m+1) if m % p == 0 and all(p % d for d in range(2, int(p**0.5)+1))]
    witness_not_all_div = {}
    count = 0
    for A in range(m):
        for B in range(m):
            Q = (A+B) % m
            for C in range(m):
                D = (Q - C) % m
                if (A*A + C*C) % m not in QR: continue
                if (B*B + C*C) % m not in QR: continue
                if (A*A + D*D) % m not in QR: continue
                if (B*B + D*D) % m not in QR: continue
                count += 1
                possibleQ.add(Q)
                for p in primes:
                    if not (A % p == 0 and B % p == 0 and C % p == 0 and D % p == 0):
                        witness_not_all_div.setdefault(p, (A,B,C,D,Q))
    if verbose:
        print(f"m={m}: {count} residue quadruples satisfy the conditions")
        print(f"   possible Q mod {m} : {sorted(possibleQ)}"
              f"  {'-> m | Q forced' if possibleQ == {0} else ''}")
        for p in primes:
            if p in witness_not_all_div:
                print(f"   p={p}: NO descent (witness (A,B,C,D,Q)={witness_not_all_div[p]})")
            else:
                print(f"   p={p}: descent! every solution has p | A,B,C,D")
    return possibleQ, witness_not_all_div, primes, count

if __name__ == "__main__":
    print("== powers of 2 and odd prime powers ==")
    for m in [2, 4, 8, 16, 32, 3, 9, 27, 5, 25, 7, 49, 11, 13]:
        analyse(m)
    print()
    print("== composite moduli ==")
    for m in [6, 12, 24, 48, 36, 72, 144, 60, 120, 168, 210]:
        analyse(m)
