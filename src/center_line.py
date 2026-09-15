#!/usr/bin/env python3
"""
center_line.py -- the case x = 1/2 of the rational-distance problem.

A point on the centre line has A = B = Q/2 and the four conditions collapse to
    A^2 + C^2 = square,  A^2 + D^2 = square,  C + D = Q = 2A .
With u = C/A (0 < u < 2) this is exactly (notes/reduction.md, Prop. 8):
    1 + u^2 = square    and    1 + (2-u)^2 = square .            (*)

Prop. 9 parametrises 1 + u^2 = w^2  by  u = (1/lam - lam)/2, lam = w - u != 0,
and turns (*) into rational points of the quartic
    nu^2 = DELTA(lam),  DELTA(lam) = lam^4 + 8 lam^3 + 18 lam^2 - 8 lam + 1 .

This script
  (1) verifies the identity DELTA(lam) = lam^2 * (v^2 + 8v + 20),  v = lam-1/lam,
      and the algebraic equivalence of (*) with the quartic, by exact rational
      arithmetic on many random lambdas;
  (2) exhaustively searches rational points of the quartic with
      lam = p/q, 1 <= |p|,q <= B  (integer arithmetic, no rounding);
  (3) exhaustively searches solutions of (*) directly with u = p/q, 1<=p,q<=B,
      as an independent check of the search engine on the centre line.
Report: exact counts; nothing is asserted beyond what the loops verify.
"""
import random
from fractions import Fraction
from math import isqrt

B = int(__import__("sys").argv[1]) if len(__import__("sys").argv) > 1 else 3000
SKIP_BIG = "--fast" in __import__("sys").argv


def delta(lam: Fraction) -> Fraction:
    return lam**4 + 8*lam**3 + 18*lam**2 - 8*lam + 1


def is_rat_square(x: Fraction):
    if x < 0:
        return None
    n, d = x.numerator, x.denominator
    rn, rd = isqrt(n), isqrt(d)
    if rn*rn == n and rd*rd == d:
        return Fraction(rn, rd)
    return None


print("== (1) algebraic identities, exact rational arithmetic ==")
random.seed(1)
ok_identity = ok_equiv = True
for _ in range(2000):
    lam = Fraction(random.randint(-50, 50), random.randint(1, 50))
    if lam == 0:
        continue
    v = lam - 1/lam
    if delta(lam) != lam**2 * (v**2 + 8*v + 20):
        ok_identity = False
        print("IDENTITY FAILS for", lam)
    # if nu^2 = Delta(lam) then u,2-u reproduce (*)
    nu = is_rat_square(delta(lam))
    if nu is not None:
        u = (1/lam - lam)/2
        w = is_rat_square(1 + u**2)
        mu = (-(lam**2 + 4*lam - 1) + nu) / (2*lam)
        u2 = (1/mu - mu)/2
        z = is_rat_square(1 + u2**2)
        if w is None or z is None or u + u2 != 2:
            ok_equiv = False
            print("EQUIVALENCE FAILS for", lam)
print("identity Delta(lam) = lam^2 (v^2+8v+20) holds on all samples:", ok_identity)
print("a quartic point yields (*):", ok_equiv, "(no random lambda happened to be a point)"
      if ok_equiv else "")

print("== (1b) same equivalence checked over finite fields (exact, many instances) ==")
def qr_mod(a, p):
    return pow(a % p, (p - 1) // 2, p) in (0, 1)
def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        r = pow(a, (p + 1) // 4, p)
        return r if r * r % p == a else None
    # Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while qr_mod(z, p):
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r
checked = bad = 0
for p in [p for p in range(101, 400) if all(p % d for d in range(2, int(p**0.5) + 1))]:
    for lam in range(1, p):
        d = (lam**4 + 8*lam**3 + 18*lam**2 - 8*lam + 1) % p
        if not qr_mod(d, p):
            continue
        nu = sqrt_mod(d, p)
        inv2l = pow(2 * lam % p, p - 2, p)
        for sgn in (1, -1):
            mu = (-(lam**2 + 4*lam - 1) + sgn * nu) * inv2l % p
            if mu == 0:
                continue
            u = (pow(lam, p - 2, p) - lam) * pow(2, p - 2, p) % p
            u2 = (pow(mu, p - 2, p) - mu) * pow(2, p - 2, p) % p
            checked += 1
            if (u + u2 - 2) % p != 0 or not qr_mod(1 + u*u, p) or not qr_mod(1 + u2*u2, p):
                bad += 1
                print("FINITE FIELD EQUIVALENCE FAILS", p, lam, sgn)
print(f"finite-field instances checked: {checked}, failures: {bad}")
print("   (each instance: Delta(lam) a square mod p => 1+u^2 and 1+(2-u)^2 are squares mod p)")

if SKIP_BIG:
    __import__("sys").exit(0)


print(f"== (2) rational points of nu^2 = DELTA(lam), lam = p/q, |p|,q <= {B} ==")
found = []
for q in range(1, B + 1):
    for p in range(-B, B + 1):
        if p == 0 or __import__("math").gcd(abs(p), q) != 1:
            continue
        # q^4 * DELTA(p/q) = p^4 + 8 p^3 q + 18 p^2 q^2 - 8 p q^3 + q^4
        val = p**4 + 8*p**3*q + 18*p**2*q**2 - 8*p*q**3 + q**4
        r = isqrt(val)
        if r*r == val:
            found.append((p, q, r))
print("rational points found (lam = p/q, nu = r/q^2):", len(found))
for f in found[:20]:
    print("   lam =", Fraction(f[0], f[1]), " nu =", Fraction(f[2], f[1]**2))
print("NOTE: lam and -1/lam give the same point (the quartic has that symmetry),")
print("      and no point is expected to satisfy the range conditions 0<u<2.")

print(f"== (3) direct search of (*): 1+u^2 and 1+(2-u)^2 squares, u = p/q <= {B} ==")
hits = []
for q in range(1, B + 1):
    for p in range(1, q):          # 0 < u < 1 is enough by the symmetry u <-> 2-u
        if __import__("math").gcd(p, q) != 1:
            continue
        n1 = p*p + q*q
        n2 = (2*q - p)**2 + q*q
        if is_rat_square(Fraction(n1, q*q)) is not None and \
           is_rat_square(Fraction(n2, q*q)) is not None:
            hits.append(Fraction(p, q))
print("centre-line solutions 0 < u < 1 found:", len(hits))
for h in hits[:20]:
    print("   u =", h)
