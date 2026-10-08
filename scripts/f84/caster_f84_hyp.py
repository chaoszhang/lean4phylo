"""Does (D)/(XA)/(XB) need `piR + piY = 1`?  (Decides the Lean hypotheses.)

Uses the literal Lean definitions of `patt4/mon/.../Ew/EwA/EwB` with FREE (sm,rm) atoms,
so the answer is about the algebraic identity, not about probabilities.
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)


def Bmat(pi):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B


def K(B, pi, smv, rmv):
    Pi = np.tile(pi, (4, 1))
    return Pi + smv * (B - Pi) + rmv * (np.eye(4) - B)


def P4(B, pi, sms, rms):
    K1, K2, Kx, K3, K4 = (K(B, pi, sms[n], rms[n]) for n in range(5))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', K1[p], K2[p], Kx[p, q] * K3[q], K4[q])
    return P


def agg(P, pi, kind):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    idx = {'diag': lambda i, j, k, l: (i, j, k, l),
           'A': lambda i, j, k, l: (i, k, j, l),
           'B': lambda i, j, k, l: (i, k, l, j)}[kind]
    Q = lambda i, j, k, l: P[tuple(idx(i, j, k, l))]
    mon = lambda U, V: sum(Q(i, i, j, j) for i in U for j in V)
    pm = lambda U, V: sum(Q(i, j, k, k) for i in U for j in U for k in V)
    mp = lambda U, V: sum(Q(i, i, k, l) for i in U for k in V for l in V)
    pa = lambda U, V: sum(Q(i, j, k, l) for i in U for j in U for k in V for l in V)
    return (pR ** 2 * pY ** 2 / 4 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR / 4 * (pm(R, Y) + mp(Y, R))
            - pR ** 2 * sqY / 4 * (mp(R, Y) + pm(Y, R))
            + sqR * sqY / 4 * (pa(R, Y) + pa(Y, R)))


def Cv(pi, sms, rms):
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    return 2 * pA * pC * pG * pT * pR * pY * (1 - sms[2]) * rms[0] * rms[1] * rms[3] * rms[4]


rng = np.random.default_rng(99)
print("=== UNNORMALISED pi (no piR+piY=1) ===")
w = [0.0, 0.0, 0.0]
spread = 0.0
for _ in range(200):
    pi = rng.random(4) + 0.2                      # NOT normalised on purpose
    B = Bmat(pi)
    sms, rms = rng.random(5) * 2 - 0.7, rng.random(5) * 2 - 0.7
    P = P4(B, pi, sms, rms)
    c = Cv(pi, sms, rms)
    w[0] = max(w[0], abs(agg(P, pi, 'diag') / c - 1))
    w[1] = max(w[1], abs(agg(P, pi, 'A')) / abs(c))
    w[2] = max(w[2], abs(agg(P, pi, 'B')) / abs(c))
print("  (D)  max |ratio-1| =", w[0])
print("  (XA) max |v|/C     =", w[1])
print("  (XB) max |v|/C     =", w[2])

print("=== NORMALISED pi ===")
w = [0.0, 0.0, 0.0]
for _ in range(200):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    B = Bmat(pi)
    sms, rms = rng.random(5) * 2 - 0.7, rng.random(5) * 2 - 0.7
    P = P4(B, pi, sms, rms)
    c = Cv(pi, sms, rms)
    w[0] = max(w[0], abs(agg(P, pi, 'diag') / c - 1))
    w[1] = max(w[1], abs(agg(P, pi, 'A')) / abs(c))
    w[2] = max(w[2], abs(agg(P, pi, 'B')) / abs(c))
print("  (D)  max |ratio-1| =", w[0])
print("  (XA) max |v|/C     =", w[1])
print("  (XB) max |v|/C     =", w[2])
