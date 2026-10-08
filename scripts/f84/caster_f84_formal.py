"""DECISIVE: are the F84 identities *rational* identities in the symbols (sm_t, rm_t, pi_j)?

If yes, the Lean proof needs NO exponential algebra at all: expand the Fin-4 sums, `field_simp`, `ring`.
(sm_t = e^{-lam t}, rm_t = e^{-lam(1+kap)t} are then only *instantiations*.)

Fixes two bugs of caster_f84_algstruct.py:
  * Cval wrongly included rm_lx (the closed form has rm over the four LEAF lengths only);
  * the leaf-permutation test indexed the leaf slots wrongly (a permutation of leaves acts on
    slots (0,1,3,4), not (0,1,2,3)).
"""
import numpy as np
from itertools import product, permutations

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(20260110)


def setup(pi):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, pR, pY


def K_alg(B, pi, smv, rmv):
    Pi = np.tile(pi, (4, 1))
    return Pi + smv * (B - Pi) + rmv * (np.eye(4) - B)


def dist(B, pi, sms, rms):
    """sms, rms indexed [leaf1,leaf2,internal,leaf3,leaf4] -- FREE symbols."""
    K1, K2, Kx, K3, K4 = (K_alg(B, pi, sms[n], rms[n]) for n in range(5))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', K1[p], K2[p], Kx[p, q] * K3[q], K4[q])
    return P


def aggregate(P, pi, kind):
    """kind = 'diag' (sides (0,1),(2,3)), 'A' (sides (0,2),(1,3)), 'B' (sides (0,3),(1,2))."""
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    if kind == 'diag':
        idx = lambda i, j, k, l: (i, j, k, l)
    elif kind == 'A':
        idx = lambda i, j, k, l: (i, k, j, l)
    else:
        idx = lambda i, j, k, l: (i, k, l, j)

    def P4(i, j, k, l):
        return P[idx(i, j, k, l)]
    mon = lambda U, V: sum(P4(i, i, j, j) for i in U for j in V)
    pureMon = lambda U, V: sum(P4(i, j, k, k) for i in U for j in U for k in V)
    monPure = lambda U, V: sum(P4(i, i, k, l) for i in U for k in V for l in V)
    pureAll = lambda U, V: sum(P4(i, j, k, l) for i in U for j in U for k in V for l in V)
    return (pR ** 2 * pY ** 2 / 4 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR / 4 * (pureMon(R, Y) + monPure(Y, R))
            - pR ** 2 * sqY / 4 * (monPure(R, Y) + pureMon(Y, R))
            + sqR * sqY / 4 * (pureAll(R, Y) + pureAll(Y, R)))


def Cval(pi, sms, rms):
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    return (2 * pA * pC * pG * pT * pR * pY * (1 - sms[2]) * rms[0] * rms[1] * rms[3] * rms[4])


print("=== FREE sm/rm symbols (independent random numbers, unrelated to any exponential) ===")
wd = wA = wB = wsym = 0.0
for _ in range(200):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    B, pR, pY = setup(pi)
    sms = rng.random(5) * 3 - 1.0          # deliberately includes negatives
    rms = rng.random(5) * 3 - 1.0
    P = dist(B, pi, sms, rms)
    Cv = Cval(pi, sms, rms)
    wd = max(wd, abs(aggregate(P, pi, 'diag') / Cv - 1))
    wA = max(wA, abs(aggregate(P, pi, 'A')))
    wB = max(wB, abs(aggregate(P, pi, 'B')))
    # leaf symmetry: permute the leaf (sm,rm) pairs
    for perm in permutations(range(4)):
        s2 = [0.0] * 5
        r2 = [0.0] * 5
        slots = [0, 1, 3, 4]
        for a, b in zip(slots, perm):
            s2[a], r2[a] = sms[slots[b]], rms[slots[b]]
        s2[2], r2[2] = sms[2], rms[2]
        P2 = dist(B, pi, s2, r2)
        v1 = aggregate(P, pi, 'diag')
        v2 = aggregate(P2, pi, 'diag')
        if abs(v1) > 1e-9:
            wsym = max(wsym, abs(v2 - v1) / abs(v1))

print("  (D) diag / C                    : max |ratio-1| =", wd)
print("  (XA) crossA                     : max |value|   =", wA)
print("  (XB) crossB                     : max |value|   =", wB)
print("  leaf-permutation symmetry of (D): max rel       =", wsym)

print()
print("=== exponential instantiation (sanity: same numbers as before) ===")
wd2 = wA2 = wB2 = 0.0
for _ in range(200):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, pR, pY = setup(pi)
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    ts = rng.random(5) + 0.1
    sms, rms = np.exp(-lam * ts), np.exp(-lam * (1 + kappa) * ts)
    P = dist(B, pi, sms, rms)
    Cv = Cval(pi, sms, rms)
    wd2 = max(wd2, abs(aggregate(P, pi, 'diag') / Cv - 1))
    wA2 = max(wA2, abs(aggregate(P, pi, 'A')) / abs(Cv))
    wB2 = max(wB2, abs(aggregate(P, pi, 'B')) / abs(Cv))
print("  (D) diag / C   : max |ratio-1| =", wd2)
print("  (XA) crossA /C : max |value|/C =", wA2)
print("  (XB) crossB /C : max |value|/C =", wB2)
