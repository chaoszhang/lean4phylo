"""Independent verification of t42's claim + derivation of the *algebraic* structure of F84's PropA.

Two questions:
  Q1. Is `Ew` (Lean-literal, `Phylo/Stat/CASTERF84Events.lean`) totally symmetric in (t1,t2,t3,t4)?
      -> if so, EwF84 = EwF84_ac = EwF84_ad and interface statement (1) is FALSE.   [see caster_f84_leancheck.py]
  Q2. Is the true structure `E[w(tau) | gene tree G] = C * [tau = topo(G)]`
      with C = 2 piA piC piG piT pR pY (1 - sm lx) rmL  (divide-by-4 normalisation)?

Q3 (the decisive one for formalisation): is the identity an identity of *rational functions*
    in the symbols (sm_t, rm_t)_{t in {t1,t2,tx,t3,t4}}, i.e. valid for ARBITRARY sm/rm,
    not only for sm_t = e^{-lam t}, rm_t = e^{-lam(1+kap)t}?
    -> if yes, `field_simp; ring` can close everything and no exponential algebra is needed.
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(4242)


def setup(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, lam, pR, pY


def K_alg(B, pi, smv, rmv):
    """K_ij = pi_j + sm*(B_ij - pi_j) + rm*(delta_ij - B_ij)  -- sm,rm FREE symbols."""
    Pi = np.tile(pi, (4, 1))
    return Pi + smv * (B - Pi) + rmv * (np.eye(4) - B)


def patt4(B, pi, sms, rms, i, j, k, l):
    """(t1,t2,tx,t3,t4) -> probability of pattern (i,j,k,l) on the ab|cd gene tree."""
    K1, K2, Kx, K3, K4 = (K_alg(B, pi, sms[n], rms[n]) for n in range(5))
    return sum(pi[p] * K1[p, i] * K2[p, j] * Kx[p, q] * K3[q, k] * K4[q, l]
               for p in range(4) for q in range(4))


def distribution(B, pi, sms, rms):
    return {(i, j, k, l): patt4(B, pi, sms, rms, i, j, k, l)
            for i, j, k, l in product(range(4), repeat=4)}


def Ew_of(P, pi, grouping, div4=True):
    """`grouping` = the two *leaf pairs* used by the weight table, as index pairs into (a,b,c,d).

    grouping = ((0,1),(2,3))  -> diagonal (tau = ab|cd)
    grouping = ((0,2),(1,3))  -> tau = ac|bd
    grouping = ((0,3),(1,2))  -> tau = ad|bc
    """
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2

    def ev(i, j, k, l):
        s = [0] * 4
        s[grouping[0][0]], s[grouping[0][1]] = i, j
        s[grouping[1][0]], s[grouping[1][1]] = k, l
        return P[tuple(s)]
    mon = lambda U, V: sum(ev(i, i, j, j) for i in U for j in V)
    pureMon = lambda U, V: sum(ev(i, j, k, k) for i in U for j in U for k in V)
    monPure = lambda U, V: sum(ev(i, i, k, l) for i in U for k in V for l in V)
    pureAll = lambda U, V: sum(ev(i, j, k, l) for i in U for j in U for k in V for l in V)
    c = 0.25 if div4 else 1.0
    return (c * pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - c * pY ** 2 * sqR * (pureMon(R, Y) + monPure(Y, R))
            - c * pR ** 2 * sqY * (monPure(R, Y) + pureMon(Y, R))
            + c * sqR * sqY * (pureAll(R, Y) + pureAll(Y, R)))


def Ew_families(P, pi, grouping):
    """the 8 signed contributions, as {name: value}"""
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2

    def ev(i, j, k, l):
        s = [0] * 4
        s[grouping[0][0]], s[grouping[0][1]] = i, j
        s[grouping[1][0]], s[grouping[1][1]] = k, l
        return P[tuple(s)]
    mon = lambda U, V: sum(ev(i, i, j, j) for i in U for j in V)
    pureMon = lambda U, V: sum(ev(i, j, k, k) for i in U for j in U for k in V)
    monPure = lambda U, V: sum(ev(i, i, k, l) for i in U for k in V for l in V)
    pureAll = lambda U, V: sum(ev(i, j, k, l) for i in U for j in U for k in V for l in V)
    U, V = R, Y
    return {
        'pR2pY2*mon(R,Y)': pR ** 2 * pY ** 2 * mon(U, V),
        'pR2pY2*mon(Y,R)': pR ** 2 * pY ** 2 * mon(V, U),
        '-pY2qR*pureMon(R,Y)': -pY ** 2 * sqR * pureMon(U, V),
        '-pY2qR*monPure(Y,R)': -pY ** 2 * sqR * monPure(V, U),
        '-pR2qY*monPure(R,Y)': -pR ** 2 * sqY * monPure(U, V),
        '-pR2qY*pureMon(Y,R)': -pR ** 2 * sqY * pureMon(V, U),
        'qRqY*pureAll(R,Y)': sqR * sqY * pureAll(U, V),
        'qRqY*pureAll(Y,R)': sqR * sqY * pureAll(V, U),
    }


# ============================ Q3: "free sm/rm" test ============================
print("=== Q3: is the identity rational in (sm,rm) symbols? (arbitrary sm,rm, NOT exponentials) ===")
worst_diag = worst_cross = worst_sym = 0.0
for _ in range(60):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    sms = rng.random(5) * 0.9 + 0.05      # arbitrary, unrelated to exp
    rms = rng.random(5) * 0.9 + 0.05
    P = distribution(B, pi, sms, rms)
    pA, pG, pC, pT = pi
    Cval = 2 * pA * pC * pG * pT * pR * pY * (1 - sms[2]) * np.prod(rms)
    d = Ew_of(P, pi, ((0, 1), (2, 3)))
    x1 = Ew_of(P, pi, ((0, 2), (1, 3)))
    x2 = Ew_of(P, pi, ((0, 3), (1, 2)))
    worst_diag = max(worst_diag, abs(d / Cval - 1))
    worst_cross = max(worst_cross, abs(x1) / max(1e-300, abs(Cval)),
                      abs(x2) / max(1e-300, abs(Cval)))

# also: is Ew still totally symmetric in the leaf *labels* with free sm/rm?
for _ in range(30):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    B, _, _, _ = setup(pi, 0.7)
    sms = rng.random(5) * 0.9 + 0.05
    rms = rng.random(5) * 0.9 + 0.05
    P = distribution(B, pi, sms, rms)
    base = Ew_of(P, pi, ((0, 1), (2, 3)))
    # permute the LEAF positions (0,1,2,3) in the distribution, keep grouping = sisters
    for perm in [(1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2), (2, 3, 0, 1)]:
        Pp = {}
        for (i, j, k, l) in P:
            t = [0] * 4
            t[perm[0]], t[perm[1]], t[perm[2]], t[perm[3]] = i, j, k, l
            Pp[(i, j, k, l)] = P[tuple(t)]
        sms2 = [sms[perm[0]], sms[perm[1]], sms[2], sms[perm[2]], sms[perm[3]]]
        rms2 = [rms[perm[0]], rms[perm[1]], rms[2], rms[perm[2]], rms[perm[3]]]
        P2 = distribution(B, pi, sms2, rms2)
        worst_sym = max(worst_sym, abs(Ew_of(P2, pi, ((0, 1), (2, 3))) - base) / max(1e-300, abs(base)))
print("   diagonal / C            : max |ratio-1| =", worst_diag)
print("   cross (both NNIs) / C   : max |value|/C =", worst_cross)
print("   leaf-length symmetry    : max rel      =", worst_sym)

# ============================ exponential-consistent check ============================
print()
print("=== Q2: with sm_t = e^{-lam t}, rm_t = e^{-lam(1+kap)t} (the real model) ===")
worst_diag2 = worst_cross2 = 0.0
for _ in range(60):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    ts = rng.random(5) + 0.1
    sms = np.exp(-lam * ts)
    rms = np.exp(-lam * (1 + kappa) * ts)
    P = distribution(B, pi, sms, rms)
    pA, pG, pC, pT = pi
    Cval = 2 * pA * pC * pG * pT * pR * pY * (1 - sms[2]) * np.prod(rms)
    worst_diag2 = max(worst_diag2, abs(Ew_of(P, pi, ((0, 1), (2, 3))) / Cval - 1))
    worst_cross2 = max(worst_cross2,
                       abs(Ew_of(P, pi, ((0, 2), (1, 3)))) / abs(Cval),
                       abs(Ew_of(P, pi, ((0, 3), (1, 2)))) / abs(Cval))
print("   diagonal / C          : max |ratio-1| =", worst_diag2)
print("   cross / C             : max |value|/C =", worst_cross2)

# ============================ the 8 families: which ones vanish? ============================
print()
print("=== the 8 signed families, cross grouping (should sum to 0) ===")
raw = rng.random(4) + 0.2
pi = raw / raw.sum()
B, lam, pR, pY = setup(pi, 0.7)
ts = rng.random(5) + 0.1
sms, rms = np.exp(-lam * ts), np.exp(-lam * (1 + 0.7) * ts)
P = distribution(B, pi, sms, rms)
fam = Ew_families(P, pi, ((0, 2), (1, 3)))
for k, v in fam.items():
    print(f"   {k:28s} = {v: .6e}")
print("   sum =", sum(fam.values()))
print()
print("=== the 8 signed families, diagonal grouping (should sum to C) ===")
fam = Ew_families(P, pi, ((0, 1), (2, 3)))
pA, pG, pC, pT = pi
Cval = 2 * pA * pC * pG * pT * pR * pY * (1 - sms[2]) * np.prod(rms)
for k, v in fam.items():
    print(f"   {k:28s} = {v: .6e}")
print("   sum =", sum(fam.values()), "   C =", Cval)
