"""Independent literal transcription of `Phylo/Stat/CASTERF84Events.lean` (commit 36ce9be).

Purpose: settle t42's claim that `Ew` is *totally symmetric* in (t1,t2,t3,t4), hence
EwF84 = EwF84_ac = EwF84_ad and statement (1) is FALSE as written.

Everything below is copied line-by-line from the Lean source:
  piR = pi0+pi1 , piY = pi2+pi3 , sqR = pi0^2+pi1^2 , sqY = pi2^2+pi3^2
  Bmat[i][j] = [class(i)=class(j)] * pi_j / p_class(j)
  Kmat(t)[i][j] = pi_j + sm(t)*(B-1)[i][j] + rm(t)*(I-B)[i][j]
  patt4(t1,t2,tx,t3,t4)[i][j][k][l] = sum_p sum_q pi_p K(t1)[p][i]K(t2)[p][j]K(tx)[p][q]K(t3)[q][k]K(t4)[q][l]
  mon(U,V)     = sum_{i in U} sum_{j in V} patt4[i][i][j][j]
  pureMon(U,V) = sum_{i in U} sum_{j in U} sum_{k in V} patt4[i][j][k][k]
  monPure(U,V) = sum_{i in U} sum_{k in V} sum_{l in V} patt4[i][i][k][l]
  pureAll(U,V) = sum_{i in U} sum_{j in U} sum_{k in V} sum_{l in V} patt4[i][j][k][l]
  Ew(t1,t2,tx,t3,t4) = pR^2 pY^2 (mon(R,Y)+mon(Y,R))
                       - pY^2 sqR (pureMon(R,Y)+monPure(Y,R))
                       - pR^2 sqY (monPure(R,Y)+pureMon(Y,R))
                       + sqR sqY (pureAll(R,Y)+pureAll(Y,R))          <-- NO /4
  EwF84    = Ew(la, lb, lx, lc, ld)
  EwF84_ac = Ew(la, lc, lx, lb, ld)
  EwF84_ad = Ew(la, ld, lx, lb, lc)
"""
import itertools
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
CLS = {A: R, G: R, C: Y, T: Y}


def build(pi, kappa):
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                       + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
    B = np.zeros((4, 4))
    for i in range(4):
        for j in range(4):
            same = (i in R and j in R) or (i in Y and j in Y)
            pc = pR if j in R else pY
            B[i, j] = pi[j] / pc if same else 0.0
    return B, lam


def Kmat(B, pi, kappa, lam, t):
    sm, rm = np.exp(-lam * t), np.exp(-lam * (1 + kappa) * t)
    Pi = np.tile(pi, (4, 1))
    return Pi + sm * (B - Pi) + rm * (np.eye(4) - B)


def patt4(pi, B, kappa, lam, t1, t2, tx, t3, t4):
    K1, K2, Kx, K3, K4 = (Kmat(B, pi, kappa, lam, t)
                          for t in (t1, t2, tx, t3, t4))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', K1[p], K2[p], Kx[p, q] * K3[q], K4[q])
    return P


def events(P):
    U = lambda U_, V_: sum(P[i, i, j, j] for i in U_ for j in V_)
    PM = lambda U_, V_: sum(P[i, j, k, k] for i in U_ for j in U_ for k in V_)
    MP = lambda U_, V_: sum(P[i, i, k, l] for i in U_ for k in V_ for l in V_)
    PA = lambda U_, V_: sum(P[i, j, k, l] for i in U_ for j in U_ for k in V_ for l in V_)
    return U, PM, MP, PA


def Ew(pi, B, kappa, lam, t1, t2, tx, t3, t4):
    P = patt4(pi, B, kappa, lam, t1, t2, tx, t3, t4)
    mon, pureMon, monPure, pureAll = events(P)
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    return (pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR * (pureMon(R, Y) + monPure(Y, R))
            - pR ** 2 * sqY * (monPure(R, Y) + pureMon(Y, R))
            + sqR * sqY * (pureAll(R, Y) + pureAll(Y, R)))


# ---- the Python "reshuffle" convention used by caster_f84_iface.py ----
def Ew_split(pi, B, kappa, lam, la, lb, lx, lc, ld, split):
    P = patt4(pi, B, kappa, lam, la, lb, lx, lc, ld)

    def Pc(i, j, k, l):
        s = [0] * 4
        s[split[0]], s[split[1]], s[split[2]], s[split[3]] = i, j, k, l
        return P[tuple(s)]
    pR, pY = pi[A] + pi[G], pi[C] + pi[T]
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    mon = lambda U_, V_: sum(Pc(i, i, j, j) for i in U_ for j in V_)
    pureMon = lambda U_, V_: sum(Pc(i, j, k, k) for i in U_ for j in U_ for k in V_)
    monPure = lambda U_, V_: sum(Pc(i, i, k, l) for i in U_ for k in V_ for l in V_)
    pureAll = lambda U_, V_: sum(Pc(i, j, k, l) for i in U_ for j in U_ for k in V_ for l in V_)
    return (pR ** 2 * pY ** 2 * (mon(R, Y) + mon(Y, R))
            - pY ** 2 * sqR * (pureMon(R, Y) + monPure(Y, R))
            - pR ** 2 * sqY * (monPure(R, Y) + pureMon(R, Y))
            + sqR * sqY * (pureAll(R, Y) + pureAll(Y, R)))


rng = np.random.default_rng(20260109)
w_perm = 0.0
w_closed = 0.0
w_acad = 0.0
w_abac = 0.0
w_abac_split = 0.0
w_acad_split = 0.0
worst = None
for _ in range(40):
    raw = rng.random(4) + 0.15
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam = build(pi, kappa)
    la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))

    base = Ew(pi, B, kappa, lam, la, lb, lx, lc, ld)
    # (1) total symmetry in the four leaf lengths?
    spread = 0.0
    for perm in itertools.permutations([la, lb, lc, ld]):
        spread = max(spread, abs(Ew(pi, B, kappa, lam, *perm, lx)
                                 if False else Ew(pi, B, kappa, lam,
                                                  perm[0], perm[1], lx, perm[2], perm[3]) - base))
    w_perm = max(w_perm, spread / max(abs(base), 1e-300))

    # (2) closed form claimed by t42: 8*piA*piC*piG*piT*pR*pY*(1-sm lx)*rm(sum l)
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    s = la + lb + lc + ld
    closed = 8 * pA * pC * pG * pT * pR * pY * (1 - np.exp(-lam * lx)) * np.exp(-lam * (1 + kappa) * s)
    if abs(closed) > 1e-300:
        w_closed = max(w_closed, abs(base / closed - 1))

    e_ab = Ew(pi, B, kappa, lam, la, lb, lx, lc, ld)
    e_ac = Ew(pi, B, kappa, lam, la, lc, lx, lb, ld)
    e_ad = Ew(pi, B, kappa, lam, la, ld, lx, lb, lc)
    claim = 2 * pA * pC * pG * pT * pR * pY * np.exp(-lam * (1 + kappa) * s) * (1 - np.exp(-lam * lx))
    w_acad = max(w_acad, abs(e_ac - e_ad) / max(abs(e_ac), 1e-300))
    w_abac = max(w_abac, abs((e_ab - e_ac) / claim - 1) if abs(claim) > 0 else 0.0)

    s_ab = Ew_split(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 1, 2, 3))
    s_ac = Ew_split(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 2, 1, 3))
    s_ad = Ew_split(pi, B, kappa, lam, la, lb, lx, lc, ld, (0, 3, 1, 2))
    w_abac_split = max(w_abac_split, abs((s_ab - s_ac) / claim - 1))
    w_acad_split = max(w_acad_split, abs(s_ac - s_ad) / max(abs(s_ac), 1e-300))
    if worst is None:
        worst = (pi.copy(), kappa, lam, (la, lb, lx, lc, ld), base, closed, e_ab, e_ac, e_ad,
                 s_ab, s_ac, s_ad, claim)

print("=== Lean-literal Ew (no /4) ===")
print("(1) total symmetry in the 4 leaf lengths : max rel spread =", w_perm)
print("(2) Ew / [8 piA piC piG piT pR pY (1-sm lx) rm(sum l)] : max |ratio-1| =", w_closed)
print("    EwF84 - EwF84_ac  vs claim (should be claim if (1) false) : max |ratio-1| =", w_abac)
print("    EwF84_ac = EwF84_ad : max rel =", w_acad)
print()
print("=== Python 'split' convention (iface.py) ===")
print("    (EwF84 - EwF84_ac)/claim : max |ratio-1| =", w_abac_split)
print("    EwF84_ac = EwF84_ad      : max rel      =", w_acad_split)
print()
pi, kappa, lam, ts, base, closed, e_ab, e_ac, e_ad, s_ab, s_ac, s_ad, claim = worst
print("worked example: pi =", pi, " kappa =", kappa, " lam =", lam)
print("  lengths (la,lb,lx,lc,ld) =", ts)
print("  Ew(lean)                  =", base)
print("  closed 8 piA piC piG piT..=", closed)
print("  EwF84, EwF84_ac, EwF84_ad =", e_ab, e_ac, e_ad)
print("  split   : ab, ac, ad      =", s_ab, s_ac, s_ad)
print("  claim                     =", claim)
