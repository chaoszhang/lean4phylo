"""Which F84 weight table is self-consistent?

Fig.1D (sm.tex 360-363) gives PER-PATTERN weights  (block1 = letters on one side, block2 = other):
    +4 pi_A pi_G pi_C pi_T          : AA|CC, AA|TT, GG|CC, GG|TT          ("mon" family)
    -2 pi_A pi_G (pi_C^2+pi_T^2)    : AG|CC, AG|TT                        ("pureMon" family)
    -2 (pi_A^2+pi_G^2) pi_C pi_T    : AA|CT, GG|CT                        ("monPure" family)
    +(pi_A^2+pi_G^2)(pi_C^2+pi_T^2) : AG|CT                               ("pureAll" family)

The appendix aggregated formula (sm.tex 1556-1564) is the same 4 families but with coefficients
    pi_R^2 pi_Y^2 ,  pi_X^2 pi_Y^2 ,  pi_R^2 pi_Psi^2 ,  pi_X^2 pi_Psi^2
which sum to  pi_R^2 pi_Y^2 , q_R pi_Y^2 , pi_R^2 q_Y , q_R q_Y  -- DIFFERENT from Fig. 1D.

Since the aggregated formula is exactly the committed Lean `Ew`, and `Ew(ab|cd)-Ew(ac|bd)` is
4x the printed constant, the natural hypothesis (teacher's hint: pi_A/pi_G mix-ups) is that the
Fig. 1D per-pattern coefficients are the right ones.  Test every reasonable candidate set.
"""
import numpy as np
from itertools import product

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)


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


def Kmat(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


def patt4(pi, B, kappa, lam, la, lb, lx, lc, ld):
    Ka, Kb, Kx, Kc, Kd = (Kmat(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
    P = np.zeros((4, 4, 4, 4))
    for p in range(4):
        for q in range(4):
            P += pi[p] * np.einsum('i,j,k,l->ijkl', Ka[p], Kb[p], Kx[p, q] * Kc[q], Kd[q])
    return P


def events(P):
    """the 8 family values with the *topology's* side grouping already applied by the caller."""
    mon = lambda U, V: sum(P[i, i, j, j] for i in U for j in V)
    pureMon = lambda U, V: sum(P[i, j, k, k] for i in U for j in U for k in V)
    monPure = lambda U, V: sum(P[i, i, k, l] for i in U for k in V for l in V)
    pureAll = lambda U, V: sum(P[i, j, k, l] for i in U for j in U for k in V for l in V)
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    return dict(monRY=mon(R, Y), monYR=mon(Y, R),
                pmRY=pureMon(R, Y), mpYR=monPure(Y, R),
                mpRY=monPure(R, Y), pmYR=pureMon(Y, R),
                paRY=pureAll(R, Y), paYR=pureAll(Y, R), qR=sqR, qY=sqY)


def aggregate(P, pi, coef):
    """coef = (c_mon, c_pureMon, c_monPure, c_pureAll) applied to the 4 family pairs."""
    e = events(P)
    c1, c2, c3, c4 = coef
    return (c1 * (e['monRY'] + e['monYR'])
            - c2 * (e['pmRY'] + e['mpYR'])
            - c3 * (e['mpRY'] + e['pmYR'])
            + c4 * (e['paRY'] + e['paYR']))


def side_view(P, side1, side2):
    """relabel the pattern array so that `side1` becomes logical positions (0,1) and side2 (2,3)."""
    Q = np.zeros((4, 4, 4, 4))
    for i, j, k, l in product(range(4), repeat=4):
        s = [0] * 4
        s[side1[0]], s[side1[1]] = i, j
        s[side2[0]], s[side2[1]] = k, l
        Q[i, j, k, l] = P[tuple(s)]
    return Q


def fig1d_coef(pi):
    pA, pG, pC, pT = pi
    return (4 * pA * pG * pC * pT, 2 * pA * pG * (pC ** 2 + pT ** 2),
            (pA ** 2 + pG ** 2) * 2 * pC * pT, (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2))


def appendix_coef(pi):
    pA, pG, pC, pT = pi
    pR, pY = pA + pG, pC + pT
    qR, qY = pA ** 2 + pG ** 2, pC ** 2 + pT ** 2
    return (pR ** 2 * pY ** 2, qR * pY ** 2, pR ** 2 * qY, qR * qY)


def quarter(coef):
    return tuple(c / 4 for c in coef)


rng = np.random.default_rng(7)
sets = {}
for _ in range(150):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))
    P = patt4(pi, B, kappa, lam, la, lb, lx, lc, ld)
    pA, pG, pC, pT = pi
    const = (2 * pA * pC * pG * pT * pR * pY
             * np.exp(-lam * (1 + kappa) * (la + lb + lc + ld)) * (1 - np.exp(-lam * lx)))

    views = {'ab': (P, (0, 1), (2, 3)),
             'ac': (P, (0, 2), (1, 3)),
             'ad': (P, (0, 3), (1, 2))}
    cands = {'APPENDIX': appendix_coef(pi), 'APPENDIX/4': quarter(appendix_coef(pi)),
             'FIG1D': fig1d_coef(pi), 'FIG1D/2': tuple(c / 2 for c in fig1d_coef(pi)),
             'FIG1D/4': quarter(fig1d_coef(pi)),
             'FIG1D*?': (4 * pA * pG * pC * pT / 2, 2 * pA * pG * (pC ** 2 + pT ** 2) / 2,
                         (pA ** 2 + pG ** 2) * 2 * pC * pT / 2,
                         (pA ** 2 + pG ** 2) * (pC ** 2 + pT ** 2) / 2)}
    for name, coef in cands.items():
        vals = {}
        for k, (Pm, s1, s2) in views.items():
            V = side_view(Pm, s1, s2)
            vals[k] = aggregate(V, pi, coef)
        rec = sets.setdefault(name, {'d_ab_ac': 0.0, 'd_ab_ad': 0.0, 'ab': 0.0, 'ac': 0.0, 'ad': 0.0})
        rec['d_ab_ac'] = max(rec['d_ab_ac'], abs((vals['ab'] - vals['ac']) / const - 1))
        rec['d_ab_ad'] = max(rec['d_ab_ad'], abs((vals['ab'] - vals['ad']) / const - 1))
        rec['ab'] = max(rec['ab'], abs(vals['ab'] / const))
        rec['ac'] = max(rec['ac'], abs(vals['ac']) / abs(const))
        rec['ad'] = max(rec['ad'], abs(vals['ad']) / abs(const))

print(f"{'candidate':12s} {'|(ab-ac)/C-1|':>14s} {'|(ab-ad)/C-1|':>14s} "
      f"{'|ab|/C':>10s} {'|ac|/C':>10s} {'|ad|/C':>10s}")
for name, r in sets.items():
    print(f"{name:12s} {r['d_ab_ac']:14.3e} {r['d_ab_ad']:14.3e} "
          f"{r['ab']:10.3e} {r['ac']:10.3e} {r['ad']:10.3e}")

print()
print("Note: 'C' = 2 piA piC piG piT pR pY e^{-lam(1+kap)(la+lb+lc+ld)}(1-e^{-lam lx})")
print("      APPENDIX * 4 is the 4x discrepancy already documented in CASTER_F84_FINDING.md.")
