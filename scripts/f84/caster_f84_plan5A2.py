"""Proper re-check of the EwA factorisation with a MEANINGFUL scale.

Both sides of the claimed identity are ~0 (because EwA = 0), so comparing
|rhs-lhs|/|lhs| is ill-posed (divides by 0). Instead compare the two SIDES of the
factorisation term-by-term against the natural scale of the (nonzero) group sums:

    grpRY_direct := piR^2 piY^2 monA(R,Y) - piY^2 sqR pureMonA(R,Y)
                    - piR^2 sqY monPureA(R,Y) + sqR sqY pureAllA(R,Y)
    grpRY_fact   := Sum_pq pi_p Kx_pq * G_R(p,q;t1,t3) * G_Y(p,q;t2,t4)
and the same with (Y,R) <-> lengths swapped:  G_Y(p,q;t1,t3) * G_R(p,q;t2,t4).
"""
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(20260113)


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


def K(B, pi, kappa, lam, t):
    Pi = np.tile(pi, (4, 1))
    return Pi + np.exp(-lam * t) * (B - Pi) + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)


wRY = wYR = wsum = 0.0
for _ in range(80):
    raw = rng.random(4) + 0.2
    pi = raw / raw.sum()
    kappa = float(rng.random() * 3)
    B, lam, pR, pY = setup(pi, kappa)
    la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))
    K1, K2, Kx, K3, K4 = (K(B, pi, kappa, lam, t) for t in (la, lb, lx, lc, ld))
    # A-grouping pattern array: Pc(i,j,k,l) = P(i,k,j,l)
    P = np.zeros((4, 4, 4, 4))
    for a in range(4):
        for b in range(4):
            P += pi[a] * np.einsum('i,j,k,l->ijkl', K1[a], K2[a], Kx[a, b] * K3[b], K4[b])
    Pc = lambda i, j, k, l: P[i, k, j, l]
    monA = lambda U, V: sum(Pc(i, i, j, j) for i in U for j in V)
    pmA = lambda U, V: sum(Pc(i, j, k, k) for i in U for j in U for k in V)
    mpA = lambda U, V: sum(Pc(i, i, k, l) for i in U for k in V for l in V)
    paA = lambda U, V: sum(Pc(i, j, k, l) for i in U for j in U for k in V for l in V)
    sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
    S = lambda U, p, Kv: sum(Kv[p, i] for i in U)
    D = lambda U, p, q, Kv1, Kv2: sum(Kv1[p, i] * Kv2[q, i] for i in U)
    Gc = lambda U, pc, qc, p, q, Kv1, Kv2: pc ** 2 * D(U, p, q, Kv1, Kv2) - qc * S(U, p, Kv1) * S(U, q, Kv2)

    dRY = (pR ** 2 * pY ** 2 * monA(R, Y) - pY ** 2 * sqR * pmA(R, Y)
           - pR ** 2 * sqY * mpA(R, Y) + sqR * sqY * paA(R, Y))
    dYR = (pR ** 2 * pY ** 2 * monA(Y, R) - pY ** 2 * sqR * mpA(Y, R)
           - pR ** 2 * sqY * pmA(Y, R) + sqR * sqY * paA(Y, R))
    fRY = sum(pi[p] * Kx[p, q] * Gc(R, pR, sqR, p, q, K1, K3) * Gc(Y, pY, sqY, p, q, K2, K4)
              for p in range(4) for q in range(4))
    fYR = sum(pi[p] * Kx[p, q] * Gc(Y, pY, sqY, p, q, K1, K3) * Gc(R, pR, sqR, p, q, K2, K4)
              for p in range(4) for q in range(4))
    scale = max(abs(dRY), abs(dYR), abs(fRY), abs(fYR))
    wRY = max(wRY, abs(fRY - dRY) / scale)
    wYR = max(wYR, abs(fYR - dYR) / scale)
    wsum = max(wsum, abs(dRY + dYR) / scale)

print("(i-a) Sum_pq pi_p Kx G_R(t1,t3) G_Y(t2,t4)  = (R,Y) group   : max rel =", wRY)
print("(i-b) Sum_pq pi_p Kx G_Y(t1,t3) G_R(t2,t4)  = (Y,R) group   : max rel =", wYR)
print("(i-c) (R,Y)+(Y,R) = 4 EwA  (i.e. the two groups cancel)     : max rel =", wsum)
