"""Which per-(p,q) summand makes 4*Ew = Sum_pq (summand) hold TERM-BY-TERM?

A's `Ew_factor` proof does `congr 1 with p; congr 1 with q; ring`, which requires the
identity to hold at each (p,q) -- NOT merely after summing.  Test:
  body_LHS(p,q) : the 8 closed-form terms at (p,q) (what `simp only [*_closed]` produces)
  cand1(p,q)    : pi_p Kx (gR(p;t1,t2) gY(q;t3,t4) + gY(p;t3,t4) gR(q;t1,t2))   <- what I had claimed
  cand2(p,q)    : pi_p Kx (gR(p;t1,t2) gY(q;t3,t4) + gY(p;t1,t2) gR(q;t3,t4))   <- length pairs follow the class
"""
import numpy as np

A, G, C, T = 0, 1, 2, 3
R, Y = (A, G), (C, T)
rng = np.random.default_rng(777)
raw = rng.random(4) + 0.2
pi = raw / raw.sum()
kappa = float(rng.random() * 3)
pR, pY = pi[A] + pi[G], pi[C] + pi[T]
lam = (pR * pY) / ((1 - sum(x * x for x in pi)) * pR * pY
                   + 2 * kappa * (pi[A] * pi[G] * pY + pi[C] * pi[T] * pR))
B = np.zeros((4, 4))
for i in range(4):
    for j in range(4):
        same = (i in R and j in R) or (i in Y and j in Y)
        pc = pR if j in R else pY
        B[i, j] = pi[j] / pc if same else 0.0
Kk = lambda t: np.tile(pi, (4, 1)) + np.exp(-lam * t) * (B - np.tile(pi, (4, 1))) \
    + np.exp(-lam * (1 + kappa) * t) * (np.eye(4) - B)
la, lb, lx, lc, ld = (float(x) for x in (rng.random(5) + 0.1))
K1, K2, Kx, K3, K4 = Kk(la), Kk(lb), Kk(lx), Kk(lc), Kk(ld)
sqR, sqY = pi[A] ** 2 + pi[G] ** 2, pi[C] ** 2 + pi[T] ** 2
S = lambda U, p, Kv: sum(Kv[p, i] for i in U)
D = lambda U, p, q, Kv1, Kv2: sum(Kv1[p, i] * Kv2[q, i] for i in U)
g = lambda c, pc, qc, p, q, Kv1, Kv2: pc ** 2 * D(c, p, q, Kv1, Kv2) - qc * S(c, p, Kv1) * S(c, q, Kv2)

print("per-(p,q) body of the LHS `4*Ew` (the 8 closed-form terms), vs the two candidate summands")
print(f"{'(p,q)':>7} {'body_LHS':>16} {'cand1 - body':>16} {'cand2 - body':>16}")
tot1 = tot2 = totL = 0.0
for p in range(4):
    for q in range(4):
        body = (pR ** 2 * pY ** 2 * D(R, p, p, K1, K2) * Kx[p, q] * D(Y, q, q, K3, K4)
                + pR ** 2 * pY ** 2 * D(Y, p, p, K1, K2) * Kx[p, q] * D(R, q, q, K3, K4)
                - pY ** 2 * sqR * S(R, p, K1) * S(R, p, K2) * Kx[p, q] * D(Y, q, q, K3, K4)
                - pY ** 2 * sqR * D(Y, p, p, K1, K2) * Kx[p, q] * S(R, q, K3) * S(R, q, K4)
                - pR ** 2 * sqY * D(R, p, p, K1, K2) * Kx[p, q] * S(Y, q, K3) * S(Y, q, K4)
                - pR ** 2 * sqY * S(Y, p, K1) * S(Y, p, K2) * Kx[p, q] * D(R, q, q, K3, K4)
                + sqR * sqY * S(R, p, K1) * S(R, p, K2) * Kx[p, q] * S(Y, q, K3) * S(Y, q, K4)
                + sqR * sqY * S(Y, p, K1) * S(Y, p, K2) * Kx[p, q] * S(R, q, K3) * S(R, q, K4))
        c1 = pi[p] * Kx[p, q] * (g(R, pR, sqR, p, p, K1, K2) * g(Y, pY, sqY, q, q, K3, K4)
                                 + g(Y, pY, sqY, p, p, K3, K4) * g(R, pR, sqR, q, q, K1, K2))
        c2 = pi[p] * Kx[p, q] * (g(R, pR, sqR, p, p, K1, K2) * g(Y, pY, sqY, q, q, K3, K4)
                                 + g(Y, pY, sqY, p, p, K1, K2) * g(R, pR, sqR, q, q, K3, K4))
        print(f"{str((p,q)):>7} {body:16.6e} {c1-body:16.3e} {c2-body:16.3e}")
        totL += body
        tot1 += c1
        tot2 += c2
print(f"\nsums: body={totL:.8e}  cand1={tot1:.8e} (diff {tot1-totL:.3e})  cand2={tot2:.8e} (diff {tot2-totL:.3e})")
print("\n=> whichever column is identically 0 is the correct per-(p,q) summand.")
