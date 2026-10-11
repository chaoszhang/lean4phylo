from fractions import Fraction as F
import sys
from itertools import product

def check(nvals=(1,2,3,4,5,7,11)):
    ok = True
    for n in nvals:
        for p in [F(0), F(1,3), F(1,2), F(1)]:
            # E[( (1/n) sum_{i<n} X_i )^2] with iid Bernoulli(p), X_i^2 = X_i
            mean = p
            ex2 = (n*p + (n*(n-1))*p*p) / (n*n)   # diagonal + off-diagonal
            var = ex2 - mean*mean
            want = p*(1-p)/n
            if var != want:
                print('MISMATCH', n, p, var, want); ok = False
        print('n=%2d  p=1/3: Var(empFreq)=%s  p(1-p)/n=%s' % (n, F(1,3)*F(2,3)/n, F(1,3)*F(2,3)/n))
    # ★ W14b（2026-10-12 协调侧加固）：本脚本【本来就有判据 ok】并已打印 ALL_OK/FAIL，
    #   但【从未把它接到退出码】✗（恒 exit 0）⇒ 失败只能从 stdout 看出，任何看退出码的消费者都看不见 ✗。
    #   现将 ok 接到退出码 ✓（不新造判据、不改任何数学内容）。
    print('ALL_OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)
check()
