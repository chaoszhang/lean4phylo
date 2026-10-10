"""W12f 第四轮：tree-poset hook-length 公式的**计数递推**数值核对（整数，无浮点）。

对应 Lean（`Phylo/Stat/HookLength.lean`）：

* §5 `prod_hook_eq_hook_mul_prod_children`：
      ∏_{D ∈ internalBelow C} s_D  =  s_C · ∏_{B ∈ children C} ∏_{D ∈ internalBelow B} s_D
* §6 `multinomial_mul_prod_factorial`：
      multinomial(s, f) · ∏_{i∈s} (f i)!  =  (∑_{i∈s} f i)!
* §6 `multinomial_children_factorial`：`N = 1 + Σ_B N_B` 时
      multinomial(Ns, id) · ∏_B N_B!  =  (N-1)!

本脚本核对的是**计数归纳的收口恒等式**（把 §5 与 §6 拼起来就得到 `LE(T) = N!/∏ s_v`）：

    multinomial(N-1; N_1..N_k) · (∏_B N_B!) · N  ==  N!

用法：`python3 scripts/msc/w12f_hook_count_check.py`
"""
import sys
from math import factorial as F
from itertools import product


def multinomial(total, parts):
    assert sum(parts) == total, (total, parts)
    num = F(total)
    for p in parts:
        num //= F(p)
    return num


def main():
    ok = True
    worst = 0
    for k in range(0, 5):
        for parts in product(range(1, 5), repeat=k):
            N = 1 + sum(parts)
            mult = multinomial(N - 1, list(parts))
            prodF = 1
            for p in parts:
                prodF *= F(p)
            lhs = mult * prodF * N
            if lhs != F(N):
                print("MISMATCH N=%d parts=%s lhs=%d N!=%d" % (N, parts, lhs, F(N)))
                ok = False
            worst = max(worst, N)
    print("checked all (N_B) vectors with N <= %d" % worst)
    print("ALL_OK" if ok else "FAIL")

    for name, parts in [("balanced((0,1),(2,3))", [1, 1]), ("caterpillar((0,1),2),3", [2])]:
        N = 1 + sum(parts)
        hookprod = 1
        for p in parts:
            hookprod *= (1 + p)
        print("%-24s N=%d  hook 积 = %d   N!/hook 积 = %d" % (name, N, hookprod, F(N) // hookprod))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
