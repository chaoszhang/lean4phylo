#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/kingman_jumpchain.py -- W10a 跳链 (2.1)/(2.2) 的**精确有理数**穷举复核

Kingman (1982) *The Coalescent*, Stochastic Processes and their Applications 13, 235-248.
文献用 OCR 版 `references/md/Kingman1982_TheCoalescent.md`；该版**公式编号在版面里错位**，
故一律「行号 + 公式内容」双重定位：

  * 绝对概率 (2.2)，**第 219-228 行**：
        P{S_k = xi} = (n-k)! k! (k-1)! / ( n! (n-1)! ) * prod_i lambda_i!
    其中 lambda_1..lambda_k 是等价关系 xi 的等价类大小（= 集合划分的各块大小）。
  * 跳链转移概率 (2.1)，**第 215-217 行** + **第 241-256 行**：
        P{S_{k-1} = eta | S_k = xi} = q_{xi eta}/q_xi = 1/C(k,2)     (xi < eta)
    即「在 xi 的 C(k,2) 个块对中均匀随机合并一对」。
  * 倒向归纳路线，**第 274-276 行**：
        "We prove (2.3) by backward induction on k, it being clearly true for k = n."

本脚本**不做 Monte Carlo**，全部 `fractions.Fraction` 精确有理数穷举。

复核条目
  (a) 归一化      sum_{|P|=k} partitionProb(n,k,P) == 1                 (1 <= k <= n <= 7)
  (b) 层间一致性  partitionProb(n,k,P) == sum_{Q above P} pp(n,k+1,Q)/C(k+1,2)
                  连同两侧的组合计数：#(P below Q) == C(k+1,2)，
                  #(Q above P) == sum_{B in P} (2^(|B|-1) - 1)
  (c) 单块分裂恒等式（**有序**和，A 与 B\\A 各计一次）
                  sum_{A subset B, A != {}, A != B} |A|! * |B\\A|! == |B|! * (|B|-1)
  (d) 归一化的**第二条独立路线**（本脚本另加，供诚实边界引用）：
                  W(n,k) := sum_{|P|=k} prod_B |B|!  满足 Lah 递推
                  W(n,k) = W(n-1,k-1) + (n-1+k) * W(n-1,k),
                  闭形式 W(n,k) = n! * C(n-1,k-1) / k!，且 lead(n,k) * W(n,k) = 1。
  (e) 样板数字：pp(4,3,{12|3|4}) = 1/6；无限制分裂和 sum_{A in B.powerset}
                  |A|!*|B\\A|! = (|B|+1)*|B|!；以及**无序**分裂和 = |B|!*(|B|-1)/2。
  (f) 【v2 新增】与交付文件 `Phylo/Stat/KingmanJumpChain.lean` 里**新证出的定理**
      逐条对应的数值断言：
        · `partitionProb_merge_recursion`：pp(n,k,P)*C(k+1,2)
              == sum_{Q: |Q|=k+1, MergeInto Q P} pp(n,k+1,Q)   （Lean 里的确切形状）
        · `stateSum_eq_succ`：S_k == S_{k+1}（1 <= k < n）
        · `stateSum_self` / `eq_bot_of_card_parts`：唯一的 n-块划分是 ⊥，且 pp = 1
        · `two_mul_choose_two_cast`：2*C(m,2) == m(m-1)
        · `card_pairSet`：使 Q 合并到 P 的**有序**块对数 == 2 当且仅当 MergeInto Q P
        · `card_offDiag`：有序相异对个数 == |s|(|s|-1)
        · `jumpWeight_sum_eq_one` / `partitionProb_sum_eq_one`：（即 (a)）

  ⚠️ 规格 `W10_COALESCENT_SPEC.md` §1.7 的 (★) 数值核对有一处笔误：
     它写「|B| = 4 时 LHS = (1!3! *4) + (2!2! *3) = 24 + 12 = 36 = 4!*3」。
     24 + 12 = 36 是**无序**分裂和（= 4!*3/2 = 36）；**有序**分裂和是 72 = 4!*3。
     §1.5 里 `sum_powerset_factorial` 的**陈述**（= |B|!*(|B|-1)）是对的（有序），
     本脚本 (c) 按该陈述复核。

Usage: python3 kingman_jumpchain.py     (exit 0 iff VERDICT: PASS)
"""
import math
import sys
from fractions import Fraction
from itertools import combinations, permutations

NMAX = 7


# --------------------------------------------------------------------- 划分
def set_partitions(items):
    """items: tuple -> items 的所有集合划分（frozenset of frozenset）。"""
    if not items:
        yield frozenset()
        return
    first, rest = items[0], items[1:]
    for rest_part in set_partitions(rest):
        yield rest_part | {frozenset((first,))}          # first 单独成块
        for block in rest_part:                          # first 并入每个已有块
            yield (rest_part - {block}) | {block | {first}}


def partitions_of(n, k=None):
    for P in set_partitions(tuple(range(n))):
        if k is None or len(P) == k:
            yield P


def partition_prob(n, k, P):
    """Kingman (2.2)：单个 k-块划分的绝对概率，精确有理数。"""
    if k == 0:
        return Fraction(1) if n == 0 else Fraction(0)
    lead = Fraction(math.factorial(n - k) * math.factorial(k) * math.factorial(k - 1),
                    math.factorial(n) * math.factorial(n - 1))
    prod = 1
    for B in P:
        prod *= math.factorial(len(B))
    return lead * prod


def merge_outcomes(Q):
    """Q 的 C(|Q|,2) 个一步合并结果（按无序块对），返回 (划分, 块对数)。"""
    blocks = sorted(Q, key=lambda b: sorted(b))
    return [frozenset([b for b in blocks if b not in (B1, B2)] + [B1 | B2])
            for B1, B2 in combinations(blocks, 2)]


def splits_above(P):
    """P 的所有一层上升 = 把 P 的某个块**无序地**劈成两个非空块。

    代表元约定：令 A 取 `min B`（无序分裂 {A, B\\A} 中**含 min B** 的那一半）。
    """
    out = []
    for B in P:
        bl = sorted(B)
        for r in range(1, len(bl)):
            for rest in combinations(bl[1:], r - 1):
                A = frozenset((bl[0],) + rest)
                out.append(frozenset([b for b in P if b != B]
                                     + [A, frozenset(B - A)]))
    return out


# ------------------------------------------------------------------- 复核
def check_a():
    bad, table = [], {}
    for n in range(1, NMAX + 1):
        row = []
        for k in range(1, n + 1):
            s = sum((partition_prob(n, k, P) for P in partitions_of(n, k)), Fraction(0))
            row.append(s)
            if s != 1:
                bad.append((n, k, str(s)))
        table[n] = row
    print("(a) 归一化  sum_{|P|=k} partitionProb(n,k,P) == 1   [n = 1..%d]" % NMAX)
    for n in range(1, NMAX + 1):
        print("      n=%d : k=1..%-2d -> %s" % (n, n, [str(x) for x in table[n]]))
    print("      => %s" % ("PASS" if not bad else "FAIL %r" % (bad,)))
    return not bad


def check_b():
    bad, triples = [], 0
    for n in range(2, NMAX + 1):
        for k in range(1, n):
            above, below_count, above_count = {}, {}, {}
            for Q in partitions_of(n, k + 1):
                outs = merge_outcomes(Q)
                if len(set(outs)) != math.comb(k + 1, 2):
                    bad.append(("#P below Q", n, k + 1, len(set(outs)),
                                math.comb(k + 1, 2)))
                pq = partition_prob(n, k + 1, Q)
                for P in outs:
                    above[P] = above.get(P, Fraction(0)) + pq
                    above_count[P] = above_count.get(P, 0) + 1
                for P in outs:
                    below_count[Q] = below_count.get(Q, 0) + 1
            for P in partitions_of(n, k):
                pp = partition_prob(n, k, P)
                ck = math.comb(k + 1, 2)
                nsplits = sum(2 ** (len(B) - 1) - 1 for B in P)
                if above_count.get(P, 0) != nsplits:
                    bad.append(("#Q above P", n, k, above_count.get(P, 0), nsplits))
                if set(splits_above(P)) != set(
                        Q for Q in partitions_of(n, k + 1) if P in merge_outcomes(Q)):
                    bad.append(("split enumerator", n, k))
                if above.get(P, Fraction(0)) / ck != pp:     # 规格 §1.5 的形状
                    bad.append(("down", n, k, str(above.get(P, Fraction(0)) / ck),
                                str(pp)))
                if above.get(P, Fraction(0)) != ck * pp:     # 等价的上行形式
                    bad.append(("up", n, k, str(above.get(P, Fraction(0))),
                                str(ck * pp)))
                triples += 1
    print("(b) 层间一致性  pp(P) == sum_{Q above P} pp(Q)/C(k+1,2)   "
          "[n<=%d，共 %d 个 (n,k,P)]" % (NMAX, triples))
    print("      · 每个 Q 的 C(k+1,2) 个块对给出**互不相同**的下降划分")
    print("      · 每个 P 恰有 sum_B (2^(|B|-1) - 1) 个上一层 Q")
    print("      => %s" % ("PASS" if not bad else "FAIL %r" % (bad[:8],)))
    return not bad


def check_c():
    bad = []
    print("(c) 单块分裂恒等式（有序和）")
    for m in range(2, NMAX + 1):
        B = frozenset(range(m))
        lhs = sum((Fraction(math.factorial(len(A)))
                   * Fraction(math.factorial(len(B - A))))
                  for r in range(1, m) for A in map(frozenset, combinations(range(m), r)))
        rhs = Fraction(math.factorial(m) * (m - 1))
        ok = lhs == rhs
        bad += [] if ok else [(m, str(lhs), str(rhs))]
        print("      |B|=%d : 有序和 = %-8s |B|!*(|B|-1) = %-8s %s"
              % (m, lhs, rhs, "OK" if ok else "FAIL"))
    print("      => %s" % ("PASS" if not bad else "FAIL %r" % (bad,)))
    return not bad


def check_d():
    bad = []
    W = {(0, 0): Fraction(1)}
    for n in range(1, NMAX + 1):
        W[(n, 0)] = Fraction(0)
        for k in range(1, n + 1):
            s = Fraction(0)
            for P in partitions_of(n, k):
                pr = 1
                for B in P:
                    pr *= math.factorial(len(B))
                s += pr
            W[(n, k)] = s
    for n in range(1, NMAX + 1):
        for k in range(1, n + 1):
            rec = W.get((n - 1, k - 1), Fraction(0)) \
                + Fraction(n - 1 + k) * W.get((n - 1, k), Fraction(0))
            closed = Fraction(math.factorial(n) * math.comb(n - 1, k - 1),
                              math.factorial(k))
            lead = Fraction(math.factorial(n - k) * math.factorial(k)
                            * math.factorial(k - 1),
                            math.factorial(n) * math.factorial(n - 1))
            if W[(n, k)] != rec:
                bad.append(("rec", n, k, str(W[(n, k)]), str(rec)))
            if W[(n, k)] != closed:
                bad.append(("closed", n, k, str(W[(n, k)]), str(closed)))
            if lead * W[(n, k)] != 1:
                bad.append(("lead*W", n, k, str(lead * W[(n, k)])))
    print("(d) Lah 路线（归一化的第二条独立路线）  [n<=%d]" % NMAX)
    print("      W(n,k) = sum_|P|=k prod_B |B|!  = W(n-1,k-1) + (n-1+k)W(n-1,k) "
          "= n!*C(n-1,k-1)/k!")
    for n in range(1, NMAX + 1):
        print("      n=%d : W = %s" % (n, [str(W[(n, k)]) for k in range(1, n + 1)]))
    print("      且 lead(n,k) * W(n,k) = 1（= partitionProb 的归一化）")
    print("      => %s" % ("PASS" if not bad else "FAIL %r" % (bad[:8],)))
    return not bad


def check_e():
    bad = []
    print("(e) 样板数字")
    P = frozenset({frozenset({0, 1}), frozenset({2}), frozenset({3})})
    got = partition_prob(4, 3, P)
    if got != Fraction(1, 6):
        bad.append(("pp(4,3,{12|3|4})", str(got)))
    print("      partitionProb(4,3,{12|3|4}) = %s            （规格 §1.7 期望 1/6）" % got)
    # 规格 §1.7 递归样板：两个 P 各 (1/6)/C(3,2) => 1/9 = pp(4,2,{12|34})
    P2 = frozenset({frozenset({0, 1}), frozenset({2, 3})})
    Q1 = frozenset({frozenset({0, 1}), frozenset({2}), frozenset({3})})
    Q2 = frozenset({frozenset({0}), frozenset({1}), frozenset({2, 3})})
    s = (partition_prob(4, 3, Q1) + partition_prob(4, 3, Q2)) / math.comb(3, 2)
    print("      (pp(4,3,{12|3|4}) + pp(4,3,{1|2|34}))/C(3,2) = %s ; "
          "pp(4,2,{12|34}) = %s" % (s, partition_prob(4, 2, P2)))
    for m in (3, 4):
        B = frozenset(range(m))
        ordered = sum((Fraction(math.factorial(len(A)))
                       * Fraction(math.factorial(len(B - A))))
                      for r in range(1, m)
                      for A in map(frozenset, combinations(range(m), r)))
        unordered = ordered / 2
        exp_o, exp_u = m * (m - 1) // 2 * 2 * math.factorial(m - 2) * 2, 0
        exp_o = Fraction(math.factorial(m) * (m - 1))
        exp_u = exp_o / 2
        if ordered != exp_o:
            bad.append(("ordered", m, str(ordered), str(exp_o)))
        if unordered != exp_u:
            bad.append(("unordered", m, str(unordered), str(exp_u)))
        print("      |B|=%d 有序和 %-4s = |B|!*(|B|-1) %-4s ；无序和 %-4s "
              "（规格 §1.7 (★) 的 |B|=4 数字 36 是无序和，非 4!*3=72）"
              % (m, ordered, exp_o, unordered))
    for m in range(0, NMAX + 1):
        B = frozenset(range(m))
        tot = sum((Fraction(math.factorial(len(A)))
                   * Fraction(math.factorial(len(B - A))))
                  for r in range(0, m + 1)
                  for A in map(frozenset, combinations(range(m), r)))
        exp = Fraction((m + 1) * math.factorial(m))
        if tot != exp:
            bad.append(("unrestricted", m, str(tot), str(exp)))
    print("      无限制版 sum_{A in B.powerset} |A|!*|B\\A|! = (|B|+1)*|B|!   [|B|<=%d]"
          % NMAX)
    print("      => %s" % ("PASS" if not bad else "FAIL %r" % (bad,)))
    return not bad


def check_f():
    """(f) 【v2 新增】与 Lean 文件里新证出的定理逐条对应的数值断言。"""
    bad = []
    # (f1) partitionProb_merge_recursion（Lean 里的确切形状）
    for n in range(2, NMAX + 1):
        for k in range(1, n):
            for P in partitions_of(n, k):
                lhs = partition_prob(n, k, P) * math.comb(k + 1, 2)
                rhs = sum((partition_prob(n, k + 1, Q)
                           for Q in partitions_of(n, k + 1)
                           if P in merge_outcomes(Q)), Fraction(0))
                if lhs != rhs:
                    bad.append(("recursion", n, k, str(lhs), str(rhs)))
    # (f2) stateSum_eq_succ：S_k == S_{k+1}
    for n in range(2, NMAX + 1):
        for k in range(1, n):
            sk = sum((partition_prob(n, k, P) for P in partitions_of(n, k)), Fraction(0))
            sk1 = sum((partition_prob(n, k + 1, P) for P in partitions_of(n, k + 1)),
                      Fraction(0))
            if sk != sk1:
                bad.append(("succ", n, k, str(sk), str(sk1)))
    # (f3) stateSum_self / eq_bot_of_card_parts：唯一的 n-块划分，pp = 1
    for n in range(1, NMAX + 1):
        Ps = list(partitions_of(n, n))
        if len(Ps) != 1:
            bad.append(("unique n-block", n, len(Ps)))
        elif partition_prob(n, n, Ps[0]) != 1:
            bad.append(("pp bot", n, str(partition_prob(n, n, Ps[0]))))
    # (f4) two_mul_choose_two_cast：2*C(m,2) == m(m-1)
    for m in range(0, NMAX + 2):
        if 2 * math.comb(m, 2) != m * (m - 1):
            bad.append(("choose2", m))
    # (f5) card_pairSet：使 Q 合并到 P 的有序块对数 == 2 当且仅当 MergeInto Q P
    for n in range(2, NMAX + 1):
        for k in range(1, n):
            for Q in partitions_of(n, k + 1):
                blocks = sorted(Q, key=lambda b: sorted(b))
                cnt = {}
                for (B1, B2) in permutations(blocks, 2):
                    Pm = frozenset([b for b in blocks if b not in (B1, B2)] + [B1 | B2])
                    cnt[Pm] = cnt.get(Pm, 0) + 1
                outs = set(merge_outcomes(Q))
                for P in partitions_of(n, k):
                    if cnt.get(P, 0) not in (0, 2):
                        bad.append(("pairSet", n, k, cnt.get(P, 0)))
                    if (P in cnt) != (P in outs):
                        bad.append(("MergeInto iff", n, k))
    # (f6) card_offDiag：有序相异对个数 == |s|(|s|-1)
    for m in range(0, NMAX + 1):
        if sum(1 for a in range(m) for b in range(m) if a != b) != m * (m - 1):
            bad.append(("offDiag", m))
    print("(f) 与 Lean 定理对应的数值断言（v2）  [n<=%d]" % NMAX)
    print("    partitionProb_merge_recursion：pp*C(k+1,2) == sum_{MergeInto} pp")
    print("    stateSum_eq_succ / stateSum_self / two_mul_choose_two_cast /")
    print("    card_pairSet（有序块对 = 2 iff MergeInto）/ card_offDiag")
    print("    => %s" % ("PASS" if not bad else "FAIL %r" % (bad[:8],)))
    return not bad


def check_g():
    """(2.1) 的**正向计数**（本轮新证）：从 `k` 块划分 `Q` 出发，一步去向恰 `C(k,2)` 个、
    且**互不相同**（对应 `KingmanStep.card_mergeTargets_cast` / `KingmanLaw.mergeTargets_gap`）。
    """
    print("=" * 78)
    print("(G) (2.1) 正向计数：一步去向 = C(k,2)  ← KingmanStep.card_mergeTargets_cast")
    bad = 0
    for n in range(2, NMAX + 1):
        for k in range(2, n + 1):
            want = math.comb(k, 2)
            parts = list(partitions_of(n, k))
            for Q in parts:
                outs = merge_outcomes(Q)
                if len(outs) != want or len(set(outs)) != want:
                    bad += 1
            print(f"   n={n} k={k}: 每个 {k} 块划分的去向数 = {want} = C({k},2)"
                  f"（{len(parts)} 个划分，全部互异）")
    print(f"   ✗ 失败数 = {bad}   " + ("✓ 全部通过" if bad == 0 else ""))
    assert bad == 0
    return True


def main():
    print("scripts/msc/kingman_jumpchain.py -- 精确有理数穷举复核（无 Monte Carlo）")
    print("=" * 78)
    oks = [check_a(), check_b(), check_c(), check_d(), check_e(), check_f(), check_g()]
    print("=" * 78)
    verdict = all(oks)
    print("VERDICT:", "PASS" if verdict else "FAIL", "   (n <= %d)" % NMAX)
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
