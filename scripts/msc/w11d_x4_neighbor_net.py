#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W11d / X4 —— Neighbor-Net（Bryant & Moulton 2004, MBE 21(2):255-265）环形 split 穷举检验。

纯标准库；**全部精确组合计数**（bitmask 整数运算，无浮点、无 Monte Carlo、无随机）。

文献：references/md/BryantMoulton2004_NeighborNetAgglomerativePhylogeneticNetworks.md
  * 行 321-329：环形 split 系统的定义（圆序下每个 split 都是「一段弧 | 其余」）
  * 行 249-253：相容（compatible）
  * 弱相容（Bandelt-Dress 1992，库内 Phylo/SplitWeak.lean）：不存在四点被**三个** split
    按三种方式 2|2 分开（即不存在「冲突四点」）

检验项
------
(1) ★★ 「环形 ⟹ 弱相容」：对 n = 4,5,6 穷举固定圆序下弧族的**所有子集**（= 所有环形系统），
    断言其中没有一个含冲突四点。对应 Lean 主定理 `NeighborNet.weaklyCompatible_of_circular`。
(2) ★B 「环形 ⇏ 两两相容」：在 n = 4,5 上找出**最小**的「环形但不两两相容」系统
    （Lean：`NeighborNet.exists_circular_not_pairwiseCompatible`）。
(3) ★B 「弱相容 ⇏ 环形？」：n = 5 上穷举**全部** 2^15 个 split 系统，同时判定环形与弱相容，
    报告两者的包含关系与最小差集元素（若有）。这是本题的「先造反例检查」。
(4) ★C 4 taxon 端到端：三个 2|2 quartet split 全在族内 ⟹ 非环形
    （Lean：`NeighborNet.not_circular_four_quartets` / `circular_not_all_three_quartets`）。
"""

from itertools import combinations
from functools import lru_cache


# ---------------------------------------------------------------- 基本结构

def all_splits(n):
    """n 个 taxon 上所有 split 的规范 bitmask（约定：bit 0 恒在 A 侧）。"""
    full = (1 << n) - 1
    out = set()
    for m in range(1, full):
        canon = m if (m & 1) else (full ^ m)
        out.add(canon)
    return sorted(out)


def parts_of(mask, n):
    a = [i for i in range(n) if (mask >> i) & 1]
    b = [i for i in range(n) if not (mask >> i) & 1]
    return a, b


def separates(mask, i, j):
    return ((mask >> i) & 1) != ((mask >> j) & 1)


def pair_label(mask, quad):
    """`mask` 在四点 `quad`（升序 4 元组）上诱导的 2|2 划分编号；非 2|2 时返回 None。

    0: {q0,q1}|{q2,q3}   1: {q0,q2}|{q1,q3}   2: {q0,q3}|{q1,q2}

    记 s = (q0 是否与 q1/q2/q3 分开)：恰好三种 2|2 对应
    [F,T,T] / [T,F,T] / [T,T,F]；其余四种（全同、全异、[F,F,T]、[F,T,F]）都是 1|3。
    """
    q0, q1, q2, q3 = quad
    s = tuple(separates(mask, q0, q) for q in (q1, q2, q3))
    return {(False, True, True): 0,
            (True, False, True): 1,
            (True, True, False): 2}.get(s)


def has_conflicting_quartet(system, n):
    """弱相容的否命题：存在四点与三个成员分别诱导三种 2|2（库内 `HasConflictingQuartet`）。"""
    sys_list = list(system)
    for quad in combinations(range(n), 4):
        seen = set()
        for mask in sys_list:
            lab = pair_label(mask, quad)
            if lab is not None:
                seen.add(lab)
        if len(seen) == 3:
            return quad
    return None


def is_weakly_compatible(system, n):
    return has_conflicting_quartet(system, n) is None


# ---------------------------------------------------------------- 环形序

def arcs_of_order(order):
    """圆序 `order`（taxon 元组）下所有弧 split 的规范 bitmask 集合。

    文献行 324-327：{x_i, x_{i+1}, ..., x_j} 及其余集。等价地：圆上一切「连续段」。
    """
    n = len(order)
    full = (1 << n) - 1
    out = set()
    for i in range(n):
        for length in range(1, n):          # 长度 1..n-1（真子集）
            m = 0
            for k in range(length):
                m |= 1 << order[(i + k) % n]
            canon = m if (m & 1) else (full ^ m)
            out.add(canon)
    return out


def cyclic_orders(n):
    """n 元集合上所有**本质不同**的圆序（固定 0 在首位，商掉反向）。"""
    from itertools import permutations
    rest = [x for x in range(1, n)]
    seen = set()
    for p in permutations(rest):
        seq = (0,) + p
        rev = (0,) + tuple(reversed(p))
        key = min(seq, rev)
        if key not in seen:
            seen.add(key)
            yield seq


def is_circular(system, n, orders=None):
    """`system` 是否为某个圆序下的环形 split 系统。"""
    if orders is None:
        orders = list(cyclic_orders(n))
    return any(system <= arcs_of_order(o) for o in orders)


# ---------------------------------------------------------------- (1) 环形 ⟹ 弱相容

def check_circular_implies_weak(n):
    """穷举固定圆序下弧族的所有子集（= 所有环形系统），返回 (子集数, 反例列表)。"""
    arcs = sorted(arcs_of_order(tuple(range(n))))
    full = (1 << n) - 1
    bad = []
    total = 0
    for r in range(len(arcs) + 1):
        for sub in combinations(arcs, r):
            total += 1
            q = has_conflicting_quartet(sub, n)
            if q is not None:
                bad.append((sub, q))
                if len(bad) > 3:
                    return total, bad
    return total, bad


# ---------------------------------------------------------------- 主流程

def report(title):
    print("=" * 72)
    print(title)
    print("=" * 72)


def main():
    ok = True

    report("[1] ★★ 环形 ⟹ 弱相容（穷举弧族的所有子集）")
    for n in (4, 5, 6):
        total, bad = check_circular_implies_weak(n)
        print("  n=%d：子集数 %d，含冲突四点者 %d" % (n, total, len(bad)))
        if bad:
            ok = False
            print("    反例（split 集, 冲突四点）= %r" % (bad[0],))
    print("  ⇒ 与 Lean `NeighborNet.weaklyCompatible_of_circular` 一致" if ok
          else "  ⇒ !! 反例存在，与主定理矛盾 !!")

    report("[2] ★B 环形 ⇏ 两两相容（最小反例）")
    for n in (4, 5):
        arcs = sorted(arcs_of_order(tuple(range(n))))
        found = None
        for r in range(1, len(arcs) + 1):
            for sub in combinations(arcs, r):
                inc = [(s, t) for s, t in combinations(sub, 2)
                       if not _compatible(s, t, n)]
                if inc and is_weakly_compatible(sub, n):
                    found = (sub, inc[0])
                    break
            if found:
                break
        sub, (s, t) = found
        print("  n=%d 最小（按基数）：|F|=%d  %s" % (n, len(sub), _fmt(sub, n)))
        print("      不相容对：%s 与 %s" % (_fmt([s], n), _fmt([t], n)))
        print("      仍弱相容：%s" % is_weakly_compatible(sub, n))
    print("  ⇒ 环形类是相容类的**严格**推广（Lean：`exists_circular_not_pairwiseCompatible`）")

    report("[3] ★B 弱相容 ⇏ 环形？（n = 5 全枚举 2^15 个 split 系统）")
    n = 5
    orders = list(cyclic_orders(n))
    arc_families = [frozenset(arcs_of_order(o)) for o in orders]
    splits = all_splits(n)
    print("  split 总数 %d，圆序数 %d" % (len(splits), len(orders)))
    stats = {"circ_weak": 0, "circ_notweak": 0, "weak_notcirc": 0, "neither": 0}
    weak_not_circ_examples = []
    circ_not_weak_examples = []
    for r in range(len(splits) + 1):
        for sub in combinations(splits, r):
            fs = frozenset(sub)
            circ = any(fs <= af for af in arc_families)
            weak = is_weakly_compatible(fs, n)
            if circ and weak:
                stats["circ_weak"] += 1
            elif circ and not weak:
                stats["circ_notweak"] += 1
                if len(circ_not_weak_examples) < 3:
                    circ_not_weak_examples.append(sub)
            elif weak and not circ:
                stats["weak_notcirc"] += 1
                if len(weak_not_circ_examples) < 3:
                    weak_not_circ_examples.append(sub)
            else:
                stats["neither"] += 1
    print("  环形∧弱相容 %d ；环形∧¬弱相容 %d ；弱相容∧¬环形 %d ；都非 %d"
          % (stats["circ_weak"], stats["circ_notweak"],
             stats["weak_notcirc"], stats["neither"]))
    if stats["circ_notweak"]:
        ok = False
        print("  !! 环形但非弱相容：%r" % (_fmt(circ_not_weak_examples[0], n),))
    if weak_not_circ_examples:
        ex = min(weak_not_circ_examples, key=len)
        print("  最小「弱相容但非环形」例子：%s（|F|=%d）" % (_fmt(ex, n), len(ex)))
    else:
        print("  n=5 上不存在「弱相容但非环形」的系统（弱相容 ⇒ 环形，n=5）")

    report("[4] ★C 4 taxon：三个 quartet split 全在族内 ⟹ 非环形")
    n = 4
    full = (1 << n) - 1
    quartets = []
    for m in range(1, full):
        a, b = parts_of(m, n)
        if len(a) == 2 and (m & 1):
            quartets.append(m)
    print("  2|2 split（含 taxon 0 的一侧）：%s" % _fmt(quartets, n))
    for o in cyclic_orders(n):
        fam = arcs_of_order(o)
        hit = [q for q in quartets if q in fam]
        print("  圆序 %s：弧族含 2|2 split %s" % (list(o), _fmt(hit, n)))
        assert len(hit) <= 2, "圆序下最多含两个 quartet split"
    three = frozenset(quartets)
    print("  三个 quartet 全体是否环形：%s" % is_circular(three, n))
    assert not is_circular(three, n)
    print("  ⇒ 与 Lean `NeighborNet.not_circular_four_quartets` 一致")

    print()
    print("ALL CHECKS PASSED" if ok else "FAILURES PRESENT")
    return 0 if ok else 1


# ---------------------------------------------------------------- 小工具

def _compatible(s, t, n):
    """两个 split 相容 ⟺ 四个交至少一个为空（库内 `Split.Compatible`）。"""
    a, b = parts_of(s, n)
    c, d = parts_of(t, n)
    for x in (a, b):
        for y in (c, d):
            if not (set(x) & set(y)):
                return True
    return False


def _fmt(system, n):
    out = []
    for m in sorted(system):
        a, b = parts_of(m, n)
        out.append("{%s}|{%s}" % (",".join(map(str, a)), ",".join(map(str, b))))
    return "{" + ", ".join(out) + "}"


if __name__ == "__main__":
    raise SystemExit(main())
