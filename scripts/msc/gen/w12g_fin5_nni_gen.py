#!/usr/bin/env python3
# --------------------------------------------------------------------------------------------
# ★ 为何【不在】run_all.sh 的扫描面内（2026-10-13 W17 任务 B；老师 2026-10-12 20:1x 批准）
#   本文件是【生成器】：把样板机械产出并写入 Lean 文件；它【没有可判定断言】，也【不输出】 PASS。
#   run_all.sh 的判据是「exit 0 ＋ 自报 PASS/通过/OK」⇒ 生成器必然被判红，属【结构误判】而非真失败。
#   ⇒ 依老师批准移入 scripts/msc/gen/：run_all.sh 只 glob 它所在目录的 *.py，故子目录天然不在扫描面内；
#     这样就【不引入】任何新的排除清单，避免重演旧问题（README 记：硬编码清单曾漏掉 4 个新脚本 ⇒ 假绿）。
#   ★ 因此：本文件不是检查器，判据须另设（它的成功 ＝ 对目标 Lean 文件产出/补齐样板，且幂等）。
# --------------------------------------------------------------------------------------------
# -*- coding: utf-8 -*-
"""W12g-5 生成器：往 `Phylo/Algorithm/NNINeighborhood.lean` 追加 §8（`n = 5` 的 NNI 连通性实例）。

体例与文件里已有的 `Fin 4` 实例（`tv₀..tv₃`、`tree₀..tree₂`、`tree_nniMove₀₁` 等）一致：
split 用**结构字面量**（该文件不 import `SplitWeak`，故没有 `ofSideA`）+ 显式 `NNIMove` 见证链，
**不用** `decide` 硬算组合爆炸（唯一的 `decide` 用于「显式集合相等」这种小判定）。

用法：python3 scripts/msc/gen/w12g_fin5_nni_gen.py Phylo/Algorithm/NNINeighborhood.lean
幂等：若文件已含「## 8.」则不做任何事。
"""

import sys

N = 5
# (名字, 注释, sideA 元素, 另一侧元素)
SPLITS = [
    ('u₀', '平凡 split `{0} | {1,2,3,4}`', [0], [1, 2, 3, 4]),
    ('u₁', '平凡 split `{1} | {0,2,3,4}`', [1], [0, 2, 3, 4]),
    ('u₂', '平凡 split `{2} | {0,1,3,4}`', [2], [0, 1, 3, 4]),
    ('u₃', '平凡 split `{3} | {0,1,2,4}`', [3], [0, 1, 2, 4]),
    ('u₄', '平凡 split `{4} | {0,1,2,3}`', [4], [0, 1, 2, 3]),
    ('uA', '内部 split `{0,1} | {2,3,4}`（树 `T` 的内部边）', [0, 1], [2, 3, 4]),
    ('uB', '内部 split `{2,3} | {0,1,4}`（树 `T` 的另一条内部边）', [2, 3], [0, 1, 4]),
    ("uA'", "NNI 分解 `{0,2,3} | {1,4}`（同一条内部边的另一个分解）", [0, 2, 3], [1, 4]),
]


def lit(xs):
    return '{' + ', '.join(str(x) for x in xs) + '}'


def split_def(name, comment, a, b):
    return ('''/-- %s。 -/
def %s : Split (Fin %d) where
  parts i := if i = 0 then %s else %s
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide
''' % (comment, name, N, lit(a), lit(b)))


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'Phylo/Algorithm/NNINeighborhood.lean'
    src = open(path, encoding='utf-8').read()
    if 'NNI 连通性实例（W12g-5）' in src:
        print('§8 already present in', path, '— nothing to do (幂等)')
        return
    anchor = 'end Split'
    assert src.count(anchor) >= 1
    # 追加在文件最后一个 `end Split` 之前
    idx = src.rindex(anchor)
    body = '''/-! ## 8. `n = 5` 的 NNI 连通性实例（W12g-5）

体例同 §7.1 的 `Fin 4` 实例：**显式**给出两个二叉树的 split 系统与一次 `NNIMove` 见证。
`T = {5 条平凡} ∪ {uA, uB}`、`T' = {5 条平凡} ∪ {uA', uB}`；`uA → uA'` 由四块
`(A₁, B₁) = ({0}, {2,3})` 的 NNI 分解给出（`A₂ = {1}`、`B₂ = {4}`）。
⇒ `NNIDist T T' 1`、`nniConnectivity_gap 5 T T'`、`rfDistance = 2`。

boilerplate 由 `scripts/msc/gen/w12g_fin5_nni_gen.py` 生成。 -/

''' + '\n'.join(split_def(*s) for s in SPLITS) + '''
/-- ★C 二叉树 `T` 的 split 系统（5 条平凡 + 2 条内部）。 -/
def tree5 : Finset (Split (Fin 5)) := {u₀, u₁, u₂, u₃, u₄, uA, uB}

/-- ★C 二叉树 `T'` 的 split 系统（把 `uA` 换成它的 NNI 分解 `uA'`）。 -/
def tree5' : Finset (Split (Fin 5)) := {u₀, u₁, u₂, u₃, u₄, uA', uB}

/-- ★C **拆分数据自洽**：`uA` 按四块 `({0}, {2,3})` 的 NNI 分解给出 `uA'`。 -/
theorem uA_nniResolvent :
    uA.nniResolvent ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5))
      (by decide) (by decide) (by decide) (by decide) = uA' := by
  refine (KPartition.eq_iff_parts _ _).mpr ?_
  funext i
  by_cases hi : i = 0
  · subst hi
    show ({0} : Finset (Fin 5)) ∪ {2, 3} = {0, 2, 3}
    decide
  · have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    show (({0, 1} : Finset (Fin 5)) \\ {0}) ∪ (({2, 3, 4} : Finset (Fin 5)) \\ {2, 3}) = {1, 4}
    decide

/-- ★★★ **`n = 5` 的一次 NNI 移动**：`T → T'`（同一条内部边的另一个分解）。 -/
theorem tree5_nniMove : NNIMove tree5 tree5' := by
  refine ⟨uA, {0}, {2, 3}, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  rw [uA_nniResolvent]
  decide

/-- ★★ 一次移动 ⟹ RF 距离恰为 2。 -/
theorem tree5_rfDistance : rfDistance tree5 tree5' = 2 := nniMove_rfDistance tree5_nniMove

/-- ★★★ **`n = 5` 连通性实例**：`T` 与 `T'` 1 步可达。 -/
theorem tree5_connectivity : nniConnectivity_gap 5 tree5 tree5' :=
  ⟨1, nniDist_one_of_move tree5_nniMove⟩

/-- ★ `T ≠ T'`（一次 NNI 真的改动了系统）。 -/
theorem tree5_ne : tree5 ≠ tree5' := (nniMove_ne tree5_nniMove).symm

'''
    src = src[:idx] + body + src[idx:]
    open(path, 'w', encoding='utf-8', newline='\n').write(src)
    print('generated §8 (n=5 NNI) into', path)


if __name__ == '__main__':
    main()
