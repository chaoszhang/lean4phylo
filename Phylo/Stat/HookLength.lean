/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Laminar
import Phylo.Stat.RankedGeneTree

/-!
# `Phylo.Stat.HookLength` —— 树偏序的**钩长**（hook length）器材层

## 为什么需要这个模块

`Phylo/Stat/RankedGeneTree.lean` 的缺口 `rankedFiberCount_gap`（= SD2012 Remark 6 的一般 `n` 形式）

```text
|{g ∈ mergeHistories n : cladesOf n g = cladesOf n f}| = (n − 1)! / ∏_{C ∈ cladesOf n f, |C| ≥ 2} (|C| − 1)
```

要按「树偏序的 hook-length 公式」证明，需要把 `cladesOf n f`（一个 `Finset (Finset (Fin n))`）
提升成**树对象**、在树上定义钩长、再引用 hook-length 公式。
⚠️ **Mathlib 里没有 hook-length 公式**（全库 `grep -rn 'hook_length\|hookLength'` **0 命中**），
`linearExtension` 侧只有 `Mathlib/Order/Extension/Linear.lean` 的**基础设施**（无计数公式）。
故本模块**只提供器材**：树偏序的钩长定义与基本性质，**不声称**已证一般 `n` 的公式。

## 钩长口径

镶嵌族 `T : Finset (Finset α)` 上，把**内部结点**看成**非单点簇** `C`（`2 ≤ |C|`），
`C` 的孩子 = `C` 在 `T` 内的**极大真子簇**（`children`）。钩长定义为

```text
hook T C = |{ D ∈ T : 2 ≤ |D| ∧ D ⊆ C }|        -- 「C 子树内的内部结点数」（含 C 自己）
```

并证明它的**递归方程** `hook T C = 1 + Σ_{B ∈ children T C} hook T B`（`2 ≤ |C|`，待证），
这就是树偏序 hook-length 公式里那个 `s_v`（子树结点数）。

## 与验证过的数值结论对照（`n = 4`）

脚本 `scripts/msc/w12f_ranked_fiber_check.py` 已穷举验证 `n = 2..6`（零反例）。
`n = 4` 的两棵拓扑在 `cladesOf` 下的 `|C| ≥ 2` 部分与钩长：

| 拓扑 | `|C| ≥ 2` 的簇 | `hook` | `∏ hook` | 纤维（已证） |
|---|---|---|---|---|
| caterpillar `(((0,1),2),3)` | `{0,1}`, `{0,1,2}`, `univ` | `1, 2, 3` | `6` | `1`（`rankedFiberCount_012_3`） |
| balanced `((0,1),(2,3))` | `{0,1}`, `{2,3}`, `univ` | `1, 1, 3` | `3` | `2`（`rankedFiberCount_01_23`） |

⚠️ 「`(n−1)!/∏ hook` = 纤维大小」（hook-length 公式本身）**本模块没有证** ——
那正是缺口本体的组合内容。本模块交付：**钩长器材 + 与 `|C| − 1` 的一致性 + 具体数值**。

**注册行（由协调侧加入 `Phylo.lean`，紧跟 `import Phylo.Stat.RankedGeneTree` 之后）**：

```lean
import Phylo.Stat.HookLength
```
-/

namespace Phylo.Stat.HookLength

open Classical

variable {α : Type*} [DecidableEq α]

/-! ## §1 内部结点与「孩子」关系 -/

/-- `T` 中落在 `C` 之下的**非单点簇**（含 `C` 自己，当 `2 ≤ |C|` 时）。 -/
def internalBelow (T : Finset (Finset α)) (C : Finset α) : Finset (Finset α) :=
  T.filter fun D => 2 ≤ D.card ∧ D ⊆ C

/-- `internalBelow` 的成员刻画。 -/
theorem mem_internalBelow {T : Finset (Finset α)} {C D : Finset α} :
    D ∈ internalBelow T C ↔ D ∈ T ∧ 2 ≤ D.card ∧ D ⊆ C := by
  simp [internalBelow]

/-- **`C` 的孩子**：`C` 在 `T` 内的**极大真子簇**（依 `Finset` 的严格包含序）。

⚠️ 与 `Phylo.Laminar.IsChildOf` 的区别：那里的 `IsChildOf F A B` 走 `IsParentOf`
（`A` 是 `B` 的最小严格**超**集），是自顶向下的父子；这里是自底向上的「直接子簇」，
且 `T` 的角色是「可选孩子的池子」。 -/
def children (T : Finset (Finset α)) (C : Finset α) : Finset (Finset α) :=
  T.filter fun B => B ⊂ C ∧ ∀ D ∈ T, B ⊂ D → D ⊂ C → False

/-- `children` 的成员刻画。 -/
theorem mem_children {T : Finset (Finset α)} {C B : Finset α} :
    B ∈ children T C ↔ B ∈ T ∧ B ⊂ C ∧ ∀ D ∈ T, B ⊂ D → D ⊂ C → False := by
  simp [children]

/-- 孩子是 `T` 的元素。 -/
theorem children_mem {T : Finset (Finset α)} {C B : Finset α} (h : B ∈ children T C) :
    B ∈ T :=
  (mem_children.mp h).1

/-- 孩子真小于父。 -/
theorem children_ssubset {T : Finset (Finset α)} {C B : Finset α} (h : B ∈ children T C) :
    B ⊂ C :=
  (mem_children.mp h).2.1

/-- 孩子在 `T` 内是**极大**的真子簇。 -/
theorem children_maximal {T : Finset (Finset α)} {C B D : Finset α} (h : B ∈ children T C)
    (hD : D ∈ T) (hBD : B ⊂ D) : ¬ D ⊂ C :=
  (mem_children.mp h).2.2 D hD hBD

/-- 孩子之间**不含真包含**：若 `B, B'` 都是 `C` 的孩子，则 `B ⊂ B'` 为假。 -/
theorem children_antichain {T : Finset (Finset α)} {C B B' : Finset α}
    (hB : B ∈ children T C) (hB' : B' ∈ children T C) (h : B ⊂ B') : False :=
  children_maximal hB (children_mem hB') h (children_ssubset hB')

/-! ## §2 钩长 -/

/-- **簇 `C` 在 `T` 中的钩长**：`C` 子树内的**内部结点数**（含 `C` 自己），
即 `|{ D ∈ T : 2 ≤ |D| ∧ D ⊆ C }|`。这正是树偏序 hook-length 公式里的 `s_v`。 -/
def hook (T : Finset (Finset α)) (C : Finset α) : ℕ :=
  (internalBelow T C).card

/-- 钩长的展开式。 -/
theorem hook_def (T : Finset (Finset α)) (C : Finset α) :
    hook T C = (T.filter fun D => 2 ≤ D.card ∧ D ⊆ C).card :=
  rfl

/-- **钩长为正 ⟺ `C` 自己是内部结点**（`C ∈ T` 且 `2 ≤ |C|`）。 -/
theorem hook_pos_iff {T : Finset (Finset α)} {C : Finset α} (hC : C ∈ T) :
    0 < hook T C ↔ 2 ≤ C.card := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := Finset.card_pos.mp h
    obtain ⟨-, hD2, hDC⟩ := mem_internalBelow.mp hD
    have hcard : D.card ≤ C.card := Finset.card_le_card hDC
    omega
  · intro h
    exact Finset.card_pos.mpr ⟨C, mem_internalBelow.mpr ⟨hC, h, Finset.Subset.rfl⟩⟩

/-- **钩长为正**（`C` 是 `T` 中的非单点簇）。 -/
theorem hook_pos {T : Finset (Finset α)} {C : Finset α} (hC : C ∈ T) (h : 2 ≤ C.card) :
    0 < hook T C :=
  (hook_pos_iff hC).mpr h

/-- **单点簇的钩长为 `0`**（单点不是内部结点）。 -/
theorem hook_eq_zero_of_card_le_one {T : Finset (Finset α)} {C : Finset α}
    (h : C.card ≤ 1) : hook T C = 0 := by
  simp only [hook, internalBelow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro D hD hcon
  obtain ⟨h2, hDC⟩ := hcon
  have hcard : D.card ≤ C.card := Finset.card_le_card hDC
  omega

/-- 钩长只依赖 `T` 在 `C` 之下的部分：若两个族在 `C` 之下（`⊆ C`）一致，则钩长一致。 -/
theorem hook_congr_of_eq_below {T T' : Finset (Finset α)} {C : Finset α}
    (h : ∀ D, D ⊆ C → (D ∈ T ↔ D ∈ T')) : hook T C = hook T' C := by
  rw [hook_def, hook_def]
  congr 1
  ext D
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hD, h2, hDC⟩
    exact ⟨(h D hDC).mp hD, h2, hDC⟩
  · rintro ⟨hD, h2, hDC⟩
    exact ⟨(h D hDC).mpr hD, h2, hDC⟩

/-! ## §3 递归方程（hook-length 公式里的 `s_v` 递推） -/

/-- **任意非空真子簇都落在某个孩子里**（极大性）。

证：在 `{B ∈ T : D ⊆ B ∧ B ⊂ C}` 中取**基数最大**者 `B`（非空，因 `D` 在其中）；
若存在 `B' ∈ T` 使 `B ⊊ B' ⊊ C`，则 `B'` 亦在该集中且基数更大 —— 矛盾。 -/
theorem exists_children_superset {T : Finset (Finset α)} {C D : Finset α}
    (hD : D ∈ T) (hDC : D ⊂ C) :
    ∃ B ∈ children T C, D ⊆ B := by
  classical
  have hmem : D ∈ T.filter (fun B => D ⊆ B ∧ B ⊂ C) :=
    Finset.mem_filter.mpr ⟨hD, Finset.Subset.refl D, hDC⟩
  have hne' : (T.filter fun B => D ⊆ B ∧ B ⊂ C).Nonempty := ⟨D, hmem⟩
  obtain ⟨B, hB, hBmax⟩ :=
    Finset.exists_mem_eq_sup (T.filter fun B => D ⊆ B ∧ B ⊂ C) hne' Finset.card
  obtain ⟨hBT, hDB, hBC⟩ := Finset.mem_filter.mp hB
  refine ⟨B, mem_children.mpr ⟨hBT, hBC, ?_⟩, hDB⟩
  intro B' hB'T hBB' hB'C
  have hB'mem : B' ∈ T.filter (fun B => D ⊆ B ∧ B ⊂ C) :=
    Finset.mem_filter.mpr ⟨hB'T, Finset.Subset.trans hDB hBB'.1, hB'C⟩
  have h1 : B'.card ≤ B.card := hBmax ▸ Finset.le_sup hB'mem
  have h2 : B.card < B'.card := Finset.card_lt_card hBB'
  omega

/-- **大小 ≥ 2 的簇要么是 `C` 自己，要么落在某个孩子里**。 -/
theorem eq_or_mem_children {T : Finset (Finset α)} {C D : Finset α}
    (hD : D ∈ T) (_hD2 : 2 ≤ D.card) (hDC : D ⊆ C) :
    D = C ∨ ∃ B ∈ children T C, D ⊆ B := by
  rcases eq_or_lt_of_le hDC with h | h
  · exact Or.inl h
  · exact Or.inr (exists_children_superset hD h)

/-- **孩子的 `internalBelow` 两两不交**。

证：设 `D ∈ internalBelow T B ∩ internalBelow T B'`（于是 `2 ≤ |D|`，特别地 `D` 非空）。
若 `B ≠ B'`，则 `B ⊄ B'` 与 `B' ⊄ B`（孩子的极大性）；
但 `D ⊆ B`、`D ⊆ B'` 且 `D` 非空，两个 `T`-成员（`B, B'`）相交于非空集合，
故由 `T` 的**镶嵌性**（`LaminarFamily`）必有一方包含另一方 —— 矛盾。 -/
theorem internalBelow_pairwiseDisjoint {T : Finset (Finset α)} {C : Finset α}
    (hl : LaminarFamily T) :
    (children T C : Set (Finset α)).PairwiseDisjoint (fun B => internalBelow T B) := by
  intro B hB B' hB' hne'
  rw [Function.onFun, Finset.disjoint_left]
  intro D hDB hDB'
  obtain ⟨-, hD2, hDsubB⟩ := mem_internalBelow.mp hDB
  obtain ⟨-, -, hDsubB'⟩ := mem_internalBelow.mp hDB'
  have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
  have hBT : B ∈ T := children_mem hB
  have hB'T : B' ∈ T := children_mem hB'
  have hinter : (B ∩ B').Nonempty := hDne.mono (Finset.subset_inter hDsubB hDsubB')
  rcases hl B hBT B' hB'T with hsub | hsub | hdisj
  · exact children_antichain hB hB'
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne' heq⟩)
  · exact children_antichain hB' hB
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne' heq.symm⟩)
  · rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    obtain ⟨a, ha⟩ := hinter
    rw [hdisj] at ha
    exact absurd ha (Finset.notMem_empty a)

/-- **钩长的递归方程**：`hook T C = 1 + Σ_{B ∈ children T C} hook T B`（`C` 非单点）。

这正是树偏序 hook-length 公式里的 `s_v = 1 + Σ_{孩子 v} s_v`。 -/
theorem hook_eq_one_add_sum_children {T : Finset (Finset α)} {C : Finset α}
    (hl : LaminarFamily T) (hC : C ∈ T) (h2 : 2 ≤ C.card) :
    hook T C = 1 + ∑ B ∈ children T C, hook T B := by
  classical
  have hset : (T.filter fun D => 2 ≤ D.card ∧ D ⊆ C)
      = insert C ((children T C).biUnion fun B => internalBelow T B) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_biUnion]
    constructor
    · rintro ⟨hDT, hD2, hDC⟩
      rcases eq_or_mem_children hDT hD2 hDC with h | ⟨B, hB, hDB⟩
      · exact Or.inl h
      · exact Or.inr ⟨B, hB, mem_internalBelow.mpr ⟨hDT, hD2, hDB⟩⟩
    · rintro (hEq | ⟨B, hB, hDB⟩)
      · exact ⟨hEq ▸ hC, hEq ▸ h2, hEq ▸ Finset.Subset.refl D⟩
      · obtain ⟨hDT, hD2, hDsubB⟩ := mem_internalBelow.mp hDB
        exact ⟨hDT, hD2, hDsubB.trans (children_ssubset hB).1⟩
  have hnotmem : C ∉ (children T C).biUnion fun B => internalBelow T B := by
    rw [Finset.mem_biUnion]
    rintro ⟨B, hB, hCB⟩
    exact (children_ssubset hB).2 (mem_internalBelow.mp hCB).2.2
  have hcard : ((children T C).biUnion fun B => internalBelow T B).card
      = ∑ B ∈ children T C, (internalBelow T B).card :=
    Finset.card_biUnion fun B hB B' hB' hne' =>
      internalBelow_pairwiseDisjoint hl hB hB' hne'
  have : hook T C = (T.filter fun D => 2 ≤ D.card ∧ D ⊆ C).card := hook_def T C
  rw [this, hset, Finset.card_insert_of_notMem hnotmem, hcard]
  simp only [hook]
  omega

/-- 钩长不超过族的大小（平凡上界）。 -/
theorem hook_le_card {T : Finset (Finset α)} {C : Finset α} : hook T C ≤ T.card :=
  Finset.card_filter_le _ _

/-! ## §4 ★B 具体数值（`n = 3, 4`，与 `rankedFiberCount_*` 的既有结论对照）

下面的 `Tbal` / `Tcat` 是 `RankedGeneTree.lean` 里 `clades_01_23` / `clades_012_3` 的
「`|C| ≥ 2` 的那部分」（即 `n = 4` 两棵拓扑的**内部结**点集）。
钩长按 §2 的定义直接算出，与数值脚本 `scripts/msc/w12f_ranked_fiber_check.py` 的穷举结果一致。 -/

/-- balanced 拓扑 `((0,1),(2,3))` 的内部结点集 -/
def Tbal : Finset (Finset (Fin 4)) := ({{0, 1}, {2, 3}, Finset.univ} : Finset (Finset (Fin 4)))

/-- caterpillar 拓扑 `(((0,1),2),3)` 的内部结点集 -/
def Tcat : Finset (Finset (Fin 4)) := ({{0, 1}, {0, 1, 2}, Finset.univ} : Finset (Finset (Fin 4)))

example : (Tbal.filter fun D => 2 ≤ D.card) = Tbal := by decide
example : (Tcat.filter fun D => 2 ≤ D.card) = Tcat := by decide

-- balanced：`hook {0,1} = 1`、`hook {2,3} = 1`、`hook univ = 3`
example : hook Tbal ({0, 1} : Finset (Fin 4)) = 1 := by decide
example : hook Tbal ({2, 3} : Finset (Fin 4)) = 1 := by decide
example : hook Tbal Finset.univ = 3 := by decide

-- caterpillar：链 `{0,1} ⊂ {0,1,2} ⊂ univ`，钩长 `1, 2, 3`
example : hook Tcat ({0, 1} : Finset (Fin 4)) = 1 := by decide
example : hook Tcat ({0, 1, 2} : Finset (Fin 4)) = 2 := by decide
example : hook Tcat Finset.univ = 3 := by decide

-- 递归方程的具体 instance（`omega` 由 §3 的一般定理给出）
example : hook Tbal Finset.univ = 1 + ∑ B ∈ children Tbal Finset.univ, hook Tbal B := by
  decide

example : hook Tcat Finset.univ = 1 + ∑ B ∈ children Tcat Finset.univ, hook Tcat B := by
  decide

/-- ★ **`rankedFiberCount_three` 的钩长对照**：`n = 3` 的（唯一）拓扑的内部结点只有根，
其钩长为 `1`，故 `(3−1)!/1 = 2` —— 与 `cladesOf` 口径下的纤维计算一致（见 `RankedGeneTree.lean`）。 -/
example : hook ({(Finset.univ : Finset (Fin 3))} : Finset (Finset (Fin 3))) Finset.univ = 1 := by
  decide

end Phylo.Stat.HookLength
