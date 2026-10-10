/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Laminar
import Phylo.Stat.RankedGeneTree
import Mathlib.Data.Nat.Choose.Multinomial

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

## 本模块**做到了**什么 / **没做到**什么（不夸大）

**已证（本模块，零 `sorry`）**：

| 块 | 声明 | 内容 |
|---|---|---|
| §1–§2 | `internalBelow` / `children` / `hook` + 成员刻画、`hook_pos`、`hook_eq_zero_of_card_le_one`、`hook_congr_of_eq_below` | 钩长器材 |
| §3 ★★ | `hook_eq_one_add_sum_children` | 钩长的**加法**递推 `s_v = 1 + Σ_{孩子} s_child` |
| §5 ★★ | `prod_hook_eq_hook_mul_prod_children` | 钩长积的**乘法**递推（hook-length 公式**分母**的递推） |
| §6 ★★ | `multinomial_mul_prod_factorial` / `multinomial_children_factorial` | 计数恒等式 `multinomial(N-1; N_B)·∏N_B! = (N-1)!` |
| §8 ★★ | `LE`（**自造**）＋ `LE_eq` ＋ `LE_eq_one_of_card_le_one` ＋ `hook_lt_of_mem_children` | 线性扩展数的**递推定义**与定义方程 |
| §4/§7/§8.1 ★B | 25 条 `example` | `n = 4` 两棵拓扑的钩长、钩长积、两条递推、计数恒等式、`LE` 的平凡定义方程 |

**⬜ 没做（hook-length 公式本体仍缺最后一环）**：

1. ~~线性扩展数 `LE` 的递推~~ —— **第五轮已做**：`LE` 按「根在首位 + 孩子子树块间插空」
   **递归定义**（§8），`LE_eq` 给出定义方程
   `LE T C = multinomial(hook 们) · ∏_B LE T B`。**但**：
2. ⬜ **由 §5 + §6 归纳出闭形式** `LE T C · ∏_{D ⊆ C} hook T D = (hook T C)!`
   —— **仍未做**。卡点很具体：`LE` 的**递归调用点**是 `(children T C).attach.prod`，
   要对它做归纳需要一条**自造的归纳原理**（把 `LE` 的 well-founded 递归
   `termination_by hook T C` 暴露成 `induction`），并额外把
   `attach.prod (fun Bx => LE T Bx.1 _)` 与 §5 的 `∏ B ∈ children T C, …` 对齐
   （`Finset.prod_attach`）。这两步**都不是数学难点，而是 Lean 基础设施**；
   我**没有**用 `sorry` 或半成品绕过它。
3. 第 (ii) 条（**不在本模块范围**）：`cladesOf` 的 clade 包含偏序的**线性扩展 ⟺ 合并史的 ranking**
   的显式双射 —— 这是 `rankedFiberCount_gap` 的**组合实体**。

⇒ 本模块交付的是**计数归纳的两块器材**（§5 分母递推 + §6 计数恒等式）
＋ **第五轮新增的 `LE` 递推定义**；**不是**缺口本体。
数值核对：`scripts/msc/w12f_hook_count_check.py`（`ALL_OK`）。

⚠️ **`LE` 的具体值不可 `decide`**：well-founded 递归定义内核不自动展开，
故 `LE Tbal univ = 2` 这类断言需要上面的归纳原理才能证；§8.1 只给了**平凡情形**
（单点簇、无孩子的非单点簇）的可展开见证。

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

/-- **孩子的钩长严格小于父**。

证：`B ∈ children T C` 给出 `B ⊂ C`、`B ∈ T`。于是
`internalBelow T B ⊊ internalBelow T C`（包含：`D ⊆ B ⊆ C`；严格：`C` 本身在
`internalBelow T C` 里但不在 `internalBelow T B` 里，因为那要求 `C ⊆ B`）。
取基数即得。 -/
theorem hook_lt_of_mem_children {T : Finset (Finset α)} {C B : Finset α}
    (hB : B ∈ children T C) (hC2 : 2 ≤ C.card) (hC : C ∈ T) :
    hook T B < hook T C := by
  have hsub : internalBelow T B ⊆ internalBelow T C := by
    intro D hD
    obtain ⟨hDT, hD2, hDB⟩ := mem_internalBelow.mp hD
    exact mem_internalBelow.mpr ⟨hDT, hD2, hDB.trans (children_ssubset hB).1⟩
  have hCmem : C ∈ internalBelow T C :=
    mem_internalBelow.mpr ⟨hC, hC2, Finset.Subset.refl C⟩
  have hCnotmem : C ∉ internalBelow T B := by
    intro hmem
    exact (children_ssubset hB).2 (mem_internalBelow.mp hmem).2.2
  have hssub : internalBelow T B ⊂ internalBelow T C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hCnotmem (heq ▸ hCmem)⟩
  exact Finset.card_lt_card hssub

/-! ## §5 hook 积的递归（hook-length 公式分母的**乘法**递推）

`hook_eq_one_add_sum_children` 是钩长的**加法**递推；hook-length 公式真正需要的是
`∏ s_v` 的**乘法**递推：

```text
∏_{D ∈ T, 2 ≤ |D|, D ⊆ C} hook T D  =  hook T C · ∏_{B ∈ children T C} (∏_{D ⊆ B} hook T D)
```

（左边是 `C` 子树内所有内部结点的钩长积，右边把 `s_C` 提出来、再乘各孩子子树的钩长积。）
这条 + 下一批的「线性扩展数递推」+ 库内 `Nat.multinomial_spec` 一起给出
`LE(T) = N!/∏ s_v` 的计数归纳（见 §6 的说明与 `scripts/msc/w12f_hook_count_check.py`）。 -/

/-- **钩长积在 `internalBelow` 上的下钻**：对每个孩子求和等于对全体孩子并集求和。 -/
theorem prod_internalBelow_biUnion {T : Finset (Finset α)} {C : Finset α}
    (hl : LaminarFamily T) :
    ∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D
      = ∏ D ∈ (children T C).biUnion (fun B => internalBelow T B), hook T D := by
  classical
  rw [Finset.prod_biUnion]
  exact fun B hB B' hB' hne' => internalBelow_pairwiseDisjoint hl hB hB' hne'

/-- ★★ **钩长积的乘法递推**（`C` 非单点）：

```text
∏_{D ∈ internalBelow T C} hook T D  =  hook T C · ∏_{B ∈ children T C} ∏_{D ∈ internalBelow T B} hook T D
```

即 hook-length 公式分母的递推。证：把 §3 的集合恒等式
`internalBelow T C = {C} ⊎ ⋃_B internalBelow T B` 取 `Finset.prod`，
并用 `hook_eq_one_add_sum_children` 把 `Σ_B (internalBelow T B).card` 认成 `hook T C - 1`。 -/
theorem prod_hook_eq_hook_mul_prod_children {T : Finset (Finset α)} {C : Finset α}
    (hl : LaminarFamily T) (hC : C ∈ T) (h2 : 2 ≤ C.card) :
    ∏ D ∈ internalBelow T C, hook T D
      = hook T C * ∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D := by
  classical
  -- (1) 集合恒等式（与 §3 同）
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
  -- (2) 并集的乘积 = 各孩子乘积之积
  have hbU : ∏ D ∈ (children T C).biUnion (fun B => internalBelow T B), hook T D
      = ∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D :=
    (prod_internalBelow_biUnion (T := T) (C := C) hl).symm
  -- (3) `Σ_B (internalBelow T B).card = hook T C - 1`
  have hcard : ∑ B ∈ children T C, (internalBelow T B).card = hook T C - 1 := by
    have h1 : (internalBelow T C).card
        = (insert C ((children T C).biUnion fun B => internalBelow T B)).card := by
      show (T.filter fun D => 2 ≤ D.card ∧ D ⊆ C).card = _
      rw [hset]
    have h2' : (internalBelow T C).card
        = 1 + ∑ B ∈ children T C, (internalBelow T B).card := by
      rw [h1, Finset.card_insert_of_notMem hnotmem,
        Finset.card_biUnion
          (fun B hB B' hB' hne' => internalBelow_pairwiseDisjoint hl hB hB' hne')]
      omega
    have h3 : hook T C = (internalBelow T C).card := rfl
    omega
  -- (4) 合并
  have hprod : ∏ D ∈ internalBelow T C, hook T D
      = hook T C * ∏ D ∈ (children T C).biUnion (fun B => internalBelow T B), hook T D := by
    have h2' : ∏ D ∈ insert C ((children T C).biUnion fun B => internalBelow T B), hook T D
        = hook T C * ∏ D ∈ (children T C).biUnion (fun B => internalBelow T B), hook T D :=
      Finset.prod_insert hnotmem
    rw [show (∏ D ∈ internalBelow T C, hook T D)
        = ∏ D ∈ insert C ((children T C).biUnion fun B => internalBelow T B), hook T D from by
      show (∏ D ∈ T.filter (fun D => 2 ≤ D.card ∧ D ⊆ C), hook T D) = _
      rw [hset]]
    exact h2'
  rw [hprod, hbU]

/-! ## §6 计数恒等式（hook-length 公式计数归纳里唯一的算术一步）

hook-length 公式 `LE(T) = N!/∏_v s_v` 的**计数归纳**骨架（本批给出前两块器材）：

1. **§5** `prod_hook_eq_hook_mul_prod_children` —— 分母 `∏ s_v` 的乘法递推；
2. **本节的** `multinomial_mul_prod_factorial` —— `multinomial(N-1; N_B) · ∏_B N_B! = (N-1)!`；
3. ⬜ **仍未做**：线性扩展数 `LE` 的递推
   `LE(T) = multinomial(N-1; N_1..N_k) · ∏_B LE(T_B)`
   以及由 1+2 归纳出 `LE(T) = N!/∏ s_v`（见 §7 的诚实边界）。

本节只落**第 2 块**（纯算术，库内 `Nat.multinomial_spec` 的直接搬运）：

* `Nat.multinomial_spec : ∏ i ∈ s, (f i)! * multinomial s f = (∑ i ∈ s, f i)!`（`ℕ` 形式）；
* 本节的 `multinomial_mul_prod_factorial` 是它在 `ℤ` 上的等价形式（顺序不同、便于后续相除）。 -/

/-- **计数恒等式**：`multinomial(s, f) · ∏_{i ∈ s} (f i)! = (∑_{i ∈ s} f i)!`（`ℤ` 形式）。

即库内 `Nat.multinomial_spec` 的等价改写（把 `∏(f i)!` 移到右边、系数放左边）。 -/
theorem multinomial_mul_prod_factorial (s : Finset ℕ) (f : ℕ → ℕ) :
    ((Nat.multinomial s f : ℕ) : ℤ) * ∏ i ∈ s, ((f i).factorial : ℤ)
      = (((∑ i ∈ s, f i).factorial : ℕ) : ℤ) := by
  rw [← Nat.cast_prod, ← Nat.cast_mul, mul_comm, Nat.multinomial_spec]

/-- 树形版本的计数恒等式：`N = 1 + Σ_B N_B` 时
`multinomial(N-1; N_B) · ∏_B N_B! = (N-1)!`。 -/
theorem multinomial_children_factorial (Ns : Finset ℕ) (N : ℕ)
    (hN : N = 1 + ∑ n ∈ Ns, n) :
    ((Nat.multinomial Ns (fun n => n) : ℕ) : ℤ) * ∏ n ∈ Ns, ((n.factorial : ℕ) : ℤ)
      = (((N - 1).factorial : ℕ) : ℤ) := by
  subst hN
  rw [multinomial_mul_prod_factorial]
  norm_num

/-! ## §7 ★B 具体数值（乘法递推 + 计数恒等式，`n = 4`）

下面把 §5 的乘法递推与 §6 的计数恒等式在**具体拓扑**上复算（`n = 4`）：

* caterpillar `Tcat = {{0,1},{0,1,2},univ}`：钩长 `1, 2, 3`，`∏ hook = 6`；
* balanced `Tbal = {{0,1},{2,3},univ}`：钩长 `1, 1, 3`，`∏ hook = 3`；
* 计数恒等式在 `Tcat` 上：`multinomial {2} id · 2! = 2!`（`N-1 = 2`）。 -/

-- 钩长积（`Tcat`：1·2·3 = 6；`Tbal`：1·1·3 = 3）
example : ∏ D ∈ internalBelow Tcat Finset.univ, hook Tcat D = 6 := by decide
example : ∏ D ∈ internalBelow Tbal Finset.univ, hook Tbal D = 3 := by decide

-- 乘法递推的两个 instance
example :
    ∏ D ∈ internalBelow Tcat Finset.univ, hook Tcat D
      = hook Tcat Finset.univ
        * ∏ B ∈ children Tcat Finset.univ, ∏ D ∈ internalBelow Tcat B, hook Tcat D := by
  decide
example :
    ∏ D ∈ internalBelow Tbal Finset.univ, hook Tbal D
      = hook Tbal Finset.univ
        * ∏ B ∈ children Tbal Finset.univ, ∏ D ∈ internalBelow Tbal B, hook Tbal D := by
  decide

-- 计数恒等式在具体 `N_B` 上的实例
-- `Ns` 是 `Finset`（无重集），故用 `{1, 2}` / `{1, 3}` 这类取值
example : ((Nat.multinomial {1, 2} (fun n => n) : ℕ) : ℤ)
    * ∏ n ∈ ({1, 2} : Finset ℕ), ((n.factorial : ℕ) : ℤ)
      = (((3 : ℕ).factorial : ℕ) : ℤ) := by
  decide
example : ((Nat.multinomial {1, 1} (fun _ => 1) : ℕ) : ℤ)
    * ∏ _n ∈ ({1} : Finset ℕ), ((1 : ℕ).factorial : ℤ)
      = (((1 : ℕ).factorial : ℕ) : ℤ) := by
  decide
-- §6 的树形版本在 caterpillar（`N_B = 2`、`N = 3`）上的 instance
example : ((Nat.multinomial ({2} : Finset ℕ) (fun n => n) : ℕ) : ℤ)
    * ∏ n ∈ ({2} : Finset ℕ), ((n.factorial : ℕ) : ℤ)
      = ((((3 : ℕ) - 1).factorial : ℕ) : ℤ) :=
  multinomial_children_factorial ({2} : Finset ℕ) 3 (by decide)

/-! ## §8 线性扩展数 `LE`（**自造**；Mathlib 无此计数）

⚠️ **三次 grep 确认**：Mathlib 的 `Mathlib/Order/Extension/Linear.lean` **只给
`LinearExtension` 类型别名与「把偏序延拓成线序」的存在性**（`extend_partialOrder`），
**没有**线性扩展的**计数**；按 `linearExtension` / `topological` / `Nat.card ∘ LinearExtension`
搜计数式引理 **全部 0 命中**。⇒ 本节的 `LE` 是**自造**的
（本会话第三次「库里没有」：`hook_length` 0 命中、`Measure.infinitePi`、此处）。

### 定义口径（**递归**，与树偏序的线性扩展一一对应）

树偏序：结点 = `internalBelow T C`（内部结点），序 = `⊊`。
线性扩展里**根必在首位**，其余位置由各**孩子子树**的线性扩展**块间插空**得到：

```text
LE T C  =  multinomial(N_B 们) · ∏_B LE T B          （2 ≤ |C|）
LE T C  =  1                                          （否则）
```

`N_B = hook T B`（孩子子树内的内部结点数）。**待证结论**是 §9 的闭形式 `LE · ∏s = N!`
（**不是**把结论当定义）。 -/

/-- **线性扩展数** `LE T C hC`（`hC : C ∈ T` 保证 `C` 在簇池里）。

对 `hook T C` 做 well-founded 递归；递归调用在 `children T C` 上
（孩子的 `hook` 严格更小，见 `hook_lt_of_mem_children`）。 -/
noncomputable def LE (T : Finset (Finset α)) (C : Finset α) (_hC : C ∈ T) : ℕ :=
  if _hcard : 2 ≤ C.card then
    Nat.multinomial (children T C) (fun B => hook T B) *
      (children T C).attach.prod (fun Bx : { B // B ∈ children T C } =>
        LE T Bx.1 (children_mem Bx.2))
  else 1
termination_by hook T C
decreasing_by
  show hook T Bx.1 < hook T C
  exact hook_lt_of_mem_children Bx.2 (by omega) _hC

theorem LE_eq (T : Finset (Finset α)) (C : Finset α) (hC : C ∈ T) (h2 : 2 ≤ C.card) :
    LE T C hC = Nat.multinomial (children T C) (fun B => hook T B) *
      (children T C).attach.prod (fun Bx : { B // B ∈ children T C } =>
        LE T Bx.1 (children_mem Bx.2)) := by
  rw [LE, dite_eq_left h2]

/-- **单点簇的 `LE` 为 `1`**（没有内部结点 ⇒ 恰一个空线性扩展）。 -/
theorem LE_eq_one_of_card_le_one {T : Finset (Finset α)} {C : Finset α} (hC : C ∈ T)
    (h : C.card ≤ 1) : LE T C hC = 1 := by
  rw [LE, dite_eq_right (by omega)]

/-! ### §8.1 ★B 见证：`LE` 的**定义方程**在具体（平凡）簇上可展开

⚠️ 说明：`LE` 是 well-founded 递归定义，内核**不会**自动展开它，
故 `decide` / `simp` **算不出** `LE Tbal univ = 2` 这类具体值
（需要专门的「递归方程 + 归纳」工具，见 §9 的 ⬜）。
但**平凡情形**可以直接用 `LE_eq_one_of_card_le_one` 与定义方程读出。 -/

-- 单点簇：`LE = 1`
example : LE ({({0} : Finset (Fin 3))} : Finset (Finset (Fin 3))) {0} (by decide) = 1 :=
  LE_eq_one_of_card_le_one (by decide) (by decide)

-- 非单点簇但族里没有它的真子簇：`children = ∅`
example : children ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) {0, 1} = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨B, hB⟩
  obtain ⟨hBT, hBsub, -⟩ := mem_children.mp hB
  rw [Finset.mem_singleton] at hBT
  exact hBsub.2 (hBT ▸ Finset.Subset.refl B)

-- 该簇的钩长为 `1`（自己是内部结点，之下没有别的内部结点）
example : hook ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) {0, 1} = 1 := by
  rw [hook_def]
  decide

end Phylo.Stat.HookLength
