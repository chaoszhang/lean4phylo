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
| §9 ★★ | `LE_induction`（**自造归纳原理**）＋ `attach_prod_LE`（`attach.prod` ↔ `Finset.prod` 桥接）＋ `two_le_card_of_child` | 闭形式归纳所需的**两件基础设施**（第七轮落地） |
| §9.2 ★D | `Thgood` ＋ `example` | 「`hgood` 一般不成立」的**已核反例**。★ **2026-10-15 W20 任务 C 更正**：本行原写「§9.1/§9.2 ｜ `Tcex` / `Thgood` + 4 条 `example`」，但经核（依据 = 本文件内 `grep -nE 'def T[a-zA-Z]+'` 与 `grep -n '§9.1'`）**全库不存在名为 `Tcex` 的声明**、**也不存在 §9.1 这一节**，故删去该虚指项并把节号改准 ✓ |
| **§10 ★★★** | **`LE_mul_prod_hook_eq_factorial`** ＋ `internalBelow_eq_empty_of_card_le_one` ＋ `laminarFamily_Tcat/_Tbal` | **hook-length 公式本体：`LE · ∏s = N!`**（第八轮落地，(i) **收口**） |
| **§13 ★★★★** | **`hook_cladesOf_eq_card_sub_one`** ＋ `rankedFiberCount_gap_of_LE` | **(O2) 已证**：`hook (cladesOf n f) C = C.card - 1`（`2 ≤ C.card`，无额外假设）；缺口现在**只剩 (O1)**（W25 泳道 C 落地） |
| **§14.2–§14.3 ★★★** | **`card_cladesOf`** ＋ **`card_filter_nonsingleton_cladesOf`** ＋ **`existsUnique_creation_level`** ＋ `children_fiberOf_chainMap_succ` | **层分解无重（全局版）**：`|cladesOf n f| = 2n-1`、非单点 clade 恰 `n-1` 个、每个非单点 clade 的**创建步唯一**且 `children` 恰为该步被合并的两块 —— (O1) 具名缺件 ① 已落地（W26 泳道 b） |
| §10.1 ★B | 4 条 `example` | `LE Tcat = 1` / `LE Tbal = 2` —— 与既有**纤维数** `rankedFiberCount_012_3 = 1` / `rankedFiberCount_01_23 = 2` **对上** |
| **§14.4–§14.5 ★★★★** | **`reconstruct`** ＋ **`reconstructStep_eq`** ＋ **`reconstruct_newClade_eq`** ＋ **`cladesOf_reconstruct_newClade`** ＋ **`eq_of_newClade_eq`** ＋ **`image_newClade`** / **`existsUnique_newClade`** | **(O1) 重建映射**：由「clade 集 ＋ 创建块」按最小元读出合并对，重建出的合并史**就是** `f`（左逆），故 `cladesOf` 复原、`f ↦ (cladesOf, newClade)` **单射**；且 `k ↦ newClade f k` **恰枚举**非单点 clade（**满射**）—— (O1) 的「纤维 ↪ 创建序」两向已通（W26 泳道 f） |
| **§15 ★★★** | **`LinExt`** ＋ `LinExt_eq_one_of_hook_eq_zero` ＋ 2 条 `example` | **线性扩展数（(O1) 计数一侧的语义对象）**：`internalBelow T C` 在 `⊊` 下的线性扩展数（`decide` 可算 ⇒ `n = 4` 取值 `Tcat = 1` / `Tbal = 2`，与 §10.1 的 `LE` 及纤维数对上）。⬜ 交错引理 `LinExt = multinomial · ∏ LinExt 孩子` **未证**（W26 泳道 f） |
| §4/§7/§8.1 ★B | 25 条 `example` | `n = 4` 两棵拓扑的钩长、钩长积、两条递推、计数恒等式、`LE` 的平凡定义方程 |

**✅ (i) 已收口（第八轮）**：hook-length 公式本体
`LE T C hC · ∏_{D ⊆ C} hook T D = (hook T C)!` 已证（§10，需 `LaminarFamily T`）。
⚠️ 但 **(i) 只是「计数」那一半**：`LE` 与 `rankedFiberCount` 的**显式双射**（(ii)）**仍未做** ——
§10.1 只给出**具体拓扑上数值一致**（`LE = 1 / 2` 对上纤维 `1 / 2`），不是一般 `n` 的双射。

**✅ 第九轮：本定理所需的 `LaminarFamily T` 在预期用例上已兑现** ——
`RankedGeneTree.lean` 新增
`laminarFamily_cladesOf : LaminarFamily (cladesOf n f)`（对**任意** `f`，不要求 `IsMergeHistory`），
故 `LE_mul_prod_hook_eq_factorial` 可直接以 `T := cladesOf n f` 使用
（此前 `LaminarFamily` 只是假设）。⬜ 剩余缺口仍是 (ii) 的**显式双射**（见 `RankedGeneTree.lean` 的登记）。

**⬜ 仍未做**：

1. ~~线性扩展数 `LE` 的递推~~ —— **第五轮已做**：`LE` 按「根在首位 + 孩子子树块间插空」
   **递归定义**（§8），`LE_eq` 给出定义方程
   `LE T C = multinomial(hook 们) · ∏_B LE T B`。**但**：
2. ✅ ~~由 §5 + §6 归纳出闭形式~~ —— **第八轮已证**（§10 `LE_mul_prod_hook_eq_factorial`）。原文：`LE T C · ∏_{D ⊆ C} hook T D = (hook T C)!`
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

/-! ## §9 (a) `LE` 归纳原理 与 (b) `attach.prod` 桥接 —— **第七轮已落地**

本轮目标是把 §10 闭形式归纳所需的两件 Lean 基础设施做出来。**两件都没能过 elaboration**，
下面把**精确失败模式**与**根因分析**记全，供后续轮次接手。

### (a) `LE` 的归纳原理

**想要的形状**：`∀ C ∈ T, 2 ≤ C.card → (∀ B ∈ children T C, P B) → P C` ⇒
`∀ C ∈ T, 2 ≤ C.card → P C`（对 `hook T C` 良基归纳）。

⚠️ **根因（本轮最重要的发现）**：把归纳假设用在孩子 `B` 上时，
`hook_lt_of_mem_children` 需要 **孩子自己的** 前提 `2 ≤ B.card`，
但 **`B ∈ children T D` 并不蕴含 `2 ≤ B.card`**！**反例**：
取 `T = {∅, {y}}`、`D = {y}`，则 `∅ ⊂ {y}` 且 `T` 中没有 `D'` 满足 `∅ ⊊ D' ⊊ {y}`，
故 `∅ ∈ children T D`，而 `∅.card = 0`。
⇒ 归纳原理需要**额外的结构假设**把这种退化的孩子排除掉
（例如「`T` 中每个 ≥2 元素的成员，其孩子都 ≥2 元素」，或对
`T = cladesOf n f` 直接验证）。**这不是 Lean 簿记问题，而是原理本身需要加强前提。**

**另外两个（次要的）elaboration 障碍**（都已试过、都失败）：

1. `WellFounded.induction (r := InvImage (· < ·) (hook T)) (InvImage.wf (r := (· < ·)) … )`
   —— 在**独立探针**里同形状通过，但在本模块报
   `… of sort Prop but is expected to have type Finset α`（隐式 `C`/`α` 错配）；
   即使把 `maxHeartbeats` 提到 800000，仍报**确定性 `whnf` 超时**
   （`InvImage` + `hook` 在 `Finset (Finset α)` + `Classical.decEq` 下的定义展开代价过高）。
2. `Nat.strongRecOn` 版本 —— motive 必须是 `Sort`，写成 `∀ D, D ∈ T → 2 ≤ D.card → hook T D = m → P D`
   时 Lean 报 `motive has type Prop of sort Type but is expected to have type …`。

### (b) `attach.prod` 桥接

`Finset.prod_attach` 本身给出
`(s.attach.prod (fun Bx => f Bx.1)) = ∏ b ∈ s, f b`；难点全在**载体依赖**：
`LE T B _` 的证据参数是 `B ∈ T`（由 `children_mem B.2` 给出），
而写成 `∏ B ∈ children T C, LE T B (…)` 时，`∏` 的绑定**不把该成员证据放进局部上下文**
（这正是 `attach` 形式的优点），于是 `(by assumption)` 拿不到 `B ∈ children T C`；
`rename_i` 也只会捕到 `DecidableEq α`。⇒ 需要先把 `prod` 换成 `attach.prod` 形式再重写，
这与 (a) 是同一处卡点。

⇒ **(a)(b) 本轮如实未落地**；**没有**用 `sorry`、半成品或改写命题来冒充。
本轮唯一可用增量是本轮**证出来的**下面这条（它是 (a) 的必要子步骤）：
「孩子 ≥2 ⇒ 父 ≥2」。 -/

/-- 孩子有 ≥ 2 个元素时，父也有（`B ⊂ C`）。 -/
theorem two_le_card_of_child {T : Finset (Finset α)} {C B : Finset α}
    (hB : B ∈ children T C) (hB2 : 2 ≤ B.card) : 2 ≤ C.card := by
  have hlt : B.card < C.card := Finset.card_lt_card (children_ssubset hB)
  omega

/-- ★★ **(a) `LE` 的归纳原理**：若
`∀ C ∈ T, 2 ≤ C.card → (∀ B ∈ children T C, 2 ≤ B.card → P B) → P C`，
则 `∀ C ∈ T, 2 ≤ C.card → P C`。

证明：对 `hook T C` 做良基归纳（`Nat.strongRecOn`，直接在 `ℕ` 上递归以避开
`InvImage`+`hook` 的 `whnf` 超时）。

⚠️ **关键点**：把归纳假设用在孩子 `B` 上时，`hook_lt_of_mem_children` 需要的是
**父的** `2 ≤ C.card`（本载体 `hD2` 直接给出），**不是**孩子的
（`B ∈ children T D` 确实**不蕴含** `2 ≤ B.card`，第六轮已给反例
`T = {∅,{0}}`）。故 `step` 里必须**接收**孩子的 `2 ≤ B.card` 作为假设。 -/
theorem LE_induction {T : Finset (Finset α)} (P : Finset α → Prop)
    (step : ∀ C, C ∈ T → 2 ≤ C.card →
      (∀ B ∈ children T C, 2 ≤ B.card → P B) → P C) :
    ∀ C, C ∈ T → 2 ≤ C.card → P C := by
  intro C hC hC2
  exact Nat.strongRecOn (hook T C)
    (motive := fun m => ∀ D : Finset α, D ∈ T → 2 ≤ D.card → hook T D = m → P D)
    (fun m ih D hD hD2 hDm =>
      step D hD hD2 fun B hB hB2 =>
        ih (hook T B) (by rw [← hDm]; exact hook_lt_of_mem_children hB hD2 hD)
          B (children_mem hB) hB2 rfl)
    C hC hC2 rfl

/-- ★★ **(b) `attach.prod` ↔ `Finset.prod` 桥接**：把 `LE_eq` 里的
`(children T C).attach.prod (fun Bx => LE T Bx.1 _)` 桥成 `Finset.prod` 形状。

⚠️ 载体依赖的处理：`LE T B _` 的证据参数类型是 `B ∈ T`，只能由 `children_mem` 从
`B ∈ children T C` 得到；而 `∏ B ∈ children T C, …` 的绑定**不把该成员证据放进局部上下文**
（这正是 `attach` 形式的优点）。⇒ 用
`if h : B ∈ children T C then LE T B (children_mem h) else 1` 把证据**内部化**，
再 `dite_eq_left` 消去；最后 `Finset.prod_attach` 把 `attach.prod` 化成 `∏`。 -/
theorem attach_prod_LE (T : Finset (Finset α)) (C : Finset α) :
    (children T C).attach.prod (fun Bx : { B // B ∈ children T C } =>
        LE T Bx.1 (children_mem Bx.2))
      = ∏ B ∈ children T C,
          (if h : B ∈ children T C then LE T B (children_mem h) else 1) := by
  classical
  rw [show (children T C).attach.prod (fun Bx : { B // B ∈ children T C } =>
        LE T Bx.1 (children_mem Bx.2))
      = (children T C).attach.prod (fun Bx : { B // B ∈ children T C } =>
        (if h : Bx.1 ∈ children T C then LE T Bx.1 (children_mem h) else 1)) from
    Finset.prod_congr rfl fun Bx _ => by rw [dite_eq_left Bx.2]]
  rw [Finset.prod_attach (children T C)
    (fun B => if h : B ∈ children T C then LE T B (children_mem h) else 1)]

/-! ### §9.2 ★D `hgood` 在一般 `T` 上**是假命题**（先证伪，故不再追求）

第七轮先按要求考察 `hgood : ∀ C ∈ T, 2 ≤ C.card → ∀ B ∈ children T C, 2 ≤ B.card`。
**它在一般 `T` 上不成立**：取 `T = {∅, {0}, {0,1}}`、`C = {0,1}`（`card = 2`），
则 `children T C = {{0}}`（`∅` 不是极大的：`∅ ⊊ {0} ⊊ {0,1}`），而 `|{0}| = 1 < 2`。

⇒ **绕开 `hgood` 的正确做法**（本轮已落地）：归纳原理的 `step` **直接接收**孩子的
`2 ≤ B.card` 作为假设，而递归调用所需的 `hook_lt_of_mem_children` 用的是
**父的** `2 ≤ C.card`（由载体给出）。见 `LE_induction`。 -/

/-- ★D 反例族：`T = {∅, {0}, {0,1}}`。 -/
def Thgood : Finset (Finset (Fin 2)) := {∅, {0}, {0,1}}

/-- ★D：`hgood` 不成立 —— `{0}` 是 `{0,1}` 的孩子，但 `|{0}| = 1 < 2`。 -/
example : ¬ (∀ C ∈ Thgood, 2 ≤ C.card → ∀ B ∈ children Thgood C, 2 ≤ B.card) := by
  intro h
  have hcard : 2 ≤ ({0, 1} : Finset (Fin 2)).card := by decide
  have hmem : ({0} : Finset (Fin 2)) ∈ children Thgood {0, 1} := by
    rw [mem_children]
    refine ⟨by decide, by decide, ?_⟩
    intro D hDT hDsub hDsub2
    fin_cases hDT <;> simp_all
  have hb : ¬ (2 ≤ ({0} : Finset (Fin 2)).card) := by decide
  exact hb (h {0, 1} (by decide) hcard {0} hmem)

/-! ## §10 ★★★ 闭形式（hook-length 公式本体）：`LE · ∏s = N!`

**这是 (i) 的收口**：树偏序的线性扩展数经验公式

```text
LE T C hC  ·  ∏_{D ∈ internalBelow T C} hook T D   =   (hook T C)!
```

即 `#LinExt = N! / ∏_v s_v`（`N = 内部结点数 = hook T C`）。

**证明**（`LE_induction` ＋ §5 ＋ §6，需 `LaminarFamily T`，因为 §5 的分母递推需要它）：

1. `LE_eq` ＋ **`attach_prod_LE`**(b) 展开 `LE T C`；
2. **`prod_hook_eq_hook_mul_prod_children`**(§5) 展开分母的 `∏s`；
3. `Finset.prod_mul_distrib` ＋ `prod_congr` ＋ `dite_eq_left` 把
   `∏_B [F B · ∏_{D⊆B} s_D]` 与归纳假设对齐 ⇒ `∏_B (hook T B)!`
   （孩子 `2 ≤ B.card` **不**成立时，两边都为 `1` —— 用
   `LE_eq_one_of_card_le_one` ＋ `hook_eq_zero_of_card_le_one` ＋
   `internalBelow_eq_empty_of_card_le_one` 处理）；
4. **`hook_eq_one_add_sum_children`**(§3) ⇒ `∑_B hook T B = hook T C - 1`；
5. **`Nat.multinomial_spec`**(§6) ⇒ `mult · ∏_B (hook T B)! = (hook T C - 1)!`；
6. `(hook T C - 1)! · hook T C = (hook T C)!`（`Nat.factorial_succ`）收口。

⚠️ 第 3 步是本轮唯一的新技术点：**孩子可以 <2 元素**（§9.1 的反例），
故不能直接把 `ih` 套上去，必须分情形；小孩子的两边都是 `1`，故公式仍然成立。 -/

/-- 若 `C.card ≤ 1`，则 `C` 之下没有内部结点（`internalBelow T C = ∅`）。 -/
theorem internalBelow_eq_empty_of_card_le_one {T : Finset (Finset α)} {C : Finset α}
    (h : C.card ≤ 1) : internalBelow T C = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨D, hD⟩
  obtain ⟨-, hD2, hDsub⟩ := mem_internalBelow.mp hD
  have := Finset.card_le_card hDsub
  omega

/-- ★★★ **hook-length 公式（闭形式）**：

```text
LE T C hC  ·  ∏_{D ∈ internalBelow T C} hook T D  =  (hook T C)!
```

等价地 `#LinExt = N! / ∏_v s_v`（`N = hook T C` 为内部结点数）。
需 `LaminarFamily T`（§5 的分母递推所需）。 -/
theorem LE_mul_prod_hook_eq_factorial {T : Finset (Finset α)} (hl : LaminarFamily T) :
    ∀ C, C ∈ T → 2 ≤ C.card →
      ∀ hC : C ∈ T, LE T C hC * ∏ D ∈ internalBelow T C, hook T D
        = (hook T C).factorial := by
  refine LE_induction (fun C => ∀ hC : C ∈ T,
    LE T C hC * ∏ D ∈ internalBelow T C, hook T D = (hook T C).factorial) ?_
  intro C hC h2 ih hCc
  have hpos : 0 < hook T C := hook_pos hCc h2
  have hsum : ∑ B ∈ children T C, hook T B = hook T C - 1 := by
    have h1 := hook_eq_one_add_sum_children hl hCc h2
    omega
  have hms : Nat.multinomial (children T C) (fun B => hook T B)
      * ∏ B ∈ children T C, (hook T B).factorial = (hook T C - 1).factorial := by
    rw [mul_comm, Nat.multinomial_spec, hsum]
  have hpair : (∏ B ∈ children T C,
        (if h : B ∈ children T C then LE T B (children_mem h) else 1))
      * (∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D)
      = ∏ B ∈ children T C, (hook T B).factorial := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun B hB => ?_
    rw [dite_eq_left hB]
    by_cases hB2 : 2 ≤ B.card
    · exact ih B hB hB2 (children_mem hB)
    · rw [LE_eq_one_of_card_le_one (children_mem hB) (by omega),
        hook_eq_zero_of_card_le_one (T := T) (by omega),
        internalBelow_eq_empty_of_card_le_one (T := T) (by omega)]
      simp
  calc LE T C hCc * ∏ D ∈ internalBelow T C, hook T D
      = Nat.multinomial (children T C) (fun B => hook T B)
        * (∏ B ∈ children T C,
            (if h : B ∈ children T C then LE T B (children_mem h) else 1))
        * (hook T C * ∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D) := by
        rw [LE_eq T C hCc h2, attach_prod_LE, prod_hook_eq_hook_mul_prod_children hl hCc h2]
    _ = Nat.multinomial (children T C) (fun B => hook T B) * (hook T C)
        * ((∏ B ∈ children T C,
              (if h : B ∈ children T C then LE T B (children_mem h) else 1))
           * (∏ B ∈ children T C, ∏ D ∈ internalBelow T B, hook T D)) := by ring
    _ = Nat.multinomial (children T C) (fun B => hook T B) * (hook T C)
        * (∏ B ∈ children T C, (hook T B).factorial) := by rw [hpair]
    _ = (hook T C).factorial := by
        have hfac : (hook T C).factorial = hook T C * (hook T C - 1).factorial := by
          conv_lhs => rw [show hook T C = (hook T C - 1) + 1 by omega]
          rw [Nat.factorial_succ]
          congr 1
          omega
        rw [show Nat.multinomial (children T C) (fun B => hook T B) * (hook T C)
              * (∏ B ∈ children T C, (hook T B).factorial)
            = (Nat.multinomial (children T C) (fun B => hook T B)
              * ∏ B ∈ children T C, (hook T B).factorial) * (hook T C) by ring,
          hms, mul_comm, ← hfac]

/-! ### §10.1 ★B capstone：`LE` 与既有**纤维数**对上

`RankedGeneTree.lean` 已证：caterpillar 的纤维 = `1`（`rankedFiberCount_012_3`）、
balanced 的纤维 = `2`（`rankedFiberCount_01_23`）。由 §10 的闭形式可**反解** `LE`：

* `Tcat`：`∏s = 6`、`N = hook = 3` ⇒ `LE · 6 = 3! = 6` ⇒ **`LE = 1`** ✓
* `Tbal`：`∏s = 3`、`N = 3` ⇒ `LE · 3 = 6` ⇒ **`LE = 2`** ✓

**两个数恰好等于既有纤维数** —— 说明 §8 用「多项式系数递推」定义的 `LE`
与 `rankedFiberCount` 在具体拓扑上**对得上**（(ii) 的显式双射仍未做）。 -/

open Phylo in
/-- ★B：`Tcat` 是镶嵌族（`{0,1} ⊂ {0,1,2} ⊂ univ` 为链）。 -/
theorem laminarFamily_Tcat : LaminarFamily Tcat := by
  intro A hA B hB
  fin_cases hA <;> fin_cases hB <;> decide

open Phylo in
/-- ★B：`Tbal` 是镶嵌族（`{0,1} ⟂ {2,3}`，且都 `⊆ univ`）。 -/
theorem laminarFamily_Tbal : LaminarFamily Tbal := by
  intro A hA B hB
  fin_cases hA <;> fin_cases hB <;> decide

/-- ★B capstone（caterpillar）：`LE · 6 = 3! = 6`。 -/
example : LE Tcat Finset.univ (by decide) * 6 = 6 := by
  have h := LE_mul_prod_hook_eq_factorial (T := Tcat) (C := Finset.univ)
    laminarFamily_Tcat (by decide) (by decide) (by decide)
  rw [show (∏ D ∈ internalBelow Tcat Finset.univ, hook Tcat D) = 6 from by decide,
      show hook Tcat Finset.univ = 3 from by decide,
      show Nat.factorial 3 = 6 from by decide] at h
  exact h

/-- ★B capstone（balanced）：`LE · 3 = 3! = 6`。 -/
example : LE Tbal Finset.univ (by decide) * 3 = 6 := by
  have h := LE_mul_prod_hook_eq_factorial (T := Tbal) (C := Finset.univ)
    laminarFamily_Tbal (by decide) (by decide) (by decide)
  rw [show (∏ D ∈ internalBelow Tbal Finset.univ, hook Tbal D) = 3 from by decide,
      show hook Tbal Finset.univ = 3 from by decide,
      show Nat.factorial 3 = 6 from by decide] at h
  exact h

/-- ★B capstone：caterpillar 的 `LE` **反解为 `1`**，与 `rankedFiberCount_012_3` 的纤维 `1` 一致。 -/
example : LE Tcat Finset.univ (by decide) = 1 := by
  have h : LE Tcat Finset.univ (by decide) * 6 = 1 * 6 := by
    have h' := LE_mul_prod_hook_eq_factorial (T := Tcat) (C := Finset.univ)
      laminarFamily_Tcat (by decide) (by decide) (by decide)
    rw [show (∏ D ∈ internalBelow Tcat Finset.univ, hook Tcat D) = 6 from by decide,
        show hook Tcat Finset.univ = 3 from by decide,
        show Nat.factorial 3 = 6 from by decide] at h'
    simpa using h'
  exact Nat.mul_right_cancel (by norm_num : 0 < 6) h

/-- ★B capstone：balanced 的 `LE` **反解为 `2`**，与 `rankedFiberCount_01_23` 的纤维 `2` 一致。 -/
example : LE Tbal Finset.univ (by decide) = 2 := by
  have h : LE Tbal Finset.univ (by decide) * 3 = 2 * 3 := by
    have h' := LE_mul_prod_hook_eq_factorial (T := Tbal) (C := Finset.univ)
      laminarFamily_Tbal (by decide) (by decide) (by decide)
    rw [show (∏ D ∈ internalBelow Tbal Finset.univ, hook Tbal D) = 3 from by decide,
        show hook Tbal Finset.univ = 3 from by decide,
        show Nat.factorial 3 = 6 from by decide] at h'
    simpa using h'
  exact Nat.mul_right_cancel (by norm_num : 0 < 3) h


/-! ## §12 ★★★ W23 任务 B-1（MSC 主线入口）：`rankedFiberCount_gap` 的**路障定位**

★ **本轮的诊断更正**（W23 派单把 B-1 记作「缺 hook-length 层」—— **那层已在库 ✓**）：
* **hook-length 公式本体已证** ✓：§10 `LE_mul_prod_hook_eq_factorial`
  （`LE T C · ∏_{D ∈ internalBelow T C} hook T D = (hook T C)!`）；
* **`T = cladesOf n f` 的镶嵌性已证** ✓：`laminarFamily_cladesOf`（`RankedGeneTree.lean:271`）
  ⇒ 上式的 `LaminarFamily` 假设**已兑现** ✓；
* ⇒ **真正剩下的只有两件**（都是**组合实体**，不是器材）：
  **(O1)** 双射「纤维 = `LE`」：
  ```text
  ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
    = LE (cladesOf n f) Finset.univ hU
  ```
  （「`cladesOf` 的 clade 包含偏序的**线性扩展** ⟺ 合并史的 **ranking**」）；
  **(O2)** 钩长计数 `hook (cladesOf n f) C = C.card − 1`（`2 ≤ C.card`）——
  即「二叉树的子树内部结点数 = 叶数 − 1」在 `cladesOf` 上的兑现。
  ⇒ 有了 (O1)(O2)，`LE_mul_prod_hook_eq_factorial` 在 `C = univ`（`hook = n−1`、
  分母 = `∏(C.card−1)`）就直接给出 `rankedFiberCount_gap` 的右端 ✓。

★ **W25 泳道 C 更新（2026-10-19）**：**(O2) 已证成** —— `hook_cladesOf_eq_card_sub_one`（本文件 §13）；
故本节的归约已成**单向**：`rankedFiberCount_gap` 只等价于 **(O1)** 这一件组合实体，
拼装好的版本是 `rankedFiberCount_gap_of_LE`（§13 末尾）。

★ **本节只交付 (O1) 的**陈述前提**：`univ ∈ cladesOf n f`（不证它就无法陈述 (O1)）✓。 -/

open Phylo.Stat.RankedGeneTree in
/-- ★★ **`univ` 是合并史的 clade**（`(O1)` 陈述的必要前提）：`IsMergeHistory n f` 的第二个合取项
正是「`chainMap n f (n−1)` 常值」⇒ 该层的唯一块是全体 ⇒ `univ ∈ cladesOf n f` ✓。 -/
theorem univ_mem_cladesOf {n : ℕ} (hn : 1 ≤ n) {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) : (Finset.univ : Finset (Fin n)) ∈ cladesOf n f := by
  have hlt : n - 1 < n := by omega
  have hconst : ∀ w w' : Fin n, chainMap n f (n - 1) w = chainMap n f (n - 1) w' := hf.2
  refine Finset.mem_biUnion.mpr ⟨n - 1, Finset.mem_range.mpr hlt, ?_⟩
  refine Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact hconst z ⟨0, hn⟩


open Phylo.Stat.RankedGeneTree

/-- ★★★★ **(O1) ＋ (O2) ⇒ `rankedFiberCount_gap`（`n ≥ 2` 的归约定理，W23）** ✓

把缺口化为**两件组合实体**（此前只是 docstring 里的说法，现在是定理）：

* **(O1)** 双射「纤维 = 线性扩展数」：
  `((mergeHistories n).filter (cladesOf · = cladesOf f)).card = LE (cladesOf n f) univ`；
* **(O2)** 钩长计数：`hook (cladesOf n f) C = C.card − 1`（`2 ≤ C.card`）。

**拼装**（全部步骤已证，无隐藏件）：
`LE_mul_prod_hook_eq_factorial`（§10，`C := univ`，`internalBelow T univ = {D ∈ T : 2 ≤ |D|}`）
⇒ `LE · ∏(C.card−1) = (hook univ)!`；(O2) 在 `C = univ` 给出 `hook univ = n − 1`
⇒ `LE · ∏(C.card−1) = (n−1)!` ⇒ 右除即闭形式（分母正，`Nat.mul_div_right`）。

⚠️ **诚实边界**：本定理**不证** (O1)/(O2)，只证「它们足够」；且只覆盖 `2 ≤ n`
（`n ≤ 1` 是退化情形：`cladesOf` 只有单点簇 ⇒ 分母为 `1`、纤维为单点，纯计算可核，
本轮未形式化，见 `rankedFiberCount_gap` 的 docstring）。 -/
theorem rankedFiberCount_gap_of_LE_and_hook {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ (f : Fin (n - 1) → Fin n × Fin n) (hf : IsMergeHistory n f),
        ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
            = LE (cladesOf n f) Finset.univ (univ_mem_cladesOf (by omega) hf)
          ∧ (∀ C ∈ cladesOf n f, 2 ≤ C.card → hook (cladesOf n f) C = C.card - 1)) :
    ∀ (f : Fin (n - 1) → Fin n × Fin n), IsMergeHistory n f →
      ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
        = (n - 1).factorial
          / ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), (C.card - 1) := by
  intro f hf
  have hn1 : 1 ≤ n := by omega
  have hU : (Finset.univ : Finset (Fin n)) ∈ cladesOf n f := univ_mem_cladesOf hn1 hf
  obtain ⟨hLE, hhook⟩ := h f hf
  have hcard : 2 ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  -- 分母集合：`internalBelow T univ` 就是「`2 ≤ |C|` 的 clade」
  have hset : internalBelow (cladesOf n f) Finset.univ
      = (cladesOf n f).filter (fun C => 2 ≤ C.card) := by
    ext D
    simp only [internalBelow, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Finset.subset_univ D⟩
  -- 钩长公式（`C = univ`）
  have hform := LE_mul_prod_hook_eq_factorial (T := cladesOf n f)
    (laminarFamily_cladesOf f) Finset.univ hU hcard hU
  rw [hset] at hform
  have hden : ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), hook (cladesOf n f) C
      = ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), (C.card - 1) := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    exact hhook C (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hC).2
  rw [hden] at hform
  have htop : hook (cladesOf n f) Finset.univ = n - 1 := by
    rw [hhook Finset.univ hU hcard, Finset.card_univ, Fintype.card_fin]
  rw [htop] at hform
  -- 收尾：`LE · P = (n−1)!` ⇒ `LE = (n−1)! / P`
  have hpos : 0 < ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), (C.card - 1) := by
    refine Finset.prod_pos ?_
    intro C hC
    have h2 := (Finset.mem_filter.mp hC).2
    omega
  rw [hLE]
  refine Nat.mul_right_cancel hpos ?_
  rw [Nat.div_mul_cancel ⟨LE (cladesOf n f) Finset.univ hU, by rw [mul_comm]; exact hform.symm⟩]
  exact hform


/-! ## §13 ★★★ W25 泳道 C：(O2) `hook (cladesOf n f) C = C.card - 1`

`cladesOf n f` 是「逐层加粗的划分链」的全部块：第 `L` 层的块 = `chainMap n f L` 的**纤维**
（`blocksOf`）。`IsMergeHistory` 保证每步是**真合并**：两块非空、不交、代表元不动。

**组合事实**：`C` 是这条链上的一个块 ⟹ `C` 之下的非单点块数 `= |C| - 1`。
理由：`C` 内部从 `|C|` 个单点出发、经 `|C| - 1` 次真合并到达 `C`；每次真合并
把「当前块数」减 `1` 且恰添 `1` 个新块，故出现过的块共 `2|C| - 1` 个，
其中单点 `|C|` 个 ⇒ 非单点 `|C| - 1` 个。

本节把这条归纳形式化，交付 **(O2)**：`hook_cladesOf_eq_card_sub_one`。 -/

/-- `r` 的**纤维**（值 `v` 的原像）＝ 一个划分块；与 `blocksOf` 的定义式一致。 -/
def fiberOf {n : ℕ} (r : Fin n → Fin n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => r z = v)

theorem mem_fiberOf {n : ℕ} {r : Fin n → Fin n} {v z : Fin n} :
    z ∈ fiberOf r v ↔ r z = v := by
  simp [fiberOf]

/-- 同一值上的纤维一致（等价关系）。 -/
theorem fiberOf_congr {n : ℕ} {r : Fin n → Fin n} {z z' : Fin n} (h : r z = r z') :
    fiberOf r (r z) = fiberOf r (r z') := by
  ext a
  rw [mem_fiberOf, mem_fiberOf, h]

theorem self_mem_fiberOf {n : ℕ} {r : Fin n → Fin n} (z : Fin n) :
    z ∈ fiberOf r (r z) := by
  rw [mem_fiberOf]

/-- `blocksOf` 的每个块都是某个元素的纤维。 -/
theorem exists_fiberOf_of_mem_blocksOf {n : ℕ} {r : Fin n → Fin n} {D : Finset (Fin n)}
    (h : D ∈ blocksOf n r) : ∃ z, D = fiberOf r (r z) := by
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
  exact ⟨w, hw.symm⟩

/-- 每个元素的纤维都是一个块。 -/
theorem fiberOf_mem_blocksOf {n : ℕ} (r : Fin n → Fin n) (z : Fin n) :
    fiberOf r (r z) ∈ blocksOf n r :=
  Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩

/-- 非空纤维都是块。 -/
theorem fiberOf_mem_blocksOf_of_nonempty {n : ℕ} {r : Fin n → Fin n} {v : Fin n}
    (h : (fiberOf r v).Nonempty) : fiberOf r v ∈ blocksOf n r := by
  obtain ⟨z, hz⟩ := h
  have hzv : r z = v := mem_fiberOf.mp hz
  rw [← hzv]
  exact fiberOf_mem_blocksOf r z

/-- `blocksOf` 的块非空。 -/
theorem nonempty_of_mem_blocksOf {n : ℕ} {r : Fin n → Fin n} {D : Finset (Fin n)}
    (h : D ∈ blocksOf n r) : D.Nonempty := by
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
  exact ⟨w, hw ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl⟩⟩

/-- 块由其**任意**元素确定。 -/
theorem eq_fiberOf_of_mem_blocksOf {n : ℕ} {r : Fin n → Fin n} {D : Finset (Fin n)}
    (hD : D ∈ blocksOf n r) {z : Fin n} (hz : z ∈ D) : D = fiberOf r (r z) := by
  obtain ⟨w, hw⟩ := exists_fiberOf_of_mem_blocksOf hD
  rw [hw] at hz ⊢
  exact (fiberOf_congr (mem_fiberOf.mp hz)).symm

/-- **纤维在 `stepMap` 下的变换**：只有 `x` 的纤维变成 `x`、`y` 两块之并，
`y` 的纤维变空，其余纤维不变。 -/
theorem fiberOf_stepMap {n : ℕ} (r : Fin n → Fin n) (x y v : Fin n) :
    fiberOf (stepMap r x y) v
      = if v = x then fiberOf r x ∪ fiberOf r y else if v = y then ∅ else fiberOf r v := by
  by_cases hvx : v = x
  · subst hvx
    ext z
    rw [ite_eq_left rfl, Finset.mem_union, mem_fiberOf, mem_fiberOf, mem_fiberOf]
    constructor
    · intro hz
      rw [stepMap] at hz
      by_cases hzy : r z = y
      · rw [ite_eq_left hzy] at hz
        exact Or.inr hzy
      · rw [ite_eq_right hzy] at hz
        exact Or.inl hz
    · rintro (h | h)
      · rw [stepMap]
        by_cases hzy : r z = y
        · rw [ite_eq_left hzy]
        · rw [ite_eq_right hzy]; exact h
      · rw [stepMap, ite_eq_left h]
  · rw [ite_eq_right hvx]
    by_cases hvy : v = y
    · rw [hvy]
      rw [ite_eq_left rfl, Finset.eq_empty_iff_forall_notMem]
      intro z
      rw [mem_fiberOf, stepMap]
      by_cases hzy : r z = y
      · rw [ite_eq_left hzy]
        exact fun h => hvx (hvy.trans h.symm)
      · rw [ite_eq_right hzy]
        exact hzy
    · rw [ite_eq_right hvy]
      ext z
      rw [mem_fiberOf, mem_fiberOf, stepMap]
      by_cases hzy : r z = y
      · rw [ite_eq_left hzy]
        exact ⟨fun h => absurd h.symm hvx, fun h => absurd (h.symm.trans hzy) hvy⟩
      · rw [ite_eq_right hzy]

/-- `stepMap` 之后的块只可能是原来的块，或多出来的 `A ∪ B`。 -/
theorem blocksOf_stepMap_subset {n : ℕ} (r : Fin n → Fin n) (x y : Fin n) :
    blocksOf n (stepMap r x y) ⊆ blocksOf n r ∪ {fiberOf r x ∪ fiberOf r y} := by
  intro D hD
  obtain ⟨w, hw⟩ := exists_fiberOf_of_mem_blocksOf hD
  rw [hw]
  have hsw : stepMap r x y w = if r w = y then x else r w := by rw [stepMap]
  by_cases hwy : r w = y
  · rw [hsw, ite_eq_left hwy, fiberOf_stepMap, ite_eq_left rfl]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  · rw [hsw, ite_eq_right hwy]
    by_cases hwx : r w = x
    · rw [hwx, fiberOf_stepMap, ite_eq_left rfl]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    · rw [fiberOf_stepMap, ite_eq_right hwx, ite_eq_right hwy]
      exact Finset.mem_union.mpr (Or.inl (fiberOf_mem_blocksOf r w))

/-- 前 `L+1` 层（第 `0` 到第 `L` 层）全部块之并。 -/
def upto {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) (L : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (L + 1)).biUnion (fun j => blocksOf n (chainMap n f j))

theorem upto_succ {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) (L : ℕ) :
    upto f (L + 1) = upto f L ∪ blocksOf n (chainMap n f (L + 1)) := by
  simp only [upto, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

theorem mem_upto {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {L : ℕ} {D : Finset (Fin n)} :
    D ∈ upto f L ↔ ∃ j ≤ L, D ∈ blocksOf n (chainMap n f j) := by
  simp only [upto, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩

theorem mem_upto_of_le {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {L j : ℕ} {D : Finset (Fin n)}
    (hj : j ≤ L) (h : D ∈ blocksOf n (chainMap n f j)) : D ∈ upto f L :=
  mem_upto.mpr ⟨j, hj, h⟩

theorem mem_cladesOf {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {D : Finset (Fin n)} :
    D ∈ cladesOf n f ↔ ∃ j < n, D ∈ blocksOf n (chainMap n f j) := by
  simp only [cladesOf, Finset.mem_biUnion, Finset.mem_range]

theorem upto_subset_cladesOf {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) {L : ℕ} (hL : L < n) :
    upto f L ⊆ cladesOf n f := by
  intro D hD
  obtain ⟨j, hj, hjD⟩ := mem_upto.mp hD
  exact mem_cladesOf.mpr ⟨j, by omega, hjD⟩

/-- 同一元素在较粗层的块包含其在较细层者。 -/
theorem fiberOf_chainMap_mono {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) {L₁ L₂ : ℕ}
    (hle : L₁ ≤ L₂) (z : Fin n) :
    fiberOf (chainMap n f L₁) (chainMap n f L₁ z)
      ⊆ fiberOf (chainMap n f L₂) (chainMap n f L₂ z) :=
  block_subset_of_le f hle z

/-- **一步真合并后，第 `L+1` 层的块 = 第 `L` 层的块 ＋ 一个新块 `A ∪ B`**。 -/
theorem upto_succ_union {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {L : ℕ} (hL : L < n - 1)
    {x y : Fin n} (hxy : f ⟨L, hL⟩ = (x, y))
    (hx : chainMap n f L x = x) :
    upto f (L + 1) = upto f L ∪ {fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y} := by
  rw [upto_succ]
  have hc : chainMap n f (L + 1) = stepMap (chainMap n f L) x y := by
    rw [chainMap_succ, dite_eq_left hL, hxy]
  rw [hc]
  refine Finset.Subset.antisymm ?_ ?_
  · intro D hD
    rcases Finset.mem_union.mp hD with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · rcases Finset.mem_union.mp (blocksOf_stepMap_subset (chainMap n f L) x y h) with h' | h'
      · exact Finset.mem_union.mpr (Or.inl (mem_upto_of_le (le_refl L) h'))
      · exact Finset.mem_union.mpr (Or.inr h')
  · intro D hD
    rcases Finset.mem_union.mp hD with h | h
    · exact Finset.mem_union.mpr (Or.inl h)
    · rw [Finset.mem_singleton.mp h]
      have hnon : (fiberOf (stepMap (chainMap n f L) x y) x).Nonempty := by
        refine ⟨x, mem_fiberOf.mpr ?_⟩
        rw [stepMap]
        by_cases hc : chainMap n f L x = y
        · rw [ite_eq_left hc]
        · rw [ite_eq_right hc]; exact hx
      have hfib : fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
          = fiberOf (stepMap (chainMap n f L) x y) x := by
        rw [fiberOf_stepMap, ite_eq_left rfl]
      rw [hfib]
      exact Finset.mem_union.mpr (Or.inr (fiberOf_mem_blocksOf_of_nonempty hnon))

/-- `(L+1)` 层的新块 `A ∪ B` 不属于更低层（`A, B` 非空不交）。 -/
theorem not_mem_upto_union {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {L : ℕ} {x y : Fin n}
    (hx : chainMap n f L x = x) (hy : chainMap n f L y = y) (hxy : x ≠ y) :
    fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y ∉ upto f L := by
  intro hmem
  obtain ⟨j, hj, hjD⟩ := mem_upto.mp hmem
  obtain ⟨z, hz⟩ := nonempty_of_mem_blocksOf hjD
  have hDj : fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
      = fiberOf (chainMap n f j) (chainMap n f j z) := eq_fiberOf_of_mem_blocksOf hjD hz
  have hsub : fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
      ⊆ fiberOf (chainMap n f L) (chainMap n f L z) := by
    rw [hDj]
    exact fiberOf_chainMap_mono f hj z
  rcases Finset.mem_union.mp hz with hzA | hzB
  · have hAeq : fiberOf (chainMap n f L) (chainMap n f L z)
        = fiberOf (chainMap n f L) x := by
      have h1 : chainMap n f L z = chainMap n f L x := by
        rw [mem_fiberOf.mp hzA]
        exact hx.symm
      rw [fiberOf_congr h1, hx]
    have hBA : fiberOf (chainMap n f L) y ⊆ fiberOf (chainMap n f L) x := by
      intro w hw
      have h1 := hsub (Finset.mem_union.mpr (Or.inr hw))
      rwa [hAeq] at h1
    have hy' : y ∈ fiberOf (chainMap n f L) y := mem_fiberOf.mpr hy
    have h1 := hBA hy'
    rw [mem_fiberOf] at h1
    exact hxy (h1.symm.trans hy)
  · have hBeq : fiberOf (chainMap n f L) (chainMap n f L z)
        = fiberOf (chainMap n f L) y := by
      have h1 : chainMap n f L z = chainMap n f L y := by
        rw [mem_fiberOf.mp hzB]
        exact hy.symm
      rw [fiberOf_congr h1, hy]
    have hAB : fiberOf (chainMap n f L) x ⊆ fiberOf (chainMap n f L) y := by
      intro w hw
      have h1 := hsub (Finset.mem_union.mpr (Or.inl hw))
      rwa [hBeq] at h1
    have hx' : x ∈ fiberOf (chainMap n f L) x := mem_fiberOf.mpr hx
    have h1 := hAB hx'
    rw [mem_fiberOf] at h1
    exact hxy (hx.symm.trans h1)

/-- 空集没有内部结点。 -/
theorem hook_empty {α : Type*} [DecidableEq α] (T : Finset (Finset α)) :
    hook T (∅ : Finset α) = 0 := by
  rw [hook_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro D _ hcon
  obtain ⟨h2, hsub⟩ := hcon
  have h0 : D.card ≤ 0 := by
    have := Finset.card_le_card hsub
    simpa using this
  omega

/-- 并上一个**不**被 `C` 包含的块，不改变 `C` 之下的内部结点集。 -/
theorem internalBelow_union_of_not_subset {α : Type*} [DecidableEq α]
    {T : Finset (Finset α)} {C N : Finset α} (hN : ¬ N ⊆ C) :
    internalBelow (T ∪ {N}) C = internalBelow T C := by
  ext D
  simp only [internalBelow, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, h2, hsub⟩
    · exact ⟨h, h2, hsub⟩
    · exact absurd (h ▸ hsub) hN
  · rintro ⟨h, h2, hsub⟩
    exact ⟨Or.inl h, h2, hsub⟩

/-- 并上一个不被 `C` 包含的块，不改变钩长。 -/
theorem hook_union_of_not_subset {α : Type*} [DecidableEq α] {T : Finset (Finset α)}
    {A B C : Finset α} (h : ¬ A ∪ B ⊆ C) :
    hook (T ∪ {A ∪ B}) C = hook T C := by
  show (internalBelow (T ∪ {A ∪ B}) C).card = (internalBelow T C).card
  rw [internalBelow_union_of_not_subset h]

/-- **`A ∪ B` 之下的内部结点 = `{A ∪ B}` ＋ `A` 之下的 ＋ `B` 之下的**（`A, B` 拆分了 `T`）。 -/
theorem internalBelow_union_of_split {α : Type*} [DecidableEq α]
    {T : Finset (Finset α)} {A B : Finset α} (h2 : 2 ≤ (A ∪ B).card)
    (hsplit : ∀ D ∈ T, D ⊆ A ∪ B → D ⊆ A ∨ D ⊆ B) :
    internalBelow (T ∪ {A ∪ B}) (A ∪ B)
      = insert (A ∪ B) (internalBelow T A ∪ internalBelow T B) := by
  ext D
  simp only [internalBelow, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨h | h, h2D, hsub⟩
    · rcases hsplit D h hsub with hs | hs
      · exact Or.inr (Or.inl ⟨h, h2D, hs⟩)
      · exact Or.inr (Or.inr ⟨h, h2D, hs⟩)
    · exact Or.inl h
  · rintro (h | ⟨h, h2D, hs⟩ | ⟨h, h2D, hs⟩)
    · exact ⟨Or.inr h, h ▸ h2, by rw [h]⟩
    · exact ⟨Or.inl h, h2D, hs.trans Finset.subset_union_left⟩
    · exact ⟨Or.inl h, h2D, hs.trans Finset.subset_union_right⟩

/-- **(O2) 的归纳步**：把新块 `A ∪ B` 并入后，`A ∪ B` 的钩长 = `|A ∪ B| - 1`。 -/
theorem hook_step_merge {α : Type*} [DecidableEq α] {T : Finset (Finset α)} {A B : Finset α}
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : A ∩ B = ∅)
    (hsplit : ∀ D ∈ T, D ⊆ A ∪ B → D ⊆ A ∨ D ⊆ B) (hN : A ∪ B ∉ T)
    (ihA : (internalBelow T A).card = A.card - 1)
    (ihB : (internalBelow T B).card = B.card - 1) :
    (internalBelow (T ∪ {A ∪ B}) (A ∪ B)).card = (A ∪ B).card - 1 := by
  have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hAB
  have h2 : 2 ≤ (A ∪ B).card := by
    have h1 : 0 < A.card := Finset.card_pos.mpr hAne
    have h2' : 0 < B.card := Finset.card_pos.mpr hBne
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  have hfilt := internalBelow_union_of_split (T := T) (A := A) (B := B) h2 hsplit
  have hnotin : A ∪ B ∉ internalBelow T A ∪ internalBelow T B := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact hN (mem_internalBelow.mp h).1
    · exact hN (mem_internalBelow.mp h).1
  have hdisjIB : Disjoint (internalBelow T A) (internalBelow T B) := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro D hD
    rw [Finset.mem_inter] at hD
    obtain ⟨hDA, hDB⟩ := hD
    obtain ⟨-, h2A, hsubA⟩ := mem_internalBelow.mp hDA
    obtain ⟨-, -, hsubB⟩ := mem_internalBelow.mp hDB
    have hsub : D ⊆ A ∩ B := fun z hz => Finset.mem_inter.mpr ⟨hsubA hz, hsubB hz⟩
    rw [hAB] at hsub
    have h0 : D.card ≤ 0 := by
      have hle := Finset.card_le_card hsub
      simpa using hle
    omega
  rw [hfilt, Finset.card_insert_of_notMem hnotin, Finset.card_union_of_disjoint hdisjIB,
    ihA, ihB, Finset.card_union_of_disjoint hdisj]
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hAne
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hBne
  omega

/-- **主引理**：第 `L` 层任一纤维的钩长 = 基数减一。 -/
theorem hook_upto_fiberOf {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) (hf : IsMergeHistory n f)
    (L : ℕ) (v : Fin n) :
    hook (upto f L) (fiberOf (chainMap n f L) v)
      = (fiberOf (chainMap n f L) v).card - 1 := by
  induction L generalizing v with
  | zero =>
    have h0 : chainMap n f 0 = (id : Fin n → Fin n) := rfl
    have hsingV : fiberOf (chainMap n f 0) v = {v} := by
      rw [h0]
      ext z
      rw [mem_fiberOf]
      simp
    have hsingW : ∀ w : Fin n, fiberOf (chainMap n f 0) (chainMap n f 0 w) = {w} := by
      intro w
      rw [h0]
      ext z
      rw [mem_fiberOf]
      simp
    have hgoal : ({v} : Finset (Fin n)).card - 1 = 0 := by simp
    rw [hsingV, hgoal, hook_def, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro D hD hcon
    obtain ⟨h2, -⟩ := hcon
    obtain ⟨j, hj, hjD⟩ := mem_upto.mp hD
    have hj0 : j = 0 := by omega
    subst hj0
    obtain ⟨w, hw⟩ := nonempty_of_mem_blocksOf hjD
    have hDw : D = fiberOf (chainMap n f 0) (chainMap n f 0 w) :=
      eq_fiberOf_of_mem_blocksOf hjD hw
    rw [hDw, hsingW w, Finset.card_singleton] at h2
    omega
  | succ L ih =>
    by_cases hL : L < n - 1
    · set x : Fin n := (f ⟨L, hL⟩).1 with hxdef
      set y : Fin n := (f ⟨L, hL⟩).2 with hydef
      have hstep := hf.1 ⟨L, hL⟩
      have hx : chainMap n f L x = x := by rw [hxdef]; exact hstep.1
      have hy : chainMap n f L y = y := by rw [hydef]; exact hstep.2.1
      have hxy : x ≠ y := by rw [hxdef, hydef]; exact ne_of_lt hstep.2.2
      have hpair : f ⟨L, hL⟩ = (x, y) := by rw [hxdef, hydef]
      have hsucc : chainMap n f (L + 1) = stepMap (chainMap n f L) x y := by
        rw [chainMap_succ, dite_eq_left hL, hpair]
      have hU : upto f (L + 1) = upto f L ∪ ({fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y} : Finset (Finset (Fin n))) :=
        upto_succ_union (f := f) hL hpair hx
      have hAne : (fiberOf (chainMap n f L) x).Nonempty := ⟨x, mem_fiberOf.mpr hx⟩
      have hBne : (fiberOf (chainMap n f L) y).Nonempty := ⟨y, mem_fiberOf.mpr hy⟩
      have hAB : fiberOf (chainMap n f L) x ∩ fiberOf (chainMap n f L) y = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rw [Finset.mem_inter, mem_fiberOf, mem_fiberOf] at hz
        exact hxy (hz.1.symm.trans hz.2)
      have hsplit : ∀ D ∈ upto f L, D ⊆ fiberOf (chainMap n f L) x
          ∪ fiberOf (chainMap n f L) y →
          D ⊆ fiberOf (chainMap n f L) x ∨ D ⊆ fiberOf (chainMap n f L) y := by
        intro D hD hsub
        obtain ⟨j, hj, hjD⟩ := mem_upto.mp hD
        obtain ⟨z, hz⟩ := nonempty_of_mem_blocksOf hjD
        have hDj : D = fiberOf (chainMap n f j) (chainMap n f j z) :=
          eq_fiberOf_of_mem_blocksOf hjD hz
        have hzAB : z ∈ fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y := hsub hz
        have hmono : fiberOf (chainMap n f j) (chainMap n f j z)
            ⊆ fiberOf (chainMap n f L) (chainMap n f L z) := fiberOf_chainMap_mono f hj z
        rcases Finset.mem_union.mp hzAB with hzA | hzB
        · left
          rw [hDj]
          refine hmono.trans ?_
          have h1 : chainMap n f L z = chainMap n f L x := by
            rw [mem_fiberOf.mp hzA, hx]
          rw [fiberOf_congr h1, hx]
        · right
          rw [hDj]
          refine hmono.trans ?_
          have h1 : chainMap n f L z = chainMap n f L y := by
            rw [mem_fiberOf.mp hzB, hy]
          rw [fiberOf_congr h1, hy]
      have hN : fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y ∉ upto f L :=
        not_mem_upto_union hx hy hxy
      have hCv : ∀ v : Fin n, fiberOf (chainMap n f (L + 1)) v
          = if v = x then fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
            else if v = y then ∅ else fiberOf (chainMap n f L) v := by
        intro v
        rw [hsucc, fiberOf_stepMap]
      rw [hCv v]
      by_cases hvx : v = x
      · rw [ite_eq_left hvx, hU]
        exact hook_step_merge hAne hBne hAB hsplit hN (ih x) (ih y)
      · rw [ite_eq_right hvx]
        by_cases hvy : v = y
        · rw [ite_eq_left hvy, hU]
          have hnotsub : ¬ fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
              ⊆ (∅ : Finset (Fin n)) := by
            intro hsub
            obtain ⟨z, hz⟩ := hAne
            exact absurd (hsub (Finset.mem_union.mpr (Or.inl hz))) (by simp)
          rw [hook_union_of_not_subset hnotsub, hook_empty]
          simp
        · rw [ite_eq_right hvy, hU]
          have hnotsub : ¬ fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y
              ⊆ fiberOf (chainMap n f L) v := by
            intro hsub
            obtain ⟨z0, hz0⟩ := hAne
            have hz0C : z0 ∈ fiberOf (chainMap n f L) v :=
              hsub (Finset.mem_union.mpr (Or.inl hz0))
            exact hvx ((mem_fiberOf.mp hz0C).symm.trans (mem_fiberOf.mp hz0))
          rw [hook_union_of_not_subset hnotsub]
          exact ih v
    · have hsucc : chainMap n f (L + 1) = chainMap n f L := by
        rw [chainMap_succ, dite_eq_right hL]
      have hU : upto f (L + 1) = upto f L := by
        rw [upto_succ, hsucc]
        exact Finset.union_eq_left.mpr
          (Finset.subset_biUnion_of_mem (fun j => blocksOf n (chainMap n f j))
            (Finset.mem_range.mpr (by omega)))
      rw [hsucc, hU]
      exact ih v

/-- ★★★★ **(O2)**：`cladesOf n f` 的钩长 `= |C| - 1`（`2 ≤ |C|`，**无额外数学假设**）。 -/
theorem hook_cladesOf_eq_card_sub_one {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n)
    (hf : IsMergeHistory n f) :
    ∀ C ∈ cladesOf n f, 2 ≤ C.card → hook (cladesOf n f) C = C.card - 1 := by
  intro C hC h2
  obtain ⟨L, hL, hCL⟩ := mem_cladesOf.mp hC
  obtain ⟨w, hw⟩ := nonempty_of_mem_blocksOf hCL
  have hCw : C = fiberOf (chainMap n f L) (chainMap n f L w) :=
    eq_fiberOf_of_mem_blocksOf hCL hw
  have htrunc : internalBelow (cladesOf n f) C = internalBelow (upto f L) C := by
    ext D
    rw [mem_internalBelow, mem_internalBelow]
    constructor
    · rintro ⟨hD, h2D, hsub⟩
      refine ⟨?_, h2D, hsub⟩
      obtain ⟨j, hj, hjD⟩ := mem_cladesOf.mp hD
      by_cases hle : j ≤ L
      · exact mem_upto.mpr ⟨j, hle, hjD⟩
      · obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
        have hDz : D = fiberOf (chainMap n f j) (chainMap n f j z) :=
          eq_fiberOf_of_mem_blocksOf hjD hz
        have hzw : chainMap n f L z = chainMap n f L w := by
          rw [hCw] at hsub
          exact mem_fiberOf.mp (hsub hz)
        have hCz : C = fiberOf (chainMap n f L) (chainMap n f L z) := by
          rw [hCw]
          exact (fiberOf_congr hzw).symm
        have hCD : C ⊆ D := by
          rw [hCz, hDz]
          exact fiberOf_chainMap_mono f (by omega) z
        have hDC : D ⊆ C := hsub
        rw [Finset.Subset.antisymm hDC hCD]
        exact mem_upto.mpr ⟨L, le_refl L, hCL⟩
    · rintro ⟨hD, h2D, hsub⟩
      exact ⟨upto_subset_cladesOf f hL hD, h2D, hsub⟩
  rw [hCw] at htrunc ⊢
  show (internalBelow (cladesOf n f) (fiberOf (chainMap n f L) (chainMap n f L w))).card
      = (fiberOf (chainMap n f L) (chainMap n f L w)).card - 1
  rw [htrunc]
  exact hook_upto_fiberOf f hf L (chainMap n f L w)

/-- ★★★★ **缺口现在只剩 (O1)**：把已证的 **(O2)**（`hook_cladesOf_eq_card_sub_one`）代入
W23 的归约定理 `rankedFiberCount_gap_of_LE_and_hook`，`rankedFiberCount_gap` 就**仅**等价于
「纤维基数 = `LE (cladesOf n f) univ`」这一件组合实体。 -/
theorem rankedFiberCount_gap_of_LE {n : ℕ} (hn : 2 ≤ n)
    (hO1 : ∀ (f : Fin (n - 1) → Fin n × Fin n) (hf : IsMergeHistory n f),
        ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
          = LE (cladesOf n f) Finset.univ (univ_mem_cladesOf (by omega) hf)) :
    ∀ (f : Fin (n - 1) → Fin n × Fin n), IsMergeHistory n f →
      ((mergeHistories n).filter (fun g => cladesOf n g = cladesOf n f)).card
        = (n - 1).factorial
          / ∏ C ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card), (C.card - 1) :=
  rankedFiberCount_gap_of_LE_and_hook hn
    (fun f hf => ⟨hO1 f hf, hook_cladesOf_eq_card_sub_one f hf⟩)

/-! ## §14 ★★★ W25 泳道 D：`cladesOf` 的**二叉性**（(O1) 的偏序侧器材）

**(O1)**（见 §12 的定位与 §13 末尾的 `rankedFiberCount_gap_of_LE`）要证的是

```text
|{g ∈ mergeHistories n : cladesOf n g = cladesOf n f}| = LE (cladesOf n f) univ
```

即「纤维 ↔ clade 包含偏序的**线性扩展**（`LE` 数的那一族对象）」之间的**显式双射**。

本节交付这条双射的**偏序侧第一件器材**：`cladesOf n f` 的包含偏序**就是二叉树的结点偏序**。
它在 clade 集上的精确内容是

> 每个非单点 clade 在 `cladesOf n f` 中恰有 **2 个**极大真子簇（`children`）。

（对比：`LE` 的递归对任意孩子数都有定义（`Nat.multinomial`）；而 `cladesOf n f` 实际只有
两个孩子 —— 这正是「合并史每步恰把**两块**并成一块」。）

证明（对层数 `L` 强归纳，用 §13 的 `fiberOf_stepMap` ＋ `chainMap_mono`）：
第 `L'+1` 层的非单点纤维要么是**上一步刚合并出的新块** `A ∪ B`，要么是第 `L'` 层原封不动
的纤维。前者：孩子恰是 `A`、`B` —— 更细层（`j ≤ L'`）的块落在 `A` 或 `B` 内，
更粗层（`j > L'`）的块若含于 `A ∪ B` 则只能整体等于它。后者：用归纳假设。

⚠️ **这仍是器材，不是 (O1) 本体**：双射本身见 §14.1 的诚实边界。 -/

/-- 第 `L` 层任一**非单点**纤维在 `cladesOf n f` 里恰有 `2` 个孩子。 -/
theorem children_fiberOf_chainMap_card_two {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) :
    ∀ L < n, ∀ v : Fin n, 2 ≤ (fiberOf (chainMap n f L) v).card →
      (children (cladesOf n f) (fiberOf (chainMap n f L) v)).card = 2 := by
  intro L
  refine Nat.strongRecOn L (motive := fun k => k < n → ∀ v : Fin n,
    2 ≤ (fiberOf (chainMap n f k) v).card →
      (children (cladesOf n f) (fiberOf (chainMap n f k) v)).card = 2) ?_
  intro L ih hLn v hv
  rcases L with _ | L'
  · have h0 : chainMap n f 0 = (id : Fin n → Fin n) := rfl
    have hsing : fiberOf (chainMap n f 0) v = {v} := by
      rw [h0]
      ext z
      rw [mem_fiberOf]
      simp
    rw [hsing, Finset.card_singleton] at hv
    omega
  · have hL'n : L' < n := by omega
    have hL' : L' < n - 1 := by omega
    set x : Fin n := (f ⟨L', hL'⟩).1 with hxdef
    set y : Fin n := (f ⟨L', hL'⟩).2 with hydef
    have hpair : f ⟨L', hL'⟩ = (x, y) := by rw [hxdef, hydef]
    have hstep := hf.1 ⟨L', hL'⟩
    have hx : chainMap n f L' x = x := by rw [hxdef]; exact hstep.1
    have hy : chainMap n f L' y = y := by rw [hydef]; exact hstep.2.1
    have hxy : x ≠ y := by rw [hxdef, hydef]; exact ne_of_lt hstep.2.2
    have hsucc : chainMap n f (L' + 1) = stepMap (chainMap n f L') x y := by
      rw [chainMap_succ, dite_eq_left hL', hpair]
    have hCv : ∀ w : Fin n, fiberOf (chainMap n f (L' + 1)) w
        = if w = x then fiberOf (chainMap n f L') x ∪ fiberOf (chainMap n f L') y
          else if w = y then ∅ else fiberOf (chainMap n f L') w := by
      intro w
      rw [hsucc, fiberOf_stepMap]
    rw [hCv v] at hv ⊢
    by_cases hvx : v = x
    · rw [ite_eq_left hvx] at hv ⊢
      set A : Finset (Fin n) := fiberOf (chainMap n f L') x with hA
      set B : Finset (Fin n) := fiberOf (chainMap n f L') y with hB
      have hCx : fiberOf (chainMap n f (L' + 1)) x = A ∪ B := by
        rw [hCv x, ite_eq_left rfl]
      have hAT : A ∈ cladesOf n f := by
        rw [hA]
        exact mem_cladesOf.mpr ⟨L', hL'n, hx ▸ fiberOf_mem_blocksOf (chainMap n f L') x⟩
      have hBT : B ∈ cladesOf n f := by
        rw [hB]
        exact mem_cladesOf.mpr ⟨L', hL'n, hy ▸ fiberOf_mem_blocksOf (chainMap n f L') y⟩
      have hxInA : x ∈ A := by rw [hA]; exact mem_fiberOf.mpr hx
      have hyInB : y ∈ B := by rw [hB]; exact mem_fiberOf.mpr hy
      have hAneB : A ≠ B := by
        intro heq
        have h1 : x ∈ B := heq ▸ hxInA
        rw [hB, mem_fiberOf] at h1
        exact hxy (hx.symm.trans h1)
      have hyNotA : y ∉ A := by
        intro h
        rw [hA, mem_fiberOf] at h
        exact hxy (h.symm.trans hy)
      have hxNotB : x ∉ B := by
        intro h
        rw [hB, mem_fiberOf] at h
        exact hxy (hx.symm.trans h)
      have hAproper : A ⊂ A ∪ B := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
        intro heq
        have h1 : y ∈ A ∪ B := Finset.mem_union_right A hyInB
        rw [← heq] at h1
        exact hyNotA h1
      have hBproper : B ⊂ A ∪ B := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
        intro heq
        have h1 : x ∈ A ∪ B := Finset.mem_union_left B hxInA
        rw [← heq] at h1
        exact hxNotB h1
      have hclassify : ∀ D ∈ cladesOf n f, D ⊆ A ∪ B → D ⊆ A ∨ D ⊆ B ∨ D = A ∪ B := by
        intro D hDT hDsub
        obtain ⟨j, hj, hDj⟩ := mem_cladesOf.mp hDT
        obtain ⟨a0, ha0⟩ := nonempty_of_mem_blocksOf hDj
        have hDeq : D = fiberOf (chainMap n f j) (chainMap n f j a0) :=
          eq_fiberOf_of_mem_blocksOf hDj ha0
        have ha0C : a0 ∈ A ∪ B := hDsub ha0
        by_cases hle : j ≤ L'
        · have hmono : D ⊆ fiberOf (chainMap n f L') (chainMap n f L' a0) := by
            rw [hDeq]
            exact fiberOf_chainMap_mono f hle a0
          rcases Finset.mem_union.mp ha0C with h | h
          · left
            have hxa : chainMap n f L' a0 = x := mem_fiberOf.mp (hA ▸ h)
            have hfe : fiberOf (chainMap n f L') (chainMap n f L' a0) = A := by
              rw [hxa, ← hA]
            rwa [hfe] at hmono
          · right; left
            have hya : chainMap n f L' a0 = y := mem_fiberOf.mp (hB ▸ h)
            have hfe : fiberOf (chainMap n f L') (chainMap n f L' a0) = B := by
              rw [hya, ← hB]
            rwa [hfe] at hmono
        · right; right
          have hle' : L' + 1 ≤ j := by omega
          have hmono : fiberOf (chainMap n f (L' + 1)) (chainMap n f (L' + 1) a0) ⊆ D := by
            rw [hDeq]
            exact fiberOf_chainMap_mono f hle' a0
          have hxval : chainMap n f (L' + 1) a0 = x := by
            have h1 : a0 ∈ fiberOf (chainMap n f (L' + 1)) x := by
              rw [hCx]
              exact ha0C
            exact mem_fiberOf.mp h1
          have hsub : A ∪ B ⊆ D := by
            rw [← hCx, ← hxval]
            exact hmono
          exact Finset.Subset.antisymm hDsub hsub
      have hAmax : ∀ D ∈ cladesOf n f, A ⊂ D → D ⊂ A ∪ B → False := by
        intro D hDT hAD hDC
        rcases hclassify D hDT hDC.1 with hsub | hsub | heq
        · have h1 := Finset.card_lt_card hAD
          have h2 := Finset.card_le_card hsub
          omega
        · have h1 : x ∈ D := hAD.1 hxInA
          have h2 : x ∈ B := hsub h1
          rw [hB, mem_fiberOf] at h2
          exact hxy (hx.symm.trans h2)
        · exact hDC.2 (heq ▸ Finset.Subset.refl D)
      have hBmax : ∀ D ∈ cladesOf n f, B ⊂ D → D ⊂ A ∪ B → False := by
        intro D hDT hBD hDC
        rcases hclassify D hDT hDC.1 with hsub | hsub | heq
        · have h1 : y ∈ D := hBD.1 hyInB
          have h2 : y ∈ A := hsub h1
          rw [hA, mem_fiberOf] at h2
          exact hxy (h2.symm.trans hy)
        · have h1 := Finset.card_lt_card hBD
          have h2 := Finset.card_le_card hsub
          omega
        · exact hDC.2 (heq ▸ Finset.Subset.refl D)
      have hAchild : A ∈ children (cladesOf n f) (A ∪ B) :=
        mem_children.mpr ⟨hAT, hAproper, hAmax⟩
      have hBchild : B ∈ children (cladesOf n f) (A ∪ B) :=
        mem_children.mpr ⟨hBT, hBproper, hBmax⟩
      have hchildren : children (cladesOf n f) (A ∪ B) = {A, B} := by
        ext D
        rw [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hD
          obtain ⟨hDT, hDC, -⟩ := mem_children.mp hD
          rcases hclassify D hDT hDC.1 with hsub | hsub | heq
          · by_cases hDA : D = A
            · exact Or.inl hDA
            · exfalso
              exact (children_maximal hD hAT
                (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hDA⟩)) hAproper
          · by_cases hDB : D = B
            · exact Or.inr hDB
            · exfalso
              exact (children_maximal hD hBT
                (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hDB⟩)) hBproper
          · exact absurd (heq ▸ Finset.Subset.refl D) hDC.2
        · rintro (rfl | rfl)
          · exact hAchild
          · exact hBchild
      rw [hchildren, Finset.card_insert_of_notMem (by simp [hAneB]), Finset.card_singleton]
    · rw [ite_eq_right hvx] at hv ⊢
      by_cases hvy : v = y
      · rw [ite_eq_left hvy] at hv ⊢
        rw [Finset.card_empty] at hv
        omega
      · rw [ite_eq_right hvy] at hv ⊢
        exact ih L' (by omega) hL'n v hv

/-- ★★★ **`cladesOf n f` 的二叉性**（(O1) 的偏序侧器材）：每个非单点 clade
恰有 `2` 个极大真子簇。

这是「`cladesOf` 的包含偏序 = 二叉树的结点偏序」的**定量**内容；
`LE` 一侧的线性扩展数正是在这个偏序上数的。 -/
theorem children_cladesOf_card_two {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {C : Finset (Fin n)} (hC : C ∈ cladesOf n f)
    (h2 : 2 ≤ C.card) :
    (children (cladesOf n f) C).card = 2 := by
  obtain ⟨j, hj, hCj⟩ := mem_cladesOf.mp hC
  obtain ⟨w, hw⟩ := nonempty_of_mem_blocksOf hCj
  have hCw : C = fiberOf (chainMap n f j) (chainMap n f j w) :=
    eq_fiberOf_of_mem_blocksOf hCj hw
  rw [hCw]
  exact children_fiberOf_chainMap_card_two hf j hj (chainMap n f j w) (hCw ▸ h2)

/-! ### §14.2 ★★★ 层分解**无重**（全局版）：`cladesOf` 的基数

`upto_succ_union` 只给出**逐步**事实（每步恰添一个新块，且新块不在旧的并里）。
本小节把它沿层**累加**成**全局**结论 —— 这正是 §14.1 具名缺件 ① 里
「各层新块之并**无重**」的那一半：

* `card_upto`：`(upto f L).card = n + L`（`L ≤ n - 1`）；
* `card_cladesOf`：`(cladesOf n f).card = 2 * n - 1`（二叉树的 `2n-1` 个 clade）；
* ★ `card_filter_nonsingleton_cladesOf`：**非单点 clade 恰 `n - 1` 个**
  —— (O1) 双射「创建序」一端的**载体基数**；
* ★ `children_fiberOf_chainMap_succ`：新块的 `children` **恰是**该步被合并的两块
  （把 §14 归纳证明里的 `hchildren` 一段**提升**成独立引理，供 `existsUnique_creation_level` 用）。

⚠️ 仍是 (O1) 的**器材**（数量半 ＋ 孩子半），不是 (O1) 本体（双射未给出）。 -/

/-- `id` 的纤维是单点（第 `0` 层的块全是单点）。 -/
theorem fiberOf_id {n : ℕ} (v : Fin n) : fiberOf (id : Fin n → Fin n) v = {v} := by
  ext z
  simp [fiberOf]

/-- `blocksOf` 与 `fiberOf` 的定义式一致（`image` 形式）。 -/
theorem blocksOf_eq_image_fiberOf {n : ℕ} (r : Fin n → Fin n) :
    blocksOf n r = (Finset.univ : Finset (Fin n)).image (fun w => fiberOf r (r w)) := rfl

/-- 第 `0` 层的块 = `n` 个单点。 -/
theorem blocksOf_zero {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) :
    blocksOf n (chainMap n f 0)
      = (Finset.univ : Finset (Fin n)).image (fun w => ({w} : Finset (Fin n))) := by
  have h0 : chainMap n f 0 = (id : Fin n → Fin n) := rfl
  have hfun : (fun w : Fin n => fiberOf (id : Fin n → Fin n) (id w))
      = (fun w : Fin n => ({w} : Finset (Fin n))) := by
    funext w
    rw [id_eq, fiberOf_id]
  rw [h0, blocksOf_eq_image_fiberOf, hfun]

/-- 第 `0` 层恰有 `n` 个块。 -/
theorem card_blocksOf_zero {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) :
    (blocksOf n (chainMap n f 0)).card = n := by
  rw [blocksOf_zero]
  have hinj : Function.Injective (fun w : Fin n => ({w} : Finset (Fin n))) := by
    intro a b hab
    have hab' : ({a} : Finset (Fin n)) = {b} := hab
    exact Finset.singleton_inj.mp hab'
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- `upto f 0` 就是第 `0` 层的块集。 -/
theorem upto_zero {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) :
    upto f 0 = blocksOf n (chainMap n f 0) := by
  ext D
  rw [mem_upto]
  constructor
  · rintro ⟨j, hj, h⟩
    have hj0 : j = 0 := by omega
    subst hj0
    exact h
  · intro h
    exact ⟨0, by omega, h⟩

/-- `upto` 随层数**单调**。 -/
theorem upto_subset {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) {L L' : ℕ} (h : L ≤ L') :
    upto f L ⊆ upto f L' := by
  intro D hD
  obtain ⟨j, hj, hjD⟩ := mem_upto.mp hD
  exact mem_upto.mpr ⟨j, by omega, hjD⟩

/-- **一步恰添一个新块**：`(upto f (L+1)).card = (upto f L).card + 1`。 -/
theorem upto_succ_card {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} (hf : IsMergeHistory n f)
    {L : ℕ} (hL : L < n - 1) : (upto f (L + 1)).card = (upto f L).card + 1 := by
  set x : Fin n := (f ⟨L, hL⟩).1 with hxdef
  set y : Fin n := (f ⟨L, hL⟩).2 with hydef
  have hpair : f ⟨L, hL⟩ = (x, y) := by rw [hxdef, hydef]
  have hstep := hf.1 ⟨L, hL⟩
  have hx : chainMap n f L x = x := by rw [hxdef]; exact hstep.1
  have hy : chainMap n f L y = y := by rw [hydef]; exact hstep.2.1
  have hxy : x ≠ y := by rw [hxdef, hydef]; exact ne_of_lt hstep.2.2
  have hU := upto_succ_union (f := f) hL hpair hx
  have hnot := not_mem_upto_union (f := f) hx hy hxy
  rw [hU, Finset.union_singleton, Finset.card_insert_of_notMem hnot]

/-- 前 `L+1` 层共 `n + L` 个块（`n` 个单点 ＋ 每步恰一个新块）。 -/
theorem card_upto {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} (hf : IsMergeHistory n f) :
    ∀ L, L ≤ n - 1 → (upto f L).card = n + L := by
  intro L
  induction L with
  | zero =>
    intro _
    rw [upto_zero, card_blocksOf_zero]
    omega
  | succ L ih =>
    intro hL1
    have hL : L < n - 1 := by omega
    rw [upto_succ_card (f := f) hf hL, ih (by omega)]
    omega

/-- `cladesOf n f` 就是到第 `n-1` 层为止的块并。 -/
theorem cladesOf_eq_upto {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) :
    cladesOf n f = upto f (n - 1) := by
  ext D
  rw [mem_cladesOf, mem_upto]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩
    obtain ⟨z, hz⟩ := nonempty_of_mem_blocksOf h
    have hzn : z.val < n := z.isLt
    exact ⟨j, by omega, h⟩

/-- ★★★ **`cladesOf` 的基数 = `2n - 1`**（`n` 个叶的二叉树恰有 `2n-1` 个 clade）。 -/
theorem card_cladesOf {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) : (cladesOf n f).card = 2 * n - 1 := by
  rw [cladesOf_eq_upto f, card_upto hf (n - 1) (by omega)]
  omega

/-- 前 `L+1` 层里**非单点**块恰 `L` 个（每步新块必非单点，旧块里单点只有 `n` 个）。 -/
theorem card_upto_filter {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} (hf : IsMergeHistory n f) :
    ∀ L, L ≤ n - 1 → ((upto f L).filter (fun C => 2 ≤ C.card)).card = L := by
  intro L
  induction L with
  | zero =>
    intro _
    rw [upto_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro D hD h2
    obtain ⟨w, hw⟩ := exists_fiberOf_of_mem_blocksOf hD
    have h0 : chainMap n f 0 = (id : Fin n → Fin n) := rfl
    have h1 : D.card = 1 := by rw [hw, h0, fiberOf_id]; simp
    omega
  | succ L ih =>
    intro hL1
    have hL : L < n - 1 := by omega
    set x : Fin n := (f ⟨L, hL⟩).1 with hxdef
    set y : Fin n := (f ⟨L, hL⟩).2 with hydef
    have hpair : f ⟨L, hL⟩ = (x, y) := by rw [hxdef, hydef]
    have hstep := hf.1 ⟨L, hL⟩
    have hx : chainMap n f L x = x := by rw [hxdef]; exact hstep.1
    have hy : chainMap n f L y = y := by rw [hydef]; exact hstep.2.1
    have hxy : x ≠ y := by rw [hxdef, hydef]; exact ne_of_lt hstep.2.2
    have hU := upto_succ_union (f := f) hL hpair hx
    have hnot := not_mem_upto_union (f := f) hx hy hxy
    have hxInA : x ∈ fiberOf (chainMap n f L) x := mem_fiberOf.mpr hx
    have hyInB : y ∈ fiberOf (chainMap n f L) y := mem_fiberOf.mpr hy
    have h2AB : 2 ≤ (fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y).card := by
      have hsub : ({x, y} : Finset (Fin n))
          ⊆ fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_left _ hxInA
        · exact Finset.mem_union_right _ hyInB
      have hcard : ({x, y} : Finset (Fin n)).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
      have hle := Finset.card_le_card hsub
      omega
    rw [hU, Finset.filter_union, Finset.filter_singleton, ite_eq_left h2AB,
      Finset.union_singleton,
      Finset.card_insert_of_notMem (fun hmem => hnot (Finset.mem_of_mem_filter _ hmem)),
      ih (by omega)]

/-- ★★★ **非单点 clade 恰 `n - 1` 个** —— (O1) 双射「创建序」的**载体基数**。 -/
theorem card_filter_nonsingleton_cladesOf {n : ℕ}
    {f : Fin (n - 1) → Fin n × Fin n} (hf : IsMergeHistory n f) :
    ((cladesOf n f).filter (fun C => 2 ≤ C.card)).card = n - 1 := by
  rw [cladesOf_eq_upto f, card_upto_filter hf (n - 1) (by omega)]

/-- ★★★ **(O1) 具名缺件 ① 的定性半**：第 `L` 步合并出的新块 `A ∪ B` 在
`cladesOf n f` 里的 `children` **恰是**该步被合并的两块 `A`、`B`。 -/
theorem children_fiberOf_chainMap_succ {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {L : ℕ}
    (hL : L < n - 1) {x y : Fin n} (hpair : f ⟨L, hL⟩ = (x, y))
    (hx : chainMap n f L x = x) (hy : chainMap n f L y = y) (hxy : x ≠ y) :
    children (cladesOf n f) (fiberOf (chainMap n f L) x ∪ fiberOf (chainMap n f L) y)
      = {fiberOf (chainMap n f L) x, fiberOf (chainMap n f L) y} := by
  have hLn : L < n := by omega
  have hsucc : chainMap n f (L + 1) = stepMap (chainMap n f L) x y := by
    rw [chainMap_succ, dite_eq_left hL, hpair]
  set A : Finset (Fin n) := fiberOf (chainMap n f L) x with hA
  set B : Finset (Fin n) := fiberOf (chainMap n f L) y with hB
  have hCx : fiberOf (chainMap n f (L + 1)) x = A ∪ B := by
    rw [hsucc, fiberOf_stepMap, ite_eq_left rfl, ← hA, ← hB]
  have hAT : A ∈ cladesOf n f := by
    rw [hA]
    exact mem_cladesOf.mpr ⟨L, hLn, hx ▸ fiberOf_mem_blocksOf (chainMap n f L) x⟩
  have hBT : B ∈ cladesOf n f := by
    rw [hB]
    exact mem_cladesOf.mpr ⟨L, hLn, hy ▸ fiberOf_mem_blocksOf (chainMap n f L) y⟩
  have hxInA : x ∈ A := by rw [hA]; exact mem_fiberOf.mpr hx
  have hyInB : y ∈ B := by rw [hB]; exact mem_fiberOf.mpr hy
  have hAneB : A ≠ B := by
    intro heq
    have h1 : x ∈ B := heq ▸ hxInA
    rw [hB, mem_fiberOf] at h1
    exact hxy (hx.symm.trans h1)
  have hyNotA : y ∉ A := by
    intro h
    rw [hA, mem_fiberOf] at h
    exact hxy (h.symm.trans hy)
  have hxNotB : x ∉ B := by
    intro h
    rw [hB, mem_fiberOf] at h
    exact hxy (hx.symm.trans h)
  have hAproper : A ⊂ A ∪ B := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
    intro heq
    have h1 : y ∈ A ∪ B := Finset.mem_union_right A hyInB
    rw [← heq] at h1
    exact hyNotA h1
  have hBproper : B ⊂ A ∪ B := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
    intro heq
    have h1 : x ∈ A ∪ B := Finset.mem_union_left B hxInA
    rw [← heq] at h1
    exact hxNotB h1
  have hclassify : ∀ D ∈ cladesOf n f, D ⊆ A ∪ B → D ⊆ A ∨ D ⊆ B ∨ D = A ∪ B := by
    intro D hDT hDsub
    obtain ⟨j, hj, hDj⟩ := mem_cladesOf.mp hDT
    obtain ⟨a0, ha0⟩ := nonempty_of_mem_blocksOf hDj
    have hDeq : D = fiberOf (chainMap n f j) (chainMap n f j a0) :=
      eq_fiberOf_of_mem_blocksOf hDj ha0
    have ha0C : a0 ∈ A ∪ B := hDsub ha0
    by_cases hle : j ≤ L
    · have hmono : D ⊆ fiberOf (chainMap n f L) (chainMap n f L a0) := by
        rw [hDeq]
        exact fiberOf_chainMap_mono f hle a0
      rcases Finset.mem_union.mp ha0C with h | h
      · left
        have hxa : chainMap n f L a0 = x := mem_fiberOf.mp (hA ▸ h)
        have hfe : fiberOf (chainMap n f L) (chainMap n f L a0) = A := by
          rw [hxa, ← hA]
        rwa [hfe] at hmono
      · right; left
        have hya : chainMap n f L a0 = y := mem_fiberOf.mp (hB ▸ h)
        have hfe : fiberOf (chainMap n f L) (chainMap n f L a0) = B := by
          rw [hya, ← hB]
        rwa [hfe] at hmono
    · right; right
      have hle' : L + 1 ≤ j := by omega
      have hmono : fiberOf (chainMap n f (L + 1)) (chainMap n f (L + 1) a0) ⊆ D := by
        rw [hDeq]
        exact fiberOf_chainMap_mono f hle' a0
      have hxval : chainMap n f (L + 1) a0 = x := by
        have h1 : a0 ∈ fiberOf (chainMap n f (L + 1)) x := by
          rw [hCx]
          exact ha0C
        exact mem_fiberOf.mp h1
      have hsub : A ∪ B ⊆ D := by
        rw [← hCx, ← hxval]
        exact hmono
      exact Finset.Subset.antisymm hDsub hsub
  have hAmax : ∀ D ∈ cladesOf n f, A ⊂ D → D ⊂ A ∪ B → False := by
    intro D hDT hAD hDC
    rcases hclassify D hDT hDC.1 with hsub | hsub | heq
    · have h1 := Finset.card_lt_card hAD
      have h2 := Finset.card_le_card hsub
      omega
    · have h1 : x ∈ D := hAD.1 hxInA
      have h2 : x ∈ B := hsub h1
      rw [hB, mem_fiberOf] at h2
      exact hxy (hx.symm.trans h2)
    · exact hDC.2 (heq ▸ Finset.Subset.refl D)
  have hBmax : ∀ D ∈ cladesOf n f, B ⊂ D → D ⊂ A ∪ B → False := by
    intro D hDT hBD hDC
    rcases hclassify D hDT hDC.1 with hsub | hsub | heq
    · have h1 : y ∈ D := hBD.1 hyInB
      have h2 : y ∈ A := hsub h1
      rw [hA, mem_fiberOf] at h2
      exact hxy (h2.symm.trans hy)
    · have h1 := Finset.card_lt_card hBD
      have h2 := Finset.card_le_card hsub
      omega
    · exact hDC.2 (heq ▸ Finset.Subset.refl D)
  have hAchild : A ∈ children (cladesOf n f) (A ∪ B) :=
    mem_children.mpr ⟨hAT, hAproper, hAmax⟩
  have hBchild : B ∈ children (cladesOf n f) (A ∪ B) :=
    mem_children.mpr ⟨hBT, hBproper, hBmax⟩
  ext D
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hD
    obtain ⟨hDT, hDC, -⟩ := mem_children.mp hD
    rcases hclassify D hDT hDC.1 with hsub | hsub | heq
    · by_cases hDA : D = A
      · exact Or.inl hDA
      · exfalso
        exact (children_maximal hD hAT
          (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hDA⟩)) hAproper
    · by_cases hDB : D = B
      · exact Or.inr hDB
      · exfalso
        exact (children_maximal hD hBT
          (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hDB⟩)) hBproper
    · exact absurd (heq ▸ Finset.Subset.refl D) hDC.2
  · rintro (rfl | rfl)
    · exact hAchild
    · exact hBchild

/-! ### §14.3 ★★★ (O1) 具名缺件 ①：`existsUnique_creation_level`

`card_filter_nonsingleton_cladesOf` 给出「非单点 clade 恰 `n - 1` 个」，
`children_fiberOf_chainMap_succ` 给出「新块的孩子恰为被合并的两块」。
本小节把两者并成 §14.1 里**具名缺件 ①** 的完整陈述：

> 每个非单点 clade `C` **唯一**确定一个「创建步」`k : Fin (n-1)`：
> `C` 在第 `k+1` 层成为块（`C ∈ blocksOf (chainMap (k+1))`）、
> 不在前 `k` 层出现过（`C ∉ upto f k`）、且 `children (cladesOf n f) C`
> 恰是第 `k` 步被合并的两块。

即：`C ↦ k` 是 `{C ∈ cladesOf n f : 2 ≤ |C|} → Fin (n-1)` 的**单射**
（单射 = 本小节末尾的 `eq_of_mem_blocksOf_succ`：同一步至多一个新非单点块；
配合 `card_filter_nonsingleton_cladesOf` 即为**双射**）——
这就是「创建序」这一端的全部组合内容。 -/

/-- ★★★ **(O1) 具名缺件 ①**：每个非单点 clade 的**创建步唯一**，
且 `children` 恰为该步被合并的两块。 -/
theorem existsUnique_creation_level {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {C : Finset (Fin n)} (hC : C ∈ cladesOf n f) (h2 : 2 ≤ C.card) :
    ∃! k : Fin (n - 1),
      C ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)) ∧ C ∉ upto f (k : ℕ) ∧
        children (cladesOf n f) C
          = {fiberOf (chainMap n f (k : ℕ)) (f k).1,
              fiberOf (chainMap n f (k : ℕ)) (f k).2} := by
  have hCn : C ∈ upto f (n - 1) := by
    rw [← cladesOf_eq_upto f]
    exact hC
  -- 第 `0` 层没有非单点块
  have hC0 : C ∉ upto f 0 := by
    intro hmem
    rw [upto_zero] at hmem
    obtain ⟨w, hw⟩ := exists_fiberOf_of_mem_blocksOf hmem
    have h0 : chainMap n f 0 = (id : Fin n → Fin n) := rfl
    have h1 : C.card = 1 := by rw [hw, h0, fiberOf_id]; simp
    omega
  -- 最小层 `m`（`C` 首次成为块的那一层）
  have hex : ∃ j : ℕ, C ∈ upto f j := ⟨n - 1, hCn⟩
  set m : ℕ := Nat.find hex with hm
  have hm_spec : C ∈ upto f m := by
    rw [hm]
    exact Nat.find_spec hex
  have hm_min : ∀ j, j < m → C ∉ upto f j := by
    intro j hj
    rw [hm] at hj
    exact Nat.find_min hex hj
  have hm_le : m ≤ n - 1 := by
    by_contra hlt
    exact hm_min (n - 1) (by omega) hCn
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (h ▸ hm_spec) hC0
    · exact h
  -- 创建步 `k = m - 1`
  set k : Fin (n - 1) := ⟨m - 1, by omega⟩ with hk
  have hkval : (k : ℕ) = m - 1 := rfl
  have hk1 : (k : ℕ) + 1 = m := by rw [hkval]; omega
  have hklt : (k : ℕ) < m := by rw [hkval]; omega
  have hnotK : C ∉ upto f (k : ℕ) := hm_min (k : ℕ) hklt
  have hmemB : C ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)) := by
    have hspec' : C ∈ upto f ((k : ℕ) + 1) := by rw [hk1]; exact hm_spec
    rw [upto_succ f (k : ℕ)] at hspec'
    rcases Finset.mem_union.mp hspec' with h | h
    · exact absurd h hnotK
    · exact h
  -- `C` 就是第 `k` 步合并出的新块 `A ∪ B`
  have hstep := hf.1 k
  have hx : chainMap n f (k : ℕ) (f k).1 = (f k).1 := hstep.1
  have hy : chainMap n f (k : ℕ) (f k).2 = (f k).2 := hstep.2.1
  have hxy : (f k).1 ≠ (f k).2 := ne_of_lt hstep.2.2
  have hsucck : chainMap n f ((k : ℕ) + 1)
      = stepMap (chainMap n f (k : ℕ)) (f k).1 (f k).2 := by
    rw [chainMap_succ, dite_eq_left k.isLt]
  have hCe : C = fiberOf (chainMap n f (k : ℕ)) (f k).1
      ∪ fiberOf (chainMap n f (k : ℕ)) (f k).2 := by
    have hmemB' : C ∈ blocksOf n (stepMap (chainMap n f (k : ℕ)) (f k).1 (f k).2) := by
      rw [← hsucck]
      exact hmemB
    have hsub := blocksOf_stepMap_subset (chainMap n f (k : ℕ)) (f k).1 (f k).2 hmemB'
    rcases Finset.mem_union.mp hsub with h | h
    · exact absurd (mem_upto_of_le (le_refl (k : ℕ)) h) hnotK
    · rw [Finset.mem_singleton] at h
      exact h
  have hchild : children (cladesOf n f) C
      = {fiberOf (chainMap n f (k : ℕ)) (f k).1,
          fiberOf (chainMap n f (k : ℕ)) (f k).2} := by
    rw [hCe]
    exact children_fiberOf_chainMap_succ k.isLt rfl hx hy hxy
  refine ⟨k, ⟨hmemB, hnotK, hchild⟩, ?_⟩
  -- 唯一性：任何满足条件的 `k'` 与 `k` 的创建层相同
  intro k' hk'
  obtain ⟨hmemB', hnotK', -⟩ := hk'
  have hmemU : C ∈ upto f ((k : ℕ) + 1) := mem_upto_of_le (le_refl ((k : ℕ) + 1)) hmemB
  have hmemU' : C ∈ upto f ((k' : ℕ) + 1) :=
    mem_upto_of_le (le_refl ((k' : ℕ) + 1)) hmemB'
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hnotK (upto_subset f (by omega) hmemU')
  · exact hnotK' (upto_subset f (by omega) hmemU)

/-- ★★★ **同一步至多创建一个非单点块**（「无重」的直接形式）：
两个都在第 `k+1` 层成为块、且都没在前 `k` 层出现过，则它们**必相等**。
这是「非单点 clade ↦ 创建步」映射**单射**的来源。 -/
theorem eq_of_mem_blocksOf_succ {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} {k : Fin (n - 1)}
    {C C' : Finset (Fin n)}
    (hC : C ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)))
    (hC' : C' ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)))
    (hnC : C ∉ upto f (k : ℕ)) (hnC' : C' ∉ upto f (k : ℕ)) : C = C' := by
  have hsucck : chainMap n f ((k : ℕ) + 1)
      = stepMap (chainMap n f (k : ℕ)) (f k).1 (f k).2 := by
    rw [chainMap_succ, dite_eq_left k.isLt]
  have key : ∀ D : Finset (Fin n), D ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)) →
      D ∉ upto f (k : ℕ) →
      D = fiberOf (chainMap n f (k : ℕ)) (f k).1
        ∪ fiberOf (chainMap n f (k : ℕ)) (f k).2 := by
    intro D hD hnD
    have hD' : D ∈ blocksOf n (stepMap (chainMap n f (k : ℕ)) (f k).1 (f k).2) := by
      rw [← hsucck]
      exact hD
    have hsub := blocksOf_stepMap_subset (chainMap n f (k : ℕ)) (f k).1 (f k).2 hD'
    rcases Finset.mem_union.mp hsub with h | h
    · exact absurd (mem_upto_of_le (le_refl (k : ℕ)) h) hnD
    · rw [Finset.mem_singleton] at h
      exact h
  rw [key C hC hnC, key C' hC' hnC']

/-! ### §14.1 (O1) 的**诚实边界**（本节**没有**做的事，逐件具名）

`children_cladesOf_card_two` 把 (O1) 双射**两端对象的形状**对齐了
（纤维一侧是「二叉树上的合并序」，`LE` 一侧是「二叉树偏序上的线性扩展」），
但双射本身**未给出**。剩余内容精确地是**两件**：

1. ✅ **`cladesOf` 的层分解无重** —— **W26 泳道 b 已落地**：由
   `card_cladesOf`（`|cladesOf n f| = 2n-1`）、`card_filter_nonsingleton_cladesOf`
   （非单点 clade 恰 `n-1` 个）与 `existsUnique_creation_level`
   （每个非单点 `C` **唯一**确定创建步 `k : Fin (n-1)`：`C` 在第 `k+1` 层成为块、
   前 `k` 层未出现、且 `children (cladesOf n f) C` 恰是第 `k` 步被合并的两块）
   **共同给出**「非单点 clade ↔ 创建步」这一端的**双射**
   （单射 = `eq_of_mem_blocksOf_succ`：同一步至多一个新非单点块；
   基数对消 = `card_filter_nonsingleton_cladesOf`）。
   ✅ **W26 泳道 f 已落地**（本文件 §14.4–§14.5）：**重建映射**
   `reconstruct (S) (σ) (d)`，第 `k` 步按「`C = σ k` 的最小元 `x` ＋ 含 `x` 的孩子」
   读出合并对 `(min' C, min' (C \ 含 x 的孩子))`。四条已证：
   `reconstructStep_eq`（读数正确）、**`reconstruct_newClade_eq`（左逆：重建 = `f`）**、
   **`cladesOf_reconstruct_newClade`（往返引理：`cladesOf` 复原）**、
   **`eq_of_newClade_eq`（单射）**、**`image_newClade` / `existsUnique_newClade`（满射：
   `k ↦ newClade f k` 恰枚举非单点 clade）**。
   ⬜ **仍缺**（(O1) 本体的最后一块）：把「**合法创建序**」刻画成 `S` 上的偏序 ——
   `σ` 合法 ⟺ `σ` 是 `S` 的非单点 clade 在**严格包含序**下的**线性扩展**
   （即 `D ⊊ σ k ⟹ D = σ j` 且 `j < k`），从而纤维基数 `= ` 线性扩展数；
   再与下面第 2 件的 `LinExt` 对上。
2. ★ **`LE` = 线性扩展数**：`LE`（§8）现在是**多项式系数递推**。要把它认成「创建序的个数」，
   需要自造线性扩展计数 `LinExt`（`internalBelow T C` 上按 `⊊` 的线性扩展数）
   ＋ **交错引理** `LinExt C = multinomial(hook 孩子) · ∏ LinExt 孩子`
   （孩子子树的线性扩展在**块间插空**）。
   **缺的具名器材**：`LinExt` ＋ `LinExt_eq`（交错引理）。
   ⚠️ Mathlib **没有**线性扩展的**计数**（`Mathlib/Order/Extension/Linear.lean` 只有
   `LinearExtension` 类型别名与存在性 `extend_partialOrder`，见 §8 的三次 grep）
   ⇒ 这件必须自造，且交错引理是**真正的组合作业**（`Finset`/`Multiset` 层面的洗牌双射）。

⇒ `rankedFiberCount_gap` **仍开着**（(O1) 未证）；可复用增量是 §14 的二叉性定理
＋ **§14.2/§14.3 的层分解无重**（创建步存在唯一 ＋ 基数 `2n-1` / 非单点 `n-1`）。
-/

/-! ### §14.4 ★★★ (O1) 重建映射：`clade 集 ＋ 创建块 ↦ 合并对`

§14.3 给出方向「非单点 clade ↦ 创建步」。本小节给出**反方向**：
由「clade 集 `S`」与「第 `k` 步创建出的块 `C_k`」读出第 `k` 步被合并的两块。

关键事实：**块的代表元就是块的最小元**（`min'_fiberOf_chainMap`）。
故第 `k` 步被合并的两块的代表元 ＝ 这两块**各自的最小元**；按「最小元的较小者在前」
排序后，合并对由 `C_k` 与它的两个孩子**唯一确定**（`reconstructStep`）。 -/

/-- 块代表元从**不超过**块内任意元素：`chainMap n f L z ≤ z`。
（归纳：每步 `x < y`，`y` 的块并入 `x` 的块后新代表元 `x` 更小。） -/
theorem le_chainMap_self {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n} (hf : IsMergeHistory n f) :
    ∀ (L : ℕ) (z : Fin n), chainMap n f L z ≤ z := by
  intro L
  induction L with
  | zero => intro z; exact le_refl z
  | succ L ih =>
    intro z
    rw [chainMap_succ]
    split_ifs with h
    · rw [stepMap]
      split_ifs with hz
      · exact le_trans ((hf.1 ⟨L, h⟩).2.2).le (hz ▸ ih z)
      · exact ih z
    · exact ih z

/-- ★★ **代表元就是块的最小元**：`v` 是第 `L` 层的块代表元（`chainMap n f L v = v`）
⇒ 纤维 `v` 的最小元是 `v`。 -/
theorem min'_fiberOf_chainMap {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {L : ℕ} {v : Fin n} (hv : chainMap n f L v = v)
    (hne : (fiberOf (chainMap n f L) v).Nonempty) :
    (fiberOf (chainMap n f L) v).min' hne = v := by
  rw [Finset.min'_eq_iff]
  refine ⟨mem_fiberOf.mpr hv, fun b hb => ?_⟩
  rw [mem_fiberOf] at hb
  exact hb ▸ le_chainMap_self hf L b

/-- 第 `k` 步**合并出的新块**（两块纤维之并）。 -/
def newClade {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) (k : Fin (n - 1)) : Finset (Fin n) :=
  fiberOf (chainMap n f (k : ℕ)) (f k).1 ∪ fiberOf (chainMap n f (k : ℕ)) (f k).2

/-- 新块就是第 `k+1` 层里 `(f k).1` 的纤维。 -/
theorem newClade_eq_fiberOf_succ {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n)
    (k : Fin (n - 1)) :
    newClade f k = fiberOf (chainMap n f ((k : ℕ) + 1)) (f k).1 := by
  rw [newClade, chainMap_succ, dite_eq_left k.isLt, fiberOf_stepMap, ite_eq_left rfl]

/-- 新块属于 `cladesOf n f`。 -/
theorem mem_cladesOf_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) : newClade f k ∈ cladesOf n f := by
  refine mem_cladesOf.mpr ⟨(k : ℕ) + 1, by omega, ?_⟩
  rw [newClade_eq_fiberOf_succ]
  refine fiberOf_mem_blocksOf_of_nonempty ⟨(f k).1, mem_fiberOf.mpr ?_⟩
  rw [chainMap_succ, dite_eq_left k.isLt, stepMap]
  by_cases h : chainMap n f (k : ℕ) (f k).1 = (f k).2
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact (hf.1 k).1

/-- 第 `k` 步被合并的两块**不交**。 -/
theorem disjoint_newClade_fibers {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) :
    Disjoint (fiberOf (chainMap n f (k : ℕ)) (f k).1)
      (fiberOf (chainMap n f (k : ℕ)) (f k).2) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  rw [mem_fiberOf] at hz1 hz2
  exact absurd (hz1.symm.trans hz2) (ne_of_lt (hf.1 k).2.2)

/-- `(f k).1` 不在 `(f k).2` 的纤维里。 -/
theorem not_mem_fiberOf_snd {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) :
    (f k).1 ∉ fiberOf (chainMap n f (k : ℕ)) (f k).2 := by
  intro h
  rw [mem_fiberOf] at h
  exact absurd ((hf.1 k).1 ▸ h) (ne_of_lt (hf.1 k).2.2)

/-- ★★★ 新块的**孩子**恰是第 `k` 步被合并的两块
（§14.2 的 `children_fiberOf_chainMap_succ` 在 `newClade` 上的重述）。 -/
theorem children_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) :
    children (cladesOf n f) (newClade f k)
      = {fiberOf (chainMap n f (k : ℕ)) (f k).1,
          fiberOf (chainMap n f (k : ℕ)) (f k).2} :=
  children_fiberOf_chainMap_succ k.isLt rfl (hf.1 k).1 (hf.1 k).2.1 (ne_of_lt (hf.1 k).2.2)
/-- `s` 的最小元；`s` 空时退化为 `d`（`Finset.min'` 的非空保险，
使 `reconstructStep` 成为**无证明参数**的函数）。 -/
noncomputable def minOr {n : ℕ} (d : Fin n) (s : Finset (Fin n)) : Fin n :=
  if h : s = ∅ then d else s.min' (Finset.nonempty_iff_ne_empty.mpr h)

/-- `minOr` 在非空集上就是 `min'`。 -/
theorem minOr_of_nonempty {n : ℕ} {d : Fin n} {s : Finset (Fin n)} (h : s.Nonempty) :
    minOr d s = s.min' h := by
  unfold minOr
  rw [dite_eq_right (Finset.nonempty_iff_ne_empty.mp h)]

/-- ★★★ **(O1) 重建映射（单步）**：由「clade 集 `S`」与「第 `k` 步创建出的块 `C`」
读出第 `k` 步的**合并对**：

* `x = min' C` —— 被合并两块中**较小者**的代表元；
* `a = ⋃ {D ∈ children S C : x ∈ D}` —— 含 `x` 的那个孩子（孩子镶嵌 ⇒ 恰一个）；
* `y = min' (C \ a)` —— 另一块的代表元。

`C = a ∪ (C \ a)`、两孩子非空都由 `S` 的镶嵌结构给出，**与 `f` 无关**；
`f` 只用来命名「第 `k` 步的创建块」`C = σ k`。`d` 只是空集情形的退化值。 -/
noncomputable def reconstructStep {n : ℕ} (S : Finset (Finset (Fin n))) (C : Finset (Fin n))
    (d : Fin n) : Fin n × Fin n :=
  let x := minOr d C
  (x, minOr x (C \ ((children S C).filter (fun D => x ∈ D)).biUnion id))

/-- ★★★ **重建出的合并史**：第 `k` 步由 `S` 与「第 `k` 步创建块 `σ k`」读出。 -/
noncomputable def reconstruct {n : ℕ} (S : Finset (Finset (Fin n)))
    (σ : Fin (n - 1) → Finset (Fin n)) (d : Fin n) : Fin (n - 1) → Fin n × Fin n :=
  fun k => reconstructStep S (σ k) d

/-- `reconstructStep` 的**计算规则**：若 `C = A ∪ B`（`A, B` 不交，`x ∈ A`、`y ∈ B` 分别是
两块的最小元，`x < y`），且 `A`、`B` 恰是 `C` 在 `S` 中的两个孩子，则
`reconstructStep S C = (x, y)`（与退化值 `d` 无关）。 -/
theorem reconstructStep_eq {n : ℕ} {S : Finset (Finset (Fin n))}
    {C A B : Finset (Fin n)} {x y : Fin n} (d : Fin n) (hC : C.Nonempty)
    (hCAB : C = A ∪ B) (hAB : Disjoint A B) (hxA : x ∈ A) (hyB : y ∈ B)
    (hminA : ∀ b ∈ A, x ≤ b) (hminB : ∀ b ∈ B, y ≤ b) (hxy : x < y)
    (hchildren : children S C = {A, B}) :
    reconstructStep S C d = (x, y) := by
  have hxnotB : x ∉ B := fun h => absurd (hminB x h) (not_le.mpr hxy)
  have hxminC : C.min' hC = x := by
    rw [Finset.min'_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [hCAB]
      exact Finset.mem_union_left B hxA
    · intro b hb
      rw [hCAB, Finset.mem_union] at hb
      rcases hb with hb | hb
      · exact hminA b hb
      · exact le_trans hxy.le (hminB b hb)
  have hminC : minOr d C = x := by
    rw [minOr_of_nonempty hC, hxminC]
  have hfilter : (children S C).filter (fun D => x ∈ D) = {A} := by
    rw [hchildren]
    ext D
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hD, hxD⟩
      rcases hD with rfl | rfl
      · rfl
      · exact absurd hxD hxnotB
    · rintro rfl
      exact ⟨Or.inl rfl, hxA⟩
  have hfilterC : (children S C).filter (fun D => minOr d C ∈ D) = {A} := by
    rw [hminC]
    exact hfilter
  have hunionC : ((children S C).filter (fun D => minOr d C ∈ D)).biUnion id = A := by
    rw [hfilterC]
    simp
  have hBA : C \ A = B := by
    rw [hCAB]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hz | hz, hnz⟩
      · exact absurd hz hnz
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, fun hzA => Finset.disjoint_left.mp hAB hzA hz⟩
  have hminB' : ∀ (h : B.Nonempty), B.min' h = y := by
    intro h
    rw [Finset.min'_eq_iff]
    exact ⟨hyB, hminB⟩
  have hminOrB : minOr (minOr d C) B = y := by
    rw [minOr_of_nonempty ⟨y, hyB⟩, hminB' ⟨y, hyB⟩]
  have hstep : reconstructStep S C d = (minOr d C, y) := by
    unfold reconstructStep
    dsimp only
    rw [hunionC, hBA, hminOrB]
  rw [hstep, hminC]
/-- 第 `k` 步新块非空（含 `(f k).1`）。 -/
theorem newClade_nonempty {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) : (newClade f k).Nonempty :=
  ⟨(f k).1, Finset.mem_union_left _ (mem_fiberOf.mpr (hf.1 k).1)⟩

/-- ★★★★ **(O1) 重建映射是左逆**：用「`cladesOf n f` ＋ 第 `k` 步的新块 `newClade f k`」
重建出的合并史**就是** `f`（对任意退化值 `d`）。

（证明要点：`min' (newClade f k) = (f k).1`、另一块的最小元 `= (f k).2`
—— 即 `min'_fiberOf_chainMap`：**代表元就是块的最小元**。） -/
theorem reconstruct_newClade_eq {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (d : Fin n) :
    reconstruct (cladesOf n f) (fun k => newClade f k) d = f := by
  funext k
  refine reconstructStep_eq d (newClade_nonempty hf k) rfl (disjoint_newClade_fibers hf k)
    (mem_fiberOf.mpr (hf.1 k).1) (mem_fiberOf.mpr (hf.1 k).2.1) ?_ ?_ (hf.1 k).2.2
    (children_newClade hf k)
  · intro b hb
    have hne : (fiberOf (chainMap n f (k : ℕ)) (f k).1).Nonempty := ⟨_, mem_fiberOf.mpr (hf.1 k).1⟩
    rw [← min'_fiberOf_chainMap hf (L := (k : ℕ)) (v := (f k).1) (hf.1 k).1 hne]
    exact Finset.min'_le _ b hb
  · intro b hb
    have hne : (fiberOf (chainMap n f (k : ℕ)) (f k).2).Nonempty := ⟨_, mem_fiberOf.mpr (hf.1 k).2.1⟩
    rw [← min'_fiberOf_chainMap hf (L := (k : ℕ)) (v := (f k).2) (hf.1 k).2.1 hne]
    exact Finset.min'_le _ b hb

/-- ★★★★ **(O1) 往返引理（本泳道交付的主体）**：
**由 `cladesOf n f` 按「创建块 = `newClade f ·`」重建出的合并史与 `f` 有相同的 clade 集**
—— 即重建映射的 `cladesOf` 侧是恒等。 -/
theorem cladesOf_reconstruct_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (d : Fin n) :
    cladesOf n (reconstruct (cladesOf n f) (fun k => newClade f k) d) = cladesOf n f := by
  rw [reconstruct_newClade_eq hf d]

/-- 重建出的编码**仍是合并史**（`IsMergeHistory` 在重建下不变）。 -/
theorem isMergeHistory_reconstruct_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (d : Fin n) :
    IsMergeHistory n (reconstruct (cladesOf n f) (fun k => newClade f k) d) := by
  rw [reconstruct_newClade_eq hf d]
  exact hf

/-- ★★★★ **(O1) 双射的「单射」半**：合并史由「clade 集 ＋ 每步创建出的块」**唯一确定**
—— 即 `f ↦ (cladesOf n f, newClade f ·)` 是**单射**。

（这就是 (O1) 里「纤维 ↪ 合法创建序」的方向；剩下的「满射 ＋ 计数」
=「合法创建序的个数 = `LE`」，见本节末尾的边界说明。） -/
theorem eq_of_newClade_eq {n : ℕ} {f f' : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (hf' : IsMergeHistory n f')
    (hS : cladesOf n f = cladesOf n f') (h : ∀ k, newClade f k = newClade f' k) : f = f' := by
  funext k
  rw [← congrFun (reconstruct_newClade_eq hf (f k).1) k,
    ← congrFun (reconstruct_newClade_eq hf' (f k).1) k, hS, funext h]
/-! ### §14.5 ★★★ (O1) 「创建块」恰枚举**非单点 clade**

`newClade f · : Fin (n-1) → Finset (Fin n)` 满足：

* 落在 `cladesOf n f` 里且非单点（`two_le_card_newClade`）；
* **单射**（`newClade_injective`：同一步至多一个新块 ⇒ 不同步的新块不同）；
* 定义域基数是 `n-1`，而非单点 clade 也恰有 `n-1` 个（`card_filter_nonsingleton_cladesOf`）
  ⇒ 像是**满的**：`image_newClade`。

推论 `existsUnique_newClade`：**每个非单点 clade 恰是某一步创建出的新块**
（这就是「创建序」这一端所需的**满射性**，与 §14.3 的 `existsUnique_creation_level` 互补）。 -/

/-- 新块在第 `k+1` 层是块。 -/
theorem mem_blocksOf_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) :
    newClade f k ∈ blocksOf n (chainMap n f ((k : ℕ) + 1)) := by
  rw [newClade_eq_fiberOf_succ]
  refine fiberOf_mem_blocksOf_of_nonempty ⟨(f k).1, mem_fiberOf.mpr ?_⟩
  rw [chainMap_succ, dite_eq_left k.isLt, stepMap]
  by_cases h : chainMap n f (k : ℕ) (f k).1 = (f k).2
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact (hf.1 k).1

/-- 新块**不在**更低层出现过。 -/
theorem not_mem_upto_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) : newClade f k ∉ upto f (k : ℕ) :=
  not_mem_upto_union (f := f) (L := (k : ℕ)) (x := (f k).1) (y := (f k).2)
    (hf.1 k).1 (hf.1 k).2.1 (ne_of_lt (hf.1 k).2.2)

/-- 新块至少两个元素。 -/
theorem two_le_card_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) : 2 ≤ (newClade f k).card := by
  have hA : (fiberOf (chainMap n f (k : ℕ)) (f k).1).Nonempty := ⟨_, mem_fiberOf.mpr (hf.1 k).1⟩
  have hB : (fiberOf (chainMap n f (k : ℕ)) (f k).2).Nonempty := ⟨_, mem_fiberOf.mpr (hf.1 k).2.1⟩
  have hcard : (newClade f k).card
      = (fiberOf (chainMap n f (k : ℕ)) (f k).1).card
        + (fiberOf (chainMap n f (k : ℕ)) (f k).2).card := by
    rw [newClade]
    exact Finset.card_union_of_disjoint (disjoint_newClade_fibers hf k)
  have h1 : 1 ≤ (fiberOf (chainMap n f (k : ℕ)) (f k).1).card := Finset.card_pos.mpr hA
  have h2 : 1 ≤ (fiberOf (chainMap n f (k : ℕ)) (f k).2).card := Finset.card_pos.mpr hB
  omega

/-- 新块是**非单点 clade**。 -/
theorem mem_filter_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) (k : Fin (n - 1)) :
    newClade f k ∈ (cladesOf n f).filter (fun C => 2 ≤ C.card) :=
  Finset.mem_filter.mpr ⟨mem_cladesOf_newClade hf k, two_le_card_newClade hf k⟩

/-- ★★★ **不同步创建的新块不同**：`k ↦ newClade f k` 是**单射**。 -/
theorem newClade_injective {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) : Function.Injective (fun k : Fin (n - 1) => newClade f k) := by
  intro k k' hkk'
  have hkk : newClade f k = newClade f k' := hkk'
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : newClade f k ∈ upto f (k' : ℕ) :=
      mem_upto_of_le (L := (k' : ℕ)) (j := (k : ℕ) + 1) (by omega)
        (mem_blocksOf_newClade hf k)
    rw [hkk] at hmem
    exact not_mem_upto_newClade hf k' hmem
  · have hmem : newClade f k' ∈ upto f (k : ℕ) :=
      mem_upto_of_le (L := (k : ℕ)) (j := (k' : ℕ) + 1) (by omega)
        (mem_blocksOf_newClade hf k')
    rw [← hkk] at hmem
    exact not_mem_upto_newClade hf k hmem

/-- ★★★★ **(O1) 满射性**：第 `k` 步创建出的新块**恰枚举全部非单点 clade**。 -/
theorem image_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) :
    (Finset.univ.image (fun k : Fin (n - 1) => newClade f k))
      = (cladesOf n f).filter (fun C => 2 ≤ C.card) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro C hC
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hC
    exact mem_filter_newClade hf k
  · rw [Finset.card_image_of_injective _ (newClade_injective hf), Finset.card_univ,
      Fintype.card_fin, card_filter_nonsingleton_cladesOf hf]

/-- ★★★★ **(O1) 每个非单点 clade 恰是某一步创建出的新块**（唯一性 ⇒ 创建块的标号唯一）。
这是 §14.3 `existsUnique_creation_level`（「由 `f` 定 `k`」）的**逆方向**。 -/
theorem existsUnique_newClade {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {C : Finset (Fin n)} (hC : C ∈ cladesOf n f)
    (h2 : 2 ≤ C.card) : ∃! k : Fin (n - 1), newClade f k = C := by
  have hmem : C ∈ Finset.univ.image (fun k : Fin (n - 1) => newClade f k) := by
    rw [image_newClade hf]
    exact Finset.mem_filter.mpr ⟨hC, h2⟩
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
  exact ⟨k, hk, fun k' hk' => newClade_injective hf (hk'.trans hk.symm)⟩

/-! ### §14.6 ★★★ `children_cover` —— 非单点 clade 是**孩子之并**（(O1) 的**入口引理**）

§14.4–§14.5 把 (O1)「纤维 ↔ 合法创建序」的两端接上了（重建映射 ＋ 创建块满射）。
(O1) 本体（「合法创建序 ⟺ 线性扩展」）还缺一条**入口事实**：

> 要建出非单点 clade `C`，**必须先把它的两个孩子建出来** ——
> `C` 的**前驱集合恰是孩子之并**，而不是「`C` 的全部真子簇」。

即集合等式 `C = ⋃_{B ∈ children (cladesOf n f) C} B`。它是 §15 的 `LinExt`
（线性扩展只数 `internalBelow`）与 §14.4 的 `reconstruct`（读创建序）之间的桥：
没有它，「`C` 的前驱只有两个孩子」这一步就无法从 `children` 的定义里取出。

证明只有一行实质内容：`existsUnique_newClade` 把 `C` 认成某一步的新块 `newClade f k`，
`children_newClade` 又把该新块的孩子算成第 `k` 步被合并的两块 `A`、`B`，
而 `newClade f k = A ∪ B` **就是定义** —— 于是等式成立。 -/

/-- ★★★ **`children_cover`**（(O1) 入口）：非单点 clade 等于其（极大真子）孩子之并。 -/
theorem children_cover {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {C : Finset (Fin n)} (hC : C ∈ cladesOf n f)
    (h2 : 2 ≤ C.card) :
    C = (children (cladesOf n f) C).biUnion id := by
  obtain ⟨k, hk, -⟩ := existsUnique_newClade hf hC h2
  rw [← hk, children_newClade hf k]
  ext z
  simp [newClade]

/-! ### §14.7 ★★★ 创建序是**线性扩展**（(O1) 的「⟹」半）

§14.4–§14.6 把「合并史 ↔ (clade 集, 创建块)」两端接上并给出了**入口**。本小节证它的「⟹」方向，即

> 合并史的创建顺序 `k ↦ newClade f k` 是非单点 clade 在**严格包含序**
> `⊂` 下的一个**线性扩展**：`C ⊂ D ⟹ 创建步(C) < 创建步(D)`。

（反方向「线性扩展 ⟹ 合法创建序」本次**未**做，见本节末尾的诚实边界。）

**证明路线**：对 `k'` 做**强归纳**。
`C ⊂ D` 且 `children D = {A, B}`（`children_newClade`）⇒ `C ⊆ A ∪ B`，
故 `C` 与某个孩子 `E ∈ {A, B}` 相交；橡嵌性（`laminarFamily_cladesOf`）给出
`C ⊆ E` 或 `E ⊆ C`：

* `C ⊆ E` 且 `C = E`：`E` 是 `k'` 层的块、`C` 的创建步为 `k`
  ⇒ `newClade_lt_of_mem_blocksOf` 直接给 `k < k'`；
* `C ⊂ E`：`E` 也是新块 `newClade f j`（`existsUnique_newClade`）且 `j < k'`（同上），
  强归纳假设给 `k < j`，故 `k < j < k'`；
* `E ⊂ C`：`E` 是 `D` 的**极大**真子簇，`E ⊂ C ⊂ D` 与极大性矛盾（`children_maximal`）；
* `Disjoint C E`：与 `C 与 E` 相交矛盾。

卡点只在一处：「`E` 是更小的新块 ⇒ 它的创建步 `< k'`」—— 它靠
`newClade f j ∈ blocksOf (chainMap k') ⇒ j < k'`，后者又靠 `not_mem_upto_newClade`
（新块不在更低层出现）与 `upto` 的单调性。

⚠️ 本条**只**交付 (O1) 双射的「⟹」半，**不**声称已证 `rankedFiberCount_gap`：
后者是 SD2012 的 **Remark 6**，而 Remark 6 本身是**转引** —— 该文正文明写
"A proof can be found in [26]"，[26] = Semple & Steel, *Phylogenetics*（Oxford），**该书不在库**。 -/

/-- ★★★ **新块在更晚层仍是块 ⇒ 它的创建步更早**（§14.7 的关键引理）。 -/
theorem newClade_lt_of_mem_blocksOf {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {k : Fin (n - 1)} {L : ℕ}
    (h : newClade f k ∈ blocksOf n (chainMap n f L)) : (k : ℕ) < L := by
  by_contra hcon
  have hLk : L ≤ (k : ℕ) := by omega
  exact not_mem_upto_newClade hf k (upto_subset f hLk (mem_upto_of_le (le_refl L) h))

/-- ★★★ **(O1) 的「⟹」半：创建序是严格包含序的线性扩展**（§14.7）。 -/
theorem newClade_ssubset_imp_lt {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {k k' : Fin (n - 1)}
    (hsub : newClade f k ⊂ newClade f k') : (k : ℕ) < (k' : ℕ) := by
  refine Nat.strongRecOn (k' : ℕ)
    (motive := fun m => ∀ (k k' : Fin (n - 1)), (k' : ℕ) = m →
      newClade f k ⊂ newClade f k' → (k : ℕ) < (k' : ℕ)) ?_ k k' rfl hsub
  intro m ih k k' hk'm hsub
  have hCcl : newClade f k ∈ cladesOf n f := mem_cladesOf_newClade hf k
  have hC2 : 2 ≤ (newClade f k).card := two_le_card_newClade hf k
  have hCD : newClade f k ⊆ newClade f k' := hsub.1
  obtain ⟨z, hzC⟩ := Finset.card_pos.mp (by omega : 0 < (newClade f k).card)
  have hzD : z ∈ newClade f k' := hCD hzC
  have key : ∀ (E : Finset (Fin n)), E ∈ blocksOf n (chainMap n f (k' : ℕ)) →
      E ∈ children (cladesOf n f) (newClade f k') → z ∈ E → (k : ℕ) < (k' : ℕ) := by
    intro E hEblk hEch hzE
    have hEcl : E ∈ cladesOf n f := children_mem hEch
    rcases laminarFamily_cladesOf f (newClade f k) hCcl E hEcl with h1 | h1 | h1
    · by_cases hEC : E = newClade f k
      · rw [hEC] at hEblk
        exact newClade_lt_of_mem_blocksOf hf hEblk
      · have hE2 : 2 ≤ E.card := le_trans hC2 (Finset.card_le_card h1)
        obtain ⟨j, hEj, -⟩ := existsUnique_newClade hf hEcl hE2
        have hjlt : (j : ℕ) < (k' : ℕ) :=
          newClade_lt_of_mem_blocksOf hf (k := j) (L := (k' : ℕ)) (by rw [hEj]; exact hEblk)
        have hss : newClade f k ⊂ newClade f j := by
          rw [hEj]
          exact Finset.ssubset_iff_subset_ne.mpr ⟨h1, fun hh => hEC hh.symm⟩
        have hkj : (k : ℕ) < (j : ℕ) := ih (j : ℕ) (by omega) k j rfl hss
        omega
    · by_cases hEC : E = newClade f k
      · rw [hEC] at hEblk
        exact newClade_lt_of_mem_blocksOf hf hEblk
      · exact absurd hsub (children_maximal hEch hCcl
          (Finset.ssubset_iff_subset_ne.mpr ⟨h1, hEC⟩))
    · exact absurd hzE (Finset.disjoint_left.mp h1 hzC)
  rw [newClade] at hzD
  rcases Finset.mem_union.mp hzD with hz | hz
  · refine key (fiberOf (chainMap n f (k' : ℕ)) (f k').1) ?_ ?_ hz
    · exact fiberOf_mem_blocksOf_of_nonempty ⟨(f k').1, mem_fiberOf.mpr (hf.1 k').1⟩
    · rw [children_newClade hf k']; simp
  · refine key (fiberOf (chainMap n f (k' : ℕ)) (f k').2) ?_ ?_ hz
    · exact fiberOf_mem_blocksOf_of_nonempty ⟨(f k').2, mem_fiberOf.mpr (hf.1 k').2.1⟩
    · rw [children_newClade hf k']; simp

/-- ★★ **§14.7 的 `LinExt` 形式**：创建序满足 §15 `LinExt` 定义里的
“下标越大者越大”条件（`i < j ⇒ ─ (newClade f j ⊂ newClade f i)`）。

它是把 `newClade_ssubset_imp_lt` 转成反面说法：若 `newClade f j` 真包含于
`newClade f i` 且 `i < j`，则它们的创建步应该 `j < i`，矛盾。 -/
theorem newClade_not_ssubset_of_lt {n : ℕ} {f : Fin (n - 1) → Fin n × Fin n}
    (hf : IsMergeHistory n f) {i j : Fin (n - 1)} (hij : i < j) :
    ¬ (newClade f j ⊂ newClade f i) := by
  intro h
  have h1 : (j : ℕ) < (i : ℕ) := newClade_ssubset_imp_lt hf h
  have h2 : (i : ℕ) < (j : ℕ) := hij
  omega



/-! ### §15 ★★★ 线性扩展数 `LinExt` —— (O1) 计数一侧的**具名器材**

§14.5 末尾把 (O1) 的剩余内容精确成两件。本小节补上第 2 件的**语义对象**：
簇偏序 `(internalBelow T C, ⊊)` 的**线性扩展数**（= 合法创建序的个数）。

背景（§8 已记录的三次 `grep`）：Mathlib **没有**线性扩展的**计数** ——
`Mathlib/Order/Extension/Linear.lean` 只有 `LinearExtension` 类型别名与存在性
`extend_partialOrder`。故这里**自造**，且刻意不写 `Fintype.card (LinearExtension _)`
（那要走子类型上的 `PartialOrder` 实例，内核不化），而用「**下标枚举 ＋ 过滤**」，
使 `LinExt` 是**可计算**的 `def`（`decide` 能直接算出具体值，见 §15.1）。

⬜ **仍未做（本节的诚实边界）**：**交错引理**
`LinExt T C = multinomial(hook 孩子) · ∏ LinExt 孩子` —— 即 §8 `LE_eq` 的语义版
（孩子子树的线性扩展在**块间插空**的洗牌双射）。本节**没有**给出它，
故「`LinExt = LE`」**仍开着**，§15.1 只给 `n = 4` 的数值对照。 -/

/-- **`C` 之下内部结点偏序的线性扩展数**。

`internalBelow T C` = `T` 中非单点且 `⊆ C` 的簇（含 `C` 自己，当 `2 ≤ |C|` 时），
元素个数恰为 `hook T C`。一个**线性扩展**就是一个枚举
`σ : Fin (hook T C) → internalBelow T C` —— 因 `hook T C` 恰是元素数，
「单射」即「双射」—— 并且**下标越大者越大**：
`i < j ⇒ σ i` 不是 `σ j` 的真子集，即 `¬ ((σ j).1 ⊂ (σ i).1)`。

这正是 §14.5 所缺的「合法创建序的个数」：§14.4 的 `reconstruct` 把创建序读成合并史，
本定义数的是**候选创建序**。 -/
def LinExt (T : Finset (Finset α)) (C : Finset α) : ℕ :=
  (Finset.univ.filter fun σ : Fin (hook T C) → {D // D ∈ internalBelow T C} =>
      (∀ i j : Fin (hook T C), i ≠ j → σ i ≠ σ j) ∧
      (∀ i j : Fin (hook T C), i < j → ¬ (σ j).1 ⊂ (σ i).1)).card

/-- 钩长为 `0`（`C` 不是 `T` 中的非单点簇）时内部结点偏序**空**，线性扩展恰 `1` 个
（唯一的空枚举）。与 §8 的 `LE_eq_one_of_card_le_one` 同值 —— 但这里走的是**计数**定义。 -/
theorem LinExt_eq_one_of_hook_eq_zero {T : Finset (Finset α)} {C : Finset α}
    (h : hook T C = 0) : LinExt T C = 1 := by
  rw [LinExt, h]
  simp

/-! #### §15.1 取值锚点：`n = 4` 的两棵拓扑（与 §10.1 的 `LE` 及既有纤维数三向对上）

| 拓扑 | `internalBelow` | `hook univ` | `LE univ`（§10.1） | 纤维（既有） | **`LinExt univ`（本节）** |
|---|---|---|---|---|---|
| caterpillar `Tcat` | `{0,1} ⊊ {0,1,2} ⊊ univ`（全序） | `3` | `1` | `1` | **`1`** |
| balanced `Tbal` | `{0,1}`、`{2,3}` 互不可比，均 `⊊ univ` | `3` | `2` | `2` | **`2`** |

⚠️ 这只是 `n = 4` 的**数值**对照（`decide` 穷举 `3^3 = 27` 个枚举），
**不是**一般 `n` 的 `LinExt = LE`（那需要上面的交错引理）。 -/

-- caterpillar：内部结点偏序是全序 ⇒ 唯一线性扩展
example : LinExt Tcat (Finset.univ : Finset (Fin 4)) = 1 := by decide

-- balanced：两个孩子可互换 ⇒ 两个线性扩展
example : LinExt Tbal (Finset.univ : Finset (Fin 4)) = 2 := by decide

end Phylo.Stat.HookLength
