/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SupertreeLimits
import Phylo.InternalEdge

/-!
# `Phylo.CladogramBuild` —— 「造具体 `Cladogram`」的器材（**W21 任务 A / C1**）

## 0. 派单与动机

W21 派单（`/lean/DISPATCH.md`）把本批定为「**补器材**」，理由是 W20 收档时的结论：
「库内**造不出**一棵具体的 `Cladogram`，`B-1` 与 `B-5` 的前置是**同一件**缺件」。

## 1. ★D 更正（W21 逐条实核）：该卡点**只对了一半**

按派单 §2.4 的授权（「若你回核出我的判断有误，直接更正并写明」），此处更正。
**本库其实已有**下列器材（W20 的「穷尽搜索」只搜了 `Cladogram` 的**实例／结构字面量**，
把真正可用的**存在性定理**与**具体 `Split` 字面量**两条路都漏掉了）：

| # | 器材 | 位置 | 作用 |
|---|---|---|---|
| 1 | `Phylo.splitOf` / `Phylo.toCladogram` | `Laminar.lean:1538` / `:1104` | 由**镶嵌 clade 集**显式建树（含全部证明项） |
| 2 | `exists_cladogram_of_compatible` | `Supertree.lean:310` | 相容 split 族 ⟹ 存在 cladogram **定向展示**全体（＋边侧刻画） |
| 3 | ★ `isSplitOf_iff_mem_or_trivial` | `ConsensusExtra.lean:222` | 同 2 的 **`↔` 加强版**：split 系统**恰为**「族 ∪ 平凡 split」 |
| 4 | ★ `SBD.exists_exact_tree_P1` / `…_P2` | `SupertreeLimits.lean:938` 一线 | B-5 的 `P₁`/`P₂` **精确树**（已给出） |
| 5 | ★ `SBD.sP1a`…`sP1c` · `SBD.famP1` · `SBD.famP1_compatible` 等 | `SupertreeLimits.lean:819-935` | **具体 `Split (Fin 6)` 字面量**（`splitOf` ＋ `by decide` 收尾） |
| 6 | ★ `SBD.two_parent_trees_conjuncts_1_2_3` | `SupertreeLimits.lean:1102` | B-5 缺口第 **1–3 条已证** ✓ |

⇒ **真正的缺口**不是「造不出树」，而是：

* **(a)** 器材 2/3 是**存在性**形态，下游每次都要 `obtain` 一次、**无法命名**一棵树；
  且**没有**「拿到 split 族就知道这棵树**全部** split」的一句话接口；
* **(b)** 没有在 `Fin 5` 上的**用例**（B-1 需要 `Cladogram (Fin 5)`）；
* **(c)** 器材 3 的刻画里「平凡」那一支是**内联析取式**，
  没有谓词形态，也没有「**非平凡** split 系统恰为族」的推论。

本文件补 (a)(b)(c) 三件。**B-1 的另一半**（多状态展示判据 = `DisplaysMultiState` 的存在性）
不在本文件，属 W21 任务 B / C2。

## 2. 本文件交付的器材表

| 器材 | 形态 | 服务的目标 |
|---|---|---|
| `Split.IsTrivial` | 谓词（「平凡 split」= 有一侧是单点集） | (c) |
| `Split.isTrivial_iff_card` / `Split.not_isTrivial_iff` | 桥：「平凡 ⟺ 某侧基数 1」／「非平凡 ⟺ 两侧 `≥ 2`」 | (c) |
| `Cladogram.ofCompatibleSplits` | ★ **通用构造器**（`def`，非纯存在性） | (a) |
| `Cladogram.isSplitOf_ofCompatibleSplits` | ★ **刻画引理**：`IsSplitOf s ↔ (s ∈ fam ∨ 平凡)` | (a) |
| `Cladogram.isSplitOf_ofCompatibleSplits_of_notTrivial` | 非平凡时**恰为** `s ∈ fam` | (a)(c) |
| `Cladogram.nontrivialSplits` | 树的**非平凡 split 系统**（`Finset`，可计数） | (a) |
| `Cladogram.nontrivialSplits_ofCompatibleSplits_eq` | ★ 非平凡 split 系统**恰为族本身** | (a)(c) |
| `compatible_swapClosure` / `nontrivial_swapClosure` / `swapClosure_swap_closed` | 把「族 + 换向」的**三条前提**自动化（消去库内重复的 4 分支证明） | (a) |
| `Cladogram.treeP1` / `treeP2` ＋ `treeP1_nontrivialSplits` ＋ `treeP1_nontrivialSplits_card` | **用例 1**：把 B-5 的 `P₁`/`P₂` 树**命名化**并**算出**其 split 系统 | (b) ＋ B-5/C3 |
| `Cat5.catTree5` ＋ `catTree5_nontrivialSplits_card` | **用例 2**：`Fin 5` 上造一棵 caterpillar 并**算出**其 split 系统 | (b) ＋ B-1 |

## 3. 纪律

* **零 `sorry` / 零 `axiom`**（建造器材不得引入缺口）；
* **不把「造树」偷换成「假设给了一棵树」**：`ofCompatibleSplits` 的假设
  **只有**「族的相容性／非平凡性／换向封闭／`3 ≤ |X|`」，**没有**任何「已给一棵树」的输入；
* 复用的既有器材（器材 2/3/4/5/6）**一字不动** ✓。
-/

universe u

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **平凡 split**（本文件口径）：有一侧是**单点集**。

⚠️ 与库内另两处的**关系**（同名不同址，本文件**不**改它们）：
* `IsTrivialSplit`（`Phylo/Stat/SplitProbabilities.lean:149`）—— 口径是**基数**
  （`sideA.card = 1 ∨ sideB.card = 1`），`Split.isTrivial_iff_card` 证明两者**等价**；
* `trivialSplitSet`（`Phylo/Algorithm/NeighborNet.lean:1187`）—— 同义谓词的 `Finset` 形态。

此处另立谓词的原因是：本文件处在 `Stat/` 与 `Algorithm/` **之下**（依赖方向不许倒转），
且 `Fin 5`/`Fin 6` 上的 `decide` 用例需要**可归约**的形态（故用 `abbrev`）。 -/
abbrev IsTrivial (s : Split α) : Prop :=
  (∃ x : α, s.sideA = {x}) ∨ (∃ x : α, s.sideA = {x}ᶜ)

/-- 桥：**平凡 ⟺ 某一侧的基数为 `1`**（与 `IsTrivialSplit` 同义）。 -/
theorem isTrivial_iff_card (s : Split α) :
    s.IsTrivial ↔ s.sideA.card = 1 ∨ s.sideB.card = 1 := by
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl (by rw [hx, Finset.card_singleton])
    · exact Or.inr (by rw [Split.sideB_eq_compl, hx, compl_compl]; exact Finset.card_singleton x)
  · rintro (h | h)
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
      exact Or.inl ⟨x, hx⟩
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
      exact Or.inr ⟨x, by rw [← hx, Split.sideB_eq_compl, compl_compl]⟩

/-- 桥（否定形态，下游最常用的形态）：**非平凡 ⟺ 两侧基数都 `≥ 2`**。 -/
theorem not_isTrivial_iff (s : Split α) :
    ¬ s.IsTrivial ↔ 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  have hA : 1 ≤ s.sideA.card := Finset.card_pos.mpr (s.nonempty 0)
  have hB : 1 ≤ s.sideB.card := Finset.card_pos.mpr (s.nonempty 1)
  rw [isTrivial_iff_card]
  constructor <;> intro h <;> omega

end Split

/-! ## 4. 「族 ＋ 换向」的三条前提自动化

库内 `famP1_*` / `famP2_*`（`SupertreeLimits.lean:831-935`）把这三条各写了一遍
（每条 4 分支）；此处**一般化**成一条引理，避免第三个族再抄一遍。 -/

section SwapClosure

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- ★★ **「族 ＋ 换向」保持两两相容**（`h` = 族本身两两相容）。 -/
theorem compatible_swapClosure {F : Finset (Split α)}
    (h : ∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t) :
    ∀ s ∈ F ∪ F.image (fun s => s.swap), ∀ t ∈ F ∪ F.image (fun s => s.swap),
      Split.Compatible s t := by
  have hR (s t : Split α) : s.Compatible t ↔ s.Compatible t.swap := by
    rw [Split.Compatible, Split.Compatible]
    simp only [Finset.disjoint_iff_inter_eq_empty, Split.swap_sideA, Split.swap_sideB]
    tauto
  have hL (s t : Split α) : s.Compatible t ↔ s.swap.Compatible t := by
    rw [Split.Compatible, Split.Compatible]
    simp only [Finset.disjoint_iff_inter_eq_empty, Split.swap_sideA, Split.swap_sideB]
    tauto
  intro s hs t ht
  rcases Finset.mem_union.mp hs with h1 | h1 <;> rcases Finset.mem_union.mp ht with h2 | h2
  · exact h s h1 t h2
  · obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact (hR s t').mp (h s h1 t' ht')
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    exact (hL s' t).mp (h s' hs' t h2)
  · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp h2
    exact (hR s'.swap t').mp ((hL s' t').mp (h s' hs' t' ht'))

/-- ★★ **「族 ＋ 换向」保持非平凡**（换向只对调两侧）。 -/
theorem nontrivial_swapClosure {F : Finset (Split α)}
    (h : ∀ s ∈ F, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) :
    ∀ s ∈ F ∪ F.image (fun s => s.swap), 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  rcases Finset.mem_union.mp hs with h1 | h1
  · exact h s h1
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨h1', h2'⟩ := h t ht
    rw [Split.swap_sideA, Split.swap_sideB]
    exact ⟨h2', h1'⟩

/-- ★★ **「族 ＋ 换向」是 `swap`-封闭的**（这正是器材 3 所要求的 `hswap`）。 -/
theorem swapClosure_swap_closed (F : Finset (Split α)) :
    ∀ s ∈ F ∪ F.image (fun s => s.swap), s.swap ∈ F ∪ F.image (fun s => s.swap) := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨s, h, rfl⟩))
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    rw [Split.swap_swap]
    exact Finset.mem_union.mpr (Or.inl ht)

end SwapClosure

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 5. ★★★ 通用构造器 -/

/-- ★★★ **通用构造器**：由「相容 ＋ 非平凡 ＋ `swap`-封闭」的 split 族造出一棵 `Cladogram X`。

**这是器材 `isSplitOf_iff_mem_or_trivial`（`ConsensusExtra.lean:222`）的 `def` 化** ——
把「存在一棵树」变成**可命名的一棵树**，使下游不必每次 `obtain`，
并且配一条**一句话**的刻画（`isSplitOf_ofCompatibleSplits`）。

⚠️ 假设面**只有**下列四条，**没有**「已给一棵树」这类输入：

* `hcomp` —— 族**两两相容**；
* `hnt` —— 族成员**非平凡**（两侧各 `≥ 2`）；
* `hswap` —— 族对**换向**封闭（`s.swap ∈ fam`）；
* `h3` —— `3 ≤ |X|`（`toCladogram` 的根非退化条件）。

★ 之所以只需 `hswap`：器材 3 的刻画以 `sideA` **定向**书写，族若不封闭于换向，
树会**多**出若干换向 split。取 `fam := base ∪ base.image swap`
（`compatible_swapClosure` ＋ `nontrivial_swapClosure` ＋ `swapClosure_swap_closed` 自动补齐三条前提）。

**构造**：`isSplitOf_iff_mem_or_trivial` 的 `Classical.choose`（底层是
`normFinset` 规范簇族 ＋ `Phylo.toCladogram` 的**显式**建树）。 -/
noncomputable def ofCompatibleSplits (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3 : 3 ≤ Fintype.card X) : Cladogram.{u, u} X :=
  (isSplitOf_iff_mem_or_trivial fam ρ hcomp hnt hswap h3).choose

/-- ★★★ **刻画引理（本器材的核心产出）**：`ofCompatibleSplits` 造出的树，
其 split 系统**恰为**「族 ∪ 平凡 split」——

    `T.IsSplitOf s ↔ s ∈ fam ∨ (∃ x, s.sideA = {x}) ∨ (∃ x, s.sideA = {x}ᶜ)`

⇒ 「造了这棵树」＝「**完全知道**它的 split 系统」，而非只是「存在一棵树展示了族」。 -/
theorem isSplitOf_ofCompatibleSplits (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3 : 3 ≤ Fintype.card X) (s : Split X) :
    (ofCompatibleSplits fam ρ hcomp hnt hswap h3).IsSplitOf s ↔
      s ∈ fam ∨ (∃ x : X, s.sideA = {x}) ∨ (∃ x : X, s.sideA = {x}ᶜ) :=
  (isSplitOf_iff_mem_or_trivial fam ρ hcomp hnt hswap h3).choose_spec s

/-- ★★ **非平凡时恰为族**：若 `s` 非平凡，则刻画里的「平凡」两支消失 ⇒ `IsSplitOf s ↔ s ∈ fam`。 -/
theorem isSplitOf_ofCompatibleSplits_of_notTrivial (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3 : 3 ≤ Fintype.card X) {s : Split X}
    (hs : ¬ s.IsTrivial) :
    (ofCompatibleSplits fam ρ hcomp hnt hswap h3).IsSplitOf s ↔ s ∈ fam := by
  rw [isSplitOf_ofCompatibleSplits fam ρ hcomp hnt hswap h3 s]
  exact ⟨fun h => h.elim id (fun h' => absurd h' hs), fun h => Or.inl h⟩

/-! ## 6. 非平凡 split 系统 -/

/-- 树 `T` 的**非平凡 split 系统**（有向形态：每条无向 split 的两个朝向都算）。

⚠️ 与 `Cladogram.splits`（`Split.lean:625` 一线，`Set (Split X)` 的**全部** split）不同：
这里**滤掉平凡 split**（叶边），并把结果收成 `Finset` 以便**计数**。 -/
noncomputable def nontrivialSplits (T : Cladogram X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s => T.IsSplitOf s ∧ ¬ s.IsTrivial

/-- ★★ **非平凡 split 系统恰为族本身**（族成员已非平凡）：这是「算出这棵树的 split 系统」
的最强形态 —— 右端是**闭式** `Finset`（无自由 `∀ s`），故下游常可 `decide`／`rw`。 -/
theorem nontrivialSplits_ofCompatibleSplits_eq (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam) (h3 : 3 ≤ Fintype.card X) :
    (ofCompatibleSplits fam ρ hcomp hnt hswap h3).nontrivialSplits = fam := by
  classical
  ext s
  rw [nontrivialSplits, Finset.mem_filter]
  rw [isSplitOf_ofCompatibleSplits fam ρ hcomp hnt hswap h3 s]
  constructor
  · rintro ⟨-, h, hn⟩
    exact h.elim id (fun h' => absurd h' hn)
  · intro h
    exact ⟨Finset.mem_univ _, Or.inl h, (Split.not_isTrivial_iff s).mpr (hnt s h)⟩

/-! ## 7. 用例 1（服务 B-5 / C3）：把 `P₁`、`P₂` 的树**命名化**并**算出** split 系统 -/

/-- ★★ **`P₁` 的树**（B-5 原文 `{{0,1}|rest, {0,1,2,3}|{4,5}, {0,1,4,5}|{2,3}}`）。

库内原本只有**存在性**形态 `SBD.exists_exact_tree_P1`；此处给出**可命名**的 `def`。 -/
noncomputable def treeP1 : Cladogram.{0, 0} (Fin 6) :=
  ofCompatibleSplits SBD.famP1 0 SBD.famP1_compatible SBD.famP1_nontrivial
    SBD.famP1_swap_closed (by decide)

/-- ★★ **`P₂` 的树**（B-5 原文 `σ(P₁)`）。 -/
noncomputable def treeP2 : Cladogram.{0, 0} (Fin 6) :=
  ofCompatibleSplits SBD.famP2 0 SBD.famP2_compatible SBD.famP2_nontrivial
    SBD.famP2_swap_closed (by decide)

/-- 用例 1a：`treeP1` 的 split 系统**被完全刻画**（`↔`，非只是「展示了 `P₁`」）。 -/
theorem treeP1_isSplitOf (s : Split (Fin 6)) :
    treeP1.IsSplitOf s ↔
      s ∈ SBD.famP1 ∨ (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ) :=
  isSplitOf_ofCompatibleSplits SBD.famP1 0 SBD.famP1_compatible SBD.famP1_nontrivial
    SBD.famP1_swap_closed (by decide) s

/-- 用例 1b：`treeP2` 的 split 系统**被完全刻画**。 -/
theorem treeP2_isSplitOf (s : Split (Fin 6)) :
    treeP2.IsSplitOf s ↔
      s ∈ SBD.famP2 ∨ (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ) :=
  isSplitOf_ofCompatibleSplits SBD.famP2 0 SBD.famP2_compatible SBD.famP2_nontrivial
    SBD.famP2_swap_closed (by decide) s

/-- ★★ **用例 1c（「算出其 split 系统」）**：`treeP1` 的**非平凡** split 系统**恰为** `SBD.famP1`。 -/
theorem treeP1_nontrivialSplits : treeP1.nontrivialSplits = SBD.famP1 := by
  simp only [treeP1]
  exact nontrivialSplits_ofCompatibleSplits_eq SBD.famP1 0 SBD.famP1_compatible
    SBD.famP1_nontrivial SBD.famP1_swap_closed (by decide)

/-- ★★ **用例 1d（计数）**：`treeP1` 的非平凡 split 数 = **6**。
`6 = 3 × 2` —— 6 taxa 上二叉树的 `n − 3 = 3` 条**无向** split，每条两个朝向
（`SBD.famP1` 已含换向，故有向计数翻倍）。 -/
theorem treeP1_nontrivialSplits_card : treeP1.nontrivialSplits.card = 6 := by
  rw [treeP1_nontrivialSplits]
  decide

/-- ★★ **用例 1e**：`treeP2` 的非平凡 split 系统**恰为** `SBD.famP2`。 -/
theorem treeP2_nontrivialSplits : treeP2.nontrivialSplits = SBD.famP2 := by
  simp only [treeP2]
  exact nontrivialSplits_ofCompatibleSplits_eq SBD.famP2 0 SBD.famP2_compatible
    SBD.famP2_nontrivial SBD.famP2_swap_closed (by decide)

/-- ★★ **用例 1f（计数）**：`treeP2` 的非平凡 split 数 = **6**（同上，`3 × 2`）。 -/
theorem treeP2_nontrivialSplits_card : treeP2.nontrivialSplits.card = 6 := by
  rw [treeP2_nontrivialSplits]
  decide

end Cladogram

/-! ## 8. 用例 2（服务 B-1）：`Fin 5` 上造一棵 caterpillar 并算出其 split 系统 -/

namespace Cat5

/-- `Fin 5` 上 caterpillar 的 clade `{0,1}` 对应的 split `{0,1} | {2,3,4}`。 -/
noncomputable abbrev sCat5a : Split (Fin 5) :=
  Phylo.splitOf ({0, 1} : Finset (Fin 5)) (by decide) (by decide)

/-- `Fin 5` 上 caterpillar 的 clade `{0,1,2}` 对应的 split `{0,1,2} | {3,4}`。 -/
noncomputable abbrev sCat5b : Split (Fin 5) :=
  Phylo.splitOf ({0, 1, 2} : Finset (Fin 5)) (by decide) (by decide)

/-- caterpillar 的基族（两条**无向** split 的一个朝向）。 -/
noncomputable abbrev catBase5 : Finset (Split (Fin 5)) := {sCat5a, sCat5b}

/-- caterpillar 的族（补上换向 ⇒ 满足 `hswap`）。 -/
noncomputable abbrev catFam5 : Finset (Split (Fin 5)) :=
  catBase5 ∪ catBase5.image (fun s => s.swap)

/-- `splitOf` 相容性的集合形态（`Fin 5` 版；与 `SBD.splitOf_compatible_iff` 同构）。 -/
theorem splitOf_compatible_iff_five {A B : Finset (Fin 5)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hB : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    (Phylo.splitOf A hA hAc).Compatible (Phylo.splitOf B hB hBc) ↔
      (A ∩ B = ∅ ∨ A ∩ Bᶜ = ∅ ∨ Aᶜ ∩ B = ∅ ∨ Aᶜ ∩ Bᶜ = ∅) := by
  rw [Split.Compatible]
  simp only [Phylo.splitOf_sideA, Phylo.splitOf_sideB, Finset.disjoint_iff_inter_eq_empty]

theorem catBase5_compatible : ∀ s ∈ catBase5, ∀ t ∈ catBase5, Split.Compatible s t := by
  intro s hs t ht
  simp only [catBase5, Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    (rw [splitOf_compatible_iff_five]; decide)

theorem catBase5_nontrivial : ∀ s ∈ catBase5, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  simp only [catBase5, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl <;>
    (simp only [Phylo.splitOf_sideA, Phylo.splitOf_sideB]; decide)

theorem catFam5_compatible : ∀ s ∈ catFam5, ∀ t ∈ catFam5, Split.Compatible s t :=
  compatible_swapClosure catBase5_compatible

theorem catFam5_nontrivial : ∀ s ∈ catFam5, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
  nontrivial_swapClosure catBase5_nontrivial

theorem catFam5_swap_closed : ∀ s ∈ catFam5, s.swap ∈ catFam5 :=
  swapClosure_swap_closed catBase5

/-- ★★ **用例 2a**：`Fin 5` 上的一棵具体 caterpillar 树（拓扑 `((0,1),2),(3,4)`）。 -/
noncomputable def catTree5 : Cladogram.{0, 0} (Fin 5) :=
  Cladogram.ofCompatibleSplits catFam5 0 catFam5_compatible catFam5_nontrivial
    catFam5_swap_closed (by decide)

/-- 用例 2a′：`catTree5` 的 split 系统**被完全刻画**。 -/
theorem catTree5_isSplitOf (s : Split (Fin 5)) :
    catTree5.IsSplitOf s ↔
      s ∈ catFam5 ∨ (∃ x : Fin 5, s.sideA = {x}) ∨ (∃ x : Fin 5, s.sideA = {x}ᶜ) :=
  Cladogram.isSplitOf_ofCompatibleSplits catFam5 0 catFam5_compatible catFam5_nontrivial
    catFam5_swap_closed (by decide) s

/-- ★★ **用例 2b（「算出其 split 系统」）**：`catTree5` 的非平凡 split 系统**恰为** `catFam5`。 -/
theorem catTree5_nontrivialSplits : catTree5.nontrivialSplits = catFam5 := by
  simp only [catTree5]
  exact Cladogram.nontrivialSplits_ofCompatibleSplits_eq catFam5 0 catFam5_compatible
    catFam5_nontrivial catFam5_swap_closed (by decide)

/-- ★★ **用例 2c（计数）**：`catTree5` 的非平凡 split 数 = **4**。
`4 = 2 × 2` —— 5 taxa 上二叉树的 `n − 3 = 2` 条**无向** split，每条两个朝向。 -/
theorem catTree5_nontrivialSplits_card : catTree5.nontrivialSplits.card = 4 := by
  rw [catTree5_nontrivialSplits]
  decide

end Cat5

/-! ## 9. 根叶附着载体 `attachRoot`：`α` 上的**镶嵌族** ↦ `Cladogram (α ⊕ Unit)`

★ **W33 新增**。库内 `Cladogram (X ⊕ Unit)` 处处是**消费者**（`IsClanMinusRoot`、
`rootedToCladogram`、`isClade_rootedToCladogram_iff_of_nonempty` 等 20 余处），
而**生产者一个也没有** —— 于是 `Phylo/Stat/ClanPairLaw.lean` 的 4 条计数陈述
（都对**任意** `U : Ω → Cladogram (Fin N ⊕ Unit)` 陈述）**无法实例化**。
本节补上生产者，并用「`IsClade` 的完全刻画」证明它是**可用的**载体。

* §9.1 `Split.pushInl`：把 `α` 侧的集合 `C` 推成 `α ⊕ Unit` 上的一条 split
  （`C.image Sum.inl` 作 `sideA`，补集 ＋ 根叶 `Sum.inr ()` 作 `sideB`）；
* §9.2 `attachFamily`：由 `L` 中「真、非单点」成员推成的 split 族；
* §9.3 `attachRoot`：`ofCompatibleSplits` 造树 ＋ `isSplitOf_attachRoot`；
* §9.4 `attachRoot_isClade`：`IsClade (A.image inl) ↔ A ∈ L ∨ |A| = 1 ∨ A = univ`。

★ **为什么必须要求镶嵌族**（而不只是「两两相容」）：根叶 `m = Sum.inr ()` 必须落在
**每一条**推上去的 split 的**同一侧**（`sideB`）。若 `C₁, C₂` 只是相容而**互为交叉**
（例 `α = Fin 3`、`C₁ = {1,2}`、`C₂ = {1,3}`：`C₁ ∩ C₂ = {1}`、互不包含），则
`C₁ | C₁ᶜ∪{m}` 与 `C₂ | C₂ᶜ∪{m}` 的四个交**全非空**（`m` 同时落在两个 `sideB` 里）
⇒ 推上去**不再相容**。镶嵌族的成员两两嵌套或相离，这两情形都保住相容性
（嵌套 ⟹ 一侧包含；相离 ⟹ 两侧不交）。 -/

namespace Split

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- **把 `α` 侧集合 `C` 推成 `α ⊕ Unit` 上的 split**：
`C.image Sum.inl` 作 `sideA`，`Cᶜ.image Sum.inl ∪ {根叶}` 作 `sideB`。
（`C` 非空且非全集，故两侧都非空。） -/
noncomputable def pushInl (C : Finset α) (hC : C.Nonempty) (_hCc : Cᶜ.Nonempty) :
    Split (α ⊕ Unit) :=
  Phylo.splitOf (C.image (Sum.inl : α → α ⊕ Unit)) (hC.image Sum.inl) ⟨Sum.inr (), by simp⟩

theorem pushInl_sideA (C : Finset α) (hC : C.Nonempty) (_hCc : Cᶜ.Nonempty) :
    (pushInl C hC _hCc).sideA = C.image (Sum.inl : α → α ⊕ Unit) :=
  Phylo.splitOf_sideA _ _ _

/-- 推上去的集合的补：`(C.image inl)ᶜ = Cᶜ.image inl ∪ {根叶}`。 -/
theorem compl_image_inl (C : Finset α) :
    (C.image (Sum.inl : α → α ⊕ Unit))ᶜ = Cᶜ.image Sum.inl ∪ {Sum.inr ()} := by
  ext x
  cases x with
  | inl y =>
      simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
        Sum.inl.injEq]
      constructor
      · intro hy
        exact Or.inl ⟨y, fun hc => hy ⟨y, hc, rfl⟩, rfl⟩
      · rintro (⟨z, hz, hzy⟩ | h)
        · rintro ⟨w, hw, hwy⟩
          subst hzy
          subst hwy
          exact hz hw
        · exact absurd h (by simp)
  | inr u =>
      cases u
      simp

/-- `pushInl` 的 `sideB`：`α` 侧的补（推上去）＋ 根叶。 -/
theorem pushInl_sideB (C : Finset α) (hC : C.Nonempty) (_hCc : Cᶜ.Nonempty) :
    (pushInl C hC _hCc).sideB = Cᶜ.image (Sum.inl : α → α ⊕ Unit) ∪ {Sum.inr ()} := by
  rw [Split.sideB_eq_compl, pushInl_sideA, compl_image_inl]

end Split

namespace Cladogram

variable {α : Type u} [DecidableEq α]

/-- `C ⊆ D` ⟹ `C.image Sum.inl ⊆ D.image Sum.inl`（`Sum.inl` 单射的集合形态）。 -/
theorem image_inl_subset {C D : Finset α} (h : C ⊆ D) :
    C.image (Sum.inl : α → α ⊕ Unit) ⊆ D.image Sum.inl := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨c, h hc, rfl⟩

/-- `C`、`D` 不交 ⟹ 推上去后仍不交。 -/
theorem disjoint_image_inl {C D : Finset α} (h : Disjoint C D) :
    Disjoint (C.image (Sum.inl : α → α ⊕ Unit)) (D.image Sum.inl) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hy
  rw [Sum.inl.injEq] at hdc
  subst hdc
  exact h hc hd

variable [Fintype α]

/-- ★ **附着族**：`L` 中「真（`≠ univ`）、非单点（基数 `≥ 2`）」的成员推成的 split 族。

三个条件都是**必需的**：`C` 非空 ↔ `sideA` 非空；`C.card ≥ 2` ↔ `sideA` 非平凡；
`C ≠ univ` ↔ `sideB` 含根叶之外还有东西（即 `sideB` 非平凡）。 -/
noncomputable def attachFamily (L : Finset (Finset α)) : Finset (Split (α ⊕ Unit)) := by
  classical
  exact Finset.univ.filter (fun s : Split (α ⊕ Unit) =>
    ∃ C ∈ L, C ≠ Finset.univ ∧ 2 ≤ C.card ∧ s.sideA = C.image (Sum.inl : α → α ⊕ Unit))

/-- `attachFamily` 的成员判定（下游只用这一条）。 -/
theorem mem_attachFamily {L : Finset (Finset α)} {s : Split (α ⊕ Unit)} :
    s ∈ attachFamily L ↔
      ∃ C ∈ L, C ≠ Finset.univ ∧ 2 ≤ C.card ∧
        s.sideA = C.image (Sum.inl : α → α ⊕ Unit) := by
  classical
  simp [attachFamily]

/-- ★★ **附着族两两相容**（镶嵌性在这里被用掉：嵌套 ⟹ 一侧包含；相离 ⟹ 两侧不交）。 -/
theorem attachFamily_compatible {L : Finset (Finset α)} (hlam : LaminarFamily L) :
    ∀ s ∈ attachFamily L, ∀ t ∈ attachFamily L, Split.Compatible s t := by
  intro s hs t ht
  obtain ⟨C, hCL, -, -, hCs⟩ := mem_attachFamily.mp hs
  obtain ⟨D, hDL, -, -, hDt⟩ := mem_attachFamily.mp ht
  rcases hlam C hCL D hDL with h | h | h
  · refine Split.compatible_of_subset_left ?_
    rw [hCs, hDt]
    exact image_inl_subset h
  · refine Split.compatible_of_subset_right ?_
    rw [hCs, hDt]
    exact image_inl_subset h
  · refine Split.compatible_of_disjoint ?_
    rw [hCs, hDt]
    exact disjoint_image_inl h

/-- ★★ **附着族非平凡**：`sideA` 基数 `= C.card ≥ 2`；`sideB` 基数 `= |α| + 1 − C.card ≥ 2`
（由 `C ≠ univ` 得 `C.card < |α|`）。 -/
theorem attachFamily_nontrivial {L : Finset (Finset α)} :
    ∀ s ∈ attachFamily L, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  obtain ⟨C, -, hCne, hC2, hCs⟩ := mem_attachFamily.mp hs
  have hcard : s.sideA.card = C.card := by
    rw [hCs, Finset.card_image_of_injective _ Sum.inl_injective]
  have hlt : C.card < Fintype.card α := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ C, hCne⟩)
  refine ⟨by omega, ?_⟩
  rw [Split.sideB_eq_compl, Finset.card_compl, Fintype.card_sum, Fintype.card_unit, hcard]
  omega

/-- **附着族 ＋ 换向**（`ofCompatibleSplits` 的 `hswap` 要求）。 -/
noncomputable def attachSplitFamily (L : Finset (Finset α)) : Finset (Split (α ⊕ Unit)) :=
  attachFamily L ∪ (attachFamily L).image (fun s => s.swap)

/-- ★★ 换向闭包两两相容（与 `RankedTreeCladogram.splitFamily_compatible` 同构）。 -/
theorem attachSplitFamily_compatible {L : Finset (Finset α)} (hlam : LaminarFamily L) :
    ∀ s ∈ attachSplitFamily L, ∀ t ∈ attachSplitFamily L, Split.Compatible s t :=
  compatible_swapClosure (attachFamily_compatible hlam)

/-- ★★ 换向闭包非平凡。 -/
theorem attachSplitFamily_nontrivial {L : Finset (Finset α)} :
    ∀ s ∈ attachSplitFamily L, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
  nontrivial_swapClosure (attachFamily_nontrivial (L := L))

/-- ★★ 换向闭包对 `swap` 封闭。 -/
theorem attachSplitFamily_swap_closed (L : Finset (Finset α)) :
    ∀ s ∈ attachSplitFamily L, s.swap ∈ attachSplitFamily L :=
  swapClosure_swap_closed (attachFamily L)

/-- ★★★ **根叶附着载体**：由 `α` 上的镶嵌族 `L` 造 `Cladogram (α ⊕ Unit)`。

split 族取 `attachSplitFamily L`（＝ ★ `attachFamily L` 连同换向），三条前提由
★★ `attachSplitFamily_compatible`、★★ `attachSplitFamily_nontrivial`、
★★ `attachSplitFamily_swap_closed` 自动补齐 —— 与 §8 的 `catTree5`、
`RankedTreeCladogram.rankedTreeCladogramOfThree` 是**同一套**构造。 -/
noncomputable def attachRoot (L : Finset (Finset α)) (hlam : LaminarFamily L)
    (h3 : 3 ≤ Fintype.card (α ⊕ Unit)) : Cladogram.{u, u} (α ⊕ Unit) :=
  ofCompatibleSplits (attachSplitFamily L) (Sum.inr ()) (attachSplitFamily_compatible hlam)
    (attachSplitFamily_nontrivial) (attachSplitFamily_swap_closed L) h3

/-- ★★ **`attachRoot` 的 split 系统被完全刻画**：族 ∪ 换向 ∪ 平凡 split。 -/
theorem isSplitOf_attachRoot {L : Finset (Finset α)} (hlam : LaminarFamily L)
    (h3 : 3 ≤ Fintype.card (α ⊕ Unit)) (s : Split (α ⊕ Unit)) :
    (attachRoot L hlam h3).IsSplitOf s ↔
      s ∈ attachSplitFamily L ∨
        (∃ x : α ⊕ Unit, s.sideA = {x}) ∨ (∃ x : α ⊕ Unit, s.sideA = {x}ᶜ) :=
  isSplitOf_ofCompatibleSplits (attachSplitFamily L) (Sum.inr ())
    (attachSplitFamily_compatible hlam) (attachSplitFamily_nontrivial)
    (attachSplitFamily_swap_closed L) h3 s

/-- ★★ **根叶在附着族的每一条 split 的 `sideB`**（「根叶」这个名字的机器内容）。 -/
theorem mem_sideB_attachFamily {L : Finset (Finset α)} {s : Split (α ⊕ Unit)}
    (hs : s ∈ attachFamily L) : Sum.inr () ∈ s.sideB := by
  obtain ⟨C, -, -, -, hCs⟩ := mem_attachFamily.mp hs
  rw [Split.sideB_eq_compl, hCs, Finset.mem_compl]
  simp

/-- ★★★ **`attachRoot` 的 `IsClade` 完全刻画**（本节的**唯一出口**）：

`A.image Sum.inl` 是 `attachRoot L` 的一条边的一侧 **⟺** `A` 是 `L` 的成员，
或 `A` 平凡（`A.card = 1`；`A = univ` 由根叶的悬挂边给出）。

★ 三个平凡支的可计算内容：`A = {x}` ⇒ `A.image Sum.inl = {Sum.inl x}`（单点 split）；
`A = univ` ⇒ `A.image Sum.inl = {Sum.inr ()}ᶜ`（根叶悬挂边的另一侧）。

★ `hne : ∀ C ∈ L, C.Nonempty` 只用来排除 `∅ ∈ L`（否则 `A = ∅` 时左端为假、右端为真）。 -/
theorem attachRoot_isClade {L : Finset (Finset α)} (hlam : LaminarFamily L)
    (hne : ∀ C ∈ L, C.Nonempty) (h3 : 3 ≤ Fintype.card (α ⊕ Unit)) (A : Finset α) :
    (attachRoot L hlam h3).IsClade (A.image (Sum.inl : α → α ⊕ Unit)) ↔
      A ∈ L ∨ A.card = 1 ∨ A = Finset.univ := by
  classical
  constructor
  · -- 正向：把 `IsSplitOf` 的三支逐条化成 `α` 侧断言
    rintro ⟨s, hs, hside⟩
    rcases (isSplitOf_attachRoot hlam h3 s).mp hs with hfam | htriv1 | htriv2
    · rcases Finset.mem_union.mp hfam with hmem | hswap
      · -- 族里：`s.sideA = C.image inl` ⇒ `A = C`
        obtain ⟨C, hCL, -, -, hCs⟩ := mem_attachFamily.mp hmem
        have hAC : A = C := by
          have hEq : A.image (Sum.inl : α → α ⊕ Unit) = C.image Sum.inl := by
            rw [← hside, hCs]
          refine Finset.Subset.antisymm ?_ ?_
          · intro z hz
            have hz' : Sum.inl z ∈ C.image (Sum.inl : α → α ⊕ Unit) := by
              rw [← hEq]
              exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
            obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hz'
            rw [Sum.inl.injEq] at hwe
            subst hwe
            exact hw
          · intro z hz
            have hz' : Sum.inl z ∈ A.image (Sum.inl : α → α ⊕ Unit) := by
              rw [hEq]
              exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
            obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hz'
            rw [Sum.inl.injEq] at hwe
            subst hwe
            exact hw
        exact Or.inl (hAC ▸ hCL)
      · -- 换向支：`sideB` 含根叶，而 `A.image inl` 不含
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hswap
        have hm := mem_sideB_attachFamily ht
        rw [← Split.swap_sideA] at hm
        rw [hside] at hm
        simp at hm
    · -- 平凡支 1：`A.image inl = {x}` ⇒ `A` 单点
      obtain ⟨x, hx⟩ := htriv1
      refine Or.inr (Or.inl ?_)
      have hx' : A.image (Sum.inl : α → α ⊕ Unit) = ({x} : Finset (α ⊕ Unit)) := by
        rw [← hside]; exact hx
      have hxmem : x ∈ A.image (Sum.inl : α → α ⊕ Unit) := by
        rw [hx']; exact Finset.mem_singleton_self x
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxmem
      have hAeq : A = {y} := by
        ext z
        constructor
        · intro hz
          have hzin : Sum.inl z ∈ ({x} : Finset (α ⊕ Unit)) := by
            rw [← hx']
            exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
          rw [Finset.mem_singleton] at hzin
          rw [Finset.mem_singleton]
          exact Sum.inl_injective (hzin.trans hxy.symm)
        · intro hz
          rw [Finset.mem_singleton] at hz
          subst hz
          exact hy
      rw [hAeq, Finset.card_singleton]
    · -- 平凡支 2：`A.image inl = {x}ᶜ`
      obtain ⟨x, hx⟩ := htriv2
      have hx' : A.image (Sum.inl : α → α ⊕ Unit) = ({x} : Finset (α ⊕ Unit))ᶜ := by
        rw [← hside]; exact hx
      cases x with
      | inl y =>
        exfalso
        have hmem : Sum.inr () ∈ ({Sum.inl y} : Finset (α ⊕ Unit))ᶜ := by simp
        rw [← hx'] at hmem
        simp at hmem
      | inr u =>
        cases u
        refine Or.inr (Or.inr ?_)
        ext z
        refine ⟨fun _ => Finset.mem_univ z, fun _ => ?_⟩
        have hz : Sum.inl z ∈ ({Sum.inr ()} : Finset (α ⊕ Unit))ᶜ := by simp
        rw [← hx'] at hz
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hz
        rw [Sum.inl.injEq] at hwe
        subst hwe
        exact hw
  · -- 反向：三个来源各给一条见证 split
    have hsingle : A.card = 1 → (attachRoot L hlam h3).IsClade (A.image Sum.inl) := by
      intro h1
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
      have hset : ({x} : Finset α).image (Sum.inl : α → α ⊕ Unit) = {Sum.inl x} :=
        Finset.image_singleton (Sum.inl : α → α ⊕ Unit) x
      refine ⟨Phylo.splitOf ({Sum.inl x} : Finset (α ⊕ Unit)) (Finset.singleton_nonempty _)
        ⟨Sum.inr (), by simp⟩, ?_, ?_⟩
      · exact (isSplitOf_attachRoot hlam h3 _).mpr
          (Or.inr (Or.inl ⟨Sum.inl x, Phylo.splitOf_sideA _ _ _⟩))
      · exact (Phylo.splitOf_sideA _ _ _).trans hset.symm
    have huniv : A = Finset.univ → (attachRoot L hlam h3).IsClade (A.image Sum.inl) := by
      intro hU
      subst hU
      have hcα : 0 < Fintype.card α := by
        have hc : Fintype.card (α ⊕ Unit) = Fintype.card α + 1 := by
          rw [Fintype.card_sum, Fintype.card_unit]
        omega
      have hnon : ((Finset.univ : Finset α).image (Sum.inl : α → α ⊕ Unit)).Nonempty :=
        ⟨Sum.inl (Classical.choice (Fintype.card_pos_iff.mp hcα)),
          Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
      have hset : ((Finset.univ : Finset α).image (Sum.inl : α → α ⊕ Unit))
          = ({Sum.inr ()} : Finset (α ⊕ Unit))ᶜ := by
        ext x
        cases x with
        | inl y =>
            constructor
            · intro _
              rw [Finset.mem_compl, Finset.mem_singleton]
              exact Sum.inl_ne_inr
            · intro _
              exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
        | inr u =>
            cases u
            constructor
            · intro h
              obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
              rw [Finset.mem_compl, Finset.mem_singleton]
              exact fun _ => Sum.inl_ne_inr hw
            · intro h
              exact absurd (Finset.mem_singleton_self (Sum.inr ()))
                (Finset.mem_compl.mp h)
      let s : Split (α ⊕ Unit) :=
        Phylo.splitOf ((Finset.univ : Finset α).image (Sum.inl : α → α ⊕ Unit)) hnon
          ⟨Sum.inr (), by simp⟩
      have hsd : s.sideA = ((Finset.univ : Finset α).image (Sum.inl : α → α ⊕ Unit)) :=
        Phylo.splitOf_sideA _ _ _
      exact ⟨s, (isSplitOf_attachRoot hlam h3 s).mpr
        (Or.inr (Or.inr ⟨Sum.inr (), hsd.trans hset⟩)), hsd⟩
    have hpush : A ∈ L → 2 ≤ A.card → A.card ≤ Fintype.card α - 1 →
        (attachRoot L hlam h3).IsClade (A.image Sum.inl) := by
      intro hAL h2 hle
      have hlt : A.card < Fintype.card α := by
        have := Finset.card_pos.mpr (hne A hAL)
        omega
      have hne' : A ≠ Finset.univ := by
        intro h
        rw [h, Finset.card_univ] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      exact ⟨Phylo.splitOf (A.image Sum.inl) ((hne A hAL).image Sum.inl) ⟨Sum.inr (), by simp⟩,
        (isSplitOf_attachRoot hlam h3 _).mpr
          (Or.inl (Finset.mem_union.mpr
            (Or.inl (mem_attachFamily.mpr ⟨A, hAL, hne', h2, rfl⟩)))),
        Phylo.splitOf_sideA _ _ _⟩
    rintro (hAL | h1 | hU)
    · by_cases h2 : 2 ≤ A.card
      · by_cases hle : A.card ≤ Fintype.card α - 1
        · exact hpush hAL h2 hle
        · exact huniv (Finset.eq_univ_of_card A (by have := Finset.card_le_univ A; omega))
      · exact hsingle (by have := Finset.card_pos.mpr (hne A hAL); omega)
    · exact hsingle h1
    · exact huniv hU

end Cladogram
