/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Consensus

/-!
# `Phylo.Supertree` —— 严格共识（NEXT.md **C1**）与 MinCut supertree（**C6**）

本文件实现 NEXT.md **P0-B（C 组）** 的两项：

## C1 严格共识（Day 1985）

一族同叶集的树 `T : ι → Cladogram X`，**所有树都含**的 split 之集
（`strictSplits`）两两相容 —— 因为它们都是任一棵 `T i` 的 split，
而一棵树的 split 系统两两相容（`pairwiseCompatible`）。

再由 Aho–Buneman 立得**严格共识树存在**（`strict_consensus_exists`）。

## C6 MinCut supertree（Semple–Steel 2000）

* **(i) 相容情形**（`supertree_exists_of_pairwiseCompatible` /
  `supertree_displays_of_pairwiseCompatible`）：若输入 split 集**两两相容**，
  则存在一棵 cladogram **定向展示全部输入 split** —— 这是「supertree 正确性」的核心，
  也正是 Semple–Steel 的 **Theorem 4.3**（`references/md/SempleSteel2000_MinCutSupertree.md:376`）
  在 split 层的对应物。
* **(ii) 割层**（`cutGraph` / `IsBlock` / `block_separates`）：把算法的第 3–4 步
  （图 `S_T` 不连通 ⟹ 按连通分支分块 ⟹ 递归）形式化到 split 层。

## 前提（本文件所有定理都显式带上）

* **`3 ≤ |X|`**：全部主定理都有此前提 —— 因为构造走 `Phylo.Laminar.toCladogram`，
  它要求根非退化 `3 ≤ |孩子| + |直接元素|`（`|X| = 2` 时恰好差 1，得到的只是**度 2 根**的有根树）。
  `|X| = 2` 是退化情形（`Split X` 只有一对互反 split，单边树即展示它），**本文件未覆盖**。
* **C1 额外需要 `[Nonempty ι]`**：`ι` 空时 `strictSplits = Finset.univ`（含不相容对），
  `strict_compatible` 不成立。

## 相比 `Phylo.Aho` 的两点加强

1. `Phylo.Aho.compatible_exists_rootedTree` 返回 `RootedTree`，且只保证**允许换向**地展示
   （`DisplaysSplit`）。本文件给出 **`Cladogram`** 版本（`exists_cladogram_of_compatible`），
   且展示是**定向的**（`IsSplitOf`，不换向）—— 见 `isSplitOf_splitOf` 的用法。
   代价：要求 `3 ≤ |X|`（`toCladogram` 的根非退化条件；见 `three_le_card_kids_add_dirs`）。
2. 附带**边侧刻画**（`toCladogram_isSplitOf_cases`）：`toCladogram` 的每条边侧只可能是
   「族成员」或「族成员的补」或「单点 / 单点的补」。这条是 C1 的 `↔` 方向（「共识树的
   split 集**恰是**公共 split 集」）所需的全部内容。

⚠️ **诚实边界**：MinCut 算法中「**最小权割**的选取」（Semple–Steel §3 的 `S_T/E_max`、
Proposition 4.1 的 `c(G∖e) + w(e) = c(G)` 判据）以及最后的「**粘合**（把各子树的根接到新根）」
**未**形式化 —— 见文件末尾 §8 的说明。
-/

open Phylo

universe u

-- `IsChildOf F _ _` 是 `Prop`，「孩子数」「直接元素数」等基数运算需要经典可判定性。
attribute [local instance] Classical.propDecidable

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 桥接引理：`IsSplitOf` 只看 `sideA` -/

namespace Cladogram

/-- **`IsSplitOf` 只依赖 `sideA`**：`s` 与 `t` 的 `sideA` 相同 ⟹
「`T` 展示 `t`」立即给出「`T` 展示 `s`」。

（有了它，「同一 split 的两种写法」不必再走 `KPartition.eq_iff_parts`。） -/
theorem isSplitOf_of_sideA_eq {T : Cladogram X} {s t : Split X} (h : s.sideA = t.sideA)
    (ht : T.IsSplitOf t) : T.IsSplitOf s := by
  obtain ⟨a, b, hab, u, hu⟩ := ht
  exact ⟨a, b, hab, u, h.trans hu⟩

/-- `s.sideA = {x}` ⟹ **任何**树都展示 `s`（叶边 `⟦leaf x, b⟧` 的 `x` 侧恰是 `{x}`）。 -/
theorem isSplitOf_of_sideA_singleton (T : Cladogram X) {s : Split X} {x : X}
    (h : s.sideA = {x}) : T.IsSplitOf s := by
  have hdeg : T.graph.degree (T.leaf x) = 1 := (T.isLeaf_iff_degree_eq_one _).mp ⟨x, rfl⟩
  obtain ⟨b, hb, -⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  exact ⟨T.leaf x, b, hb, T.leaf x, by rw [h]; exact (T.sideLeaves_leaf_edge hb).symm⟩

/-- `s.sideB = {x}` ⟹ **任何**树都展示 `s`（换向化归到 `sideA` 情形）。 -/
theorem isSplitOf_of_sideB_singleton (T : Cladogram X) {s : Split X} {x : X}
    (h : s.sideB = {x}) : T.IsSplitOf s := by
  have h' : T.IsSplitOf s.swap :=
    isSplitOf_of_sideA_singleton T (s := s.swap) (x := x) (by rw [Split.swap_sideA]; exact h)
  have h'' := T.isSplitOf_swap h'
  rwa [Split.swap_swap] at h''

end Cladogram

/-! ## 2. 根非退化：`3 ≤ |univ 的孩子| + |univ 的直接元素|`

`Phylo.Laminar.toCladogram` 要求该量 `≥ 3`（否则 `univ` 成度 2 顶点，不是 cladogram）。
`two_le_card_kids_add_dirs` 已给 `≥ 2`；这里把**退化的 `= 2`** 排除掉。

两个关键结构事实（本文件在应用处提供）：
* 每个非 `univ` 成员 `B` 都是某个输入 split 的**规范簇** ⟹ `ρ ∉ B`、且 `Bᶜ` 是**另一侧**（`≥ 2` 个叶）；
* `X` 是「直接元素」与「`univ` 的孩子」的**不交并**（`hcover`）。
-/

/-- ★★ **`3 ≤ |univ 的孩子| + |univ 的直接元素|`**（比 `two_le_card_kids_add_dirs` 强一档）。

假设（**不需要**镶嵌性，也**不需要** `univ ∈ F`）：
* `3 ≤ |X|`；
* 存在 `ρ` 不被任何**非 `univ`** 成员含（每个非 `univ` 成员都是避开 `ρ` 的规范簇）；
* 每个非 `univ` 成员的补至少 2 个元素（该成员是某个**非平凡** split 的一侧）。

三种退化情形都被 `hcover`（`X = 直接元素 ⊔ 孩子`）排除：
`|孩子| = 0` 时直接元素就是 `X`（`≥ 3`）；`|孩子| = |直接元素| = 1` 时
`Aᶜ ⊆ 直接元素` 与 `2 ≤ |Aᶜ|` 矛盾；`|孩子| = 2`、无直接元素时 `ρ` 落在两个孩子之一，矛盾。 -/
theorem three_le_card_kids_add_dirs {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} (h3 : 3 ≤ Fintype.card α)
    {ρ : α} (havoid : ∀ B ∈ F, B ≠ Finset.univ → ρ ∉ B)
    (hcompl : ∀ B ∈ F, B ≠ Finset.univ → 2 ≤ Bᶜ.card) :
    3 ≤ (F.filter fun B => IsChildOf F Finset.univ B).card
      + (directElems F Finset.univ).card := by
  classical
  by_contra hcon
  have hle : (F.filter fun B => IsChildOf F Finset.univ B).card
      + (directElems F Finset.univ).card ≤ 2 := by omega
  set K : Finset (Finset α) := F.filter fun B => IsChildOf F Finset.univ B with hK
  set D : Finset α := directElems F Finset.univ with hD
  -- `X` 的每个元素要么直接挂在 `univ` 上，要么落在 `univ` 的某个孩子里
  have hcover : ∀ x : α, x ∈ D ∨ ∃ A ∈ K, x ∈ A := by
    intro x
    by_cases hx : x ∈ D
    · exact Or.inl hx
    · refine Or.inr ?_
      have hx' : ¬ ∀ B ∈ F, x ∈ B → Finset.univ ⊆ B := by
        intro hall
        exact hx (by rw [hD, mem_directElems]; exact ⟨Finset.mem_univ x, hall⟩)
      push Not at hx'
      obtain ⟨B, hBF, hxB, hBsub⟩ := hx'
      have hBne : B ≠ Finset.univ := fun h => hBsub (h ▸ Finset.subset_univ B)
      obtain ⟨C, hCchild, hBC⟩ := exists_isChildOf_univ_superset hBF hBne
      exact ⟨C, hK.symm ▸ Finset.mem_filter.mpr ⟨hCchild.1, hCchild⟩, hBC hxB⟩
  rcases (by omega : K.card = 0 ∨ K.card = 1 ∨ K.card = 2) with hk | hk | hk
  · -- `|K| = 0`：族里只有 `univ`，全部元素都是「直接元素」
    have hKempty : K = ∅ := Finset.card_eq_zero.mp hk
    have hsub : (Finset.univ : Finset α) ⊆ D := by
      intro x _
      rcases hcover x with h | ⟨A, hA, -⟩
      · exact h
      · exact absurd (hKempty ▸ hA) (Finset.notMem_empty A)
    have hcard : Fintype.card α ≤ D.card := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_univ] at this
    omega
  · -- `|K| = 1`：唯一孩子 `A`，则 `Aᶜ ⊆ D` 而 `D.card ≤ 1`
    obtain ⟨A, hAK⟩ := Finset.card_eq_one.mp hk
    have hAin : A ∈ K := hAK.symm ▸ (Finset.mem_singleton_self A : A ∈ ({A} : Finset (Finset α)))
    have hAchild : IsChildOf F Finset.univ A := (Finset.mem_filter.mp hAin).2
    have hAne : A ≠ Finset.univ := (Finset.ssubset_iff_subset_ne.mp hAchild.2.1).2
    have hsub : (Finset.univ : Finset α) ⊆ A ∪ D := by
      intro x _
      rcases hcover x with h | ⟨C, hC, hxC⟩
      · exact Finset.mem_union.mpr (Or.inr h)
      · have hCA : C = A := by
          have hC' : C ∈ ({A} : Finset (Finset α)) := hAK ▸ hC
          exact Finset.mem_singleton.mp hC'
        exact Finset.mem_union.mpr (Or.inl (hCA ▸ hxC))
    have hsub2 : Aᶜ ⊆ D := by
      intro x hx
      rcases Finset.mem_union.mp (hsub (Finset.mem_univ x)) with h | h
      · exact absurd h (by simpa using hx)
      · exact h
    have hle' : Aᶜ.card ≤ D.card := Finset.card_le_card hsub2
    have hcomplA : 2 ≤ Aᶜ.card := hcompl A hAchild.1 hAne
    omega
  · -- `|K| = 2`、`D = ∅`：两个孩子的并是 `X`，而 `ρ` 避开两者
    obtain ⟨A₁, A₂, -, hAK⟩ := Finset.card_eq_two.mp hk
    have hDempty : D = ∅ := Finset.card_eq_zero.mp (by omega)
    have hA1 : A₁ ∈ K :=
      hAK.symm ▸ (Finset.mem_insert_self A₁ {A₂} : A₁ ∈ ({A₁, A₂} : Finset (Finset α)))
    have hA2 : A₂ ∈ K :=
      hAK.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self A₂) :
        A₂ ∈ ({A₁, A₂} : Finset (Finset α)))
    have hchild1 : IsChildOf F Finset.univ A₁ := (Finset.mem_filter.mp hA1).2
    have hchild2 : IsChildOf F Finset.univ A₂ := (Finset.mem_filter.mp hA2).2
    have hsub : (Finset.univ : Finset α) ⊆ A₁ ∪ A₂ := by
      intro x _
      rcases hcover x with h | ⟨C, hC, hxC⟩
      · exact absurd (hDempty ▸ h) (Finset.notMem_empty x)
      · have hC' : C ∈ ({A₁, A₂} : Finset (Finset α)) := hAK ▸ hC
        rcases Finset.mem_insert.mp hC' with h | h
        · exact Finset.mem_union.mpr (Or.inl (h ▸ hxC))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mp h ▸ hxC))
    have hρ1 : ρ ∉ A₁ := havoid A₁ hchild1.1 (Finset.ssubset_iff_subset_ne.mp hchild1.2.1).2
    have hρ2 : ρ ∉ A₂ := havoid A₂ hchild2.1 (Finset.ssubset_iff_subset_ne.mp hchild2.2.1).2
    rcases Finset.mem_union.mp (hsub (Finset.mem_univ ρ)) with h | h
    · exact hρ1 h
    · exact hρ2 h

/-! ## 3. `toCladogram` 的两条刻画 -/

/-- ★★ **`toCladogram` 的每条边侧都是「族成员 / 族成员的补 / 单点 / 单点的补」**。

证明：边都可写成 `parEdge`（`edgeSet_subset_range`），而 `parEdge v` 只有两种形态：
* `v = Sum.inl A`（簇）：两侧是 `A`（`leafSide_parentEdge`）与 `Aᶜ`（补侧）；
* `v = Sum.inr x`（元素）：两侧是 `{x}`（叶边的侧，`sideLeaves_leaf_edge`）与 `{x}ᶜ`。

任意顶点 `u` 必与边的某一端点同侧（`inSide_or_inSide`），而 `sideLeaves` 在同侧上不变
（`sideLeaves_eq_of_inSide`）。 -/
theorem toCladogram_isSplitOf_cases {F : Finset (Finset X)} (hl : LaminarFamily F)
    (hne : ∀ B ∈ F, B.Nonempty) (huniv : (Finset.univ : Finset X) ∈ F)
    (hcard : ∀ B ∈ F, B = Finset.univ ∨ 2 ≤ B.card)
    (hroot : 3 ≤ (F.filter fun B => IsChildOf F Finset.univ B).card
        + (directElems F Finset.univ).card)
    {s : Split X} (hs : (toCladogram hl hne huniv hcard hroot).IsSplitOf s) :
    (∃ B ∈ F, B ≠ Finset.univ ∧ (s.sideA = B ∨ s.sideA = Bᶜ)) ∨
      (∃ x : X, s.sideA = {x} ∨ s.sideA = {x}ᶜ) := by
  classical
  obtain ⟨a, b, hab, u, hu⟩ := hs
  -- `s(a,b)` 是 `treeGraph F` 的边
  have he : s(a, b) ∈ (treeGraph F).edgeSet := by
    have h : s(a, b) ∈ (toCladogram hl hne huniv hcard hroot).graph.edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hab
    rwa [toCladogram_graph] at h
  -- 每条边都是某个非根顶点的 `parEdge`
  obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp (edgeSet_subset_range hl hne huniv he)
  rw [Finset.mem_erase] at hv
  rcases v with A | x
  · -- 簇–簇边：`s(a,b) = s(inl A, inl (parentV A))`
    have hAne : A.1 ≠ Finset.univ := fun h => hv.1 (congrArg Sum.inl (Subtype.ext h))
    have hparV : parV hl hne huniv (Sum.inl A) = Sum.inl (parentV hl hne huniv A hAne) := by
      show (if h : A.1 = Finset.univ then Sum.inl A
        else Sum.inl (parentV hl hne huniv A h)) = Sum.inl (parentV hl hne huniv A hAne)
      split_ifs with h
      · exact absurd (congrArg Sum.inl (Subtype.ext h)) hv.1
      · exact congrArg Sum.inl (Subtype.ext rfl)
    have hsym : s(a, b) = s(Sum.inl A, Sum.inl (parentV hl hne huniv A hAne)) :=
      hve.symm.trans (congrArg (fun z => s(Sum.inl A, z)) hparV)
    have hadj : (toCladogram hl hne huniv hcard hroot).graph.Adj
        (Sum.inl A) (Sum.inl (parentV hl hne huniv A hAne)) := by
      rw [toCladogram_graph]
      exact (treeGraph_adj_inl_inl F A (parentV hl hne huniv A hAne)).mpr
        (Or.inl (isParentOf_parentOf (A := A.1) hl hne huniv A.2 hAne))
    have hsidec : (toCladogram hl hne huniv hcard hroot).sideLeaves
        s(Sum.inl A, Sum.inl (parentV hl hne huniv A hAne)) (Sum.inl A) = A.1 :=
      leafSide_parentEdge hl hne huniv A.2 hAne
    have hkey : ∀ w : LaminarVertex F,
        (toCladogram hl hne huniv hcard hroot).sideLeaves
            s(Sum.inl A, Sum.inl (parentV hl hne huniv A hAne)) w = A.1 ∨
          (toCladogram hl hne huniv hcard hroot).sideLeaves
            s(Sum.inl A, Sum.inl (parentV hl hne huniv A hAne)) w = A.1ᶜ := by
      intro w
      rcases (toCladogram hl hne huniv hcard hroot).inSide_or_inSide hadj (x := w) with hw | hw
      · left
        exact ((toCladogram hl hne huniv hcard hroot).sideLeaves_eq_of_inSide hw).trans hsidec
      · right
        exact (((toCladogram hl hne huniv hcard hroot).sideLeaves_eq_of_inSide hw).trans
          ((toCladogram hl hne huniv hcard hroot).sideLeaves_compl_adj hadj)).trans
          (congrArg (fun z : Finset X => zᶜ) hsidec)
    have htransfer : (toCladogram hl hne huniv hcard hroot).sideLeaves s(a, b) u
        = (toCladogram hl hne huniv hcard hroot).sideLeaves
            s(Sum.inl A, Sum.inl (parentV hl hne huniv A hAne)) u :=
      congrArg (fun e => (toCladogram hl hne huniv hcard hroot).sideLeaves e u) hsym
    rcases hkey u with hh | hh
    · exact Or.inl ⟨A.1, A.2, hAne, Or.inl (hu.trans (htransfer.trans hh))⟩
    · exact Or.inl ⟨A.1, A.2, hAne, Or.inr (hu.trans (htransfer.trans hh))⟩
  · -- 元素–簇边：`s(a,b) = s(inr x, inl (minClusterV x))`
    have hsym : s(a, b) = s(Sum.inr x, Sum.inl (minClusterV hl huniv x)) := hve.symm
    have hadj : (toCladogram hl hne huniv hcard hroot).graph.Adj
        ((toCladogram hl hne huniv hcard hroot).leaf x) (Sum.inl (minClusterV hl huniv x)) := by
      rw [toCladogram_graph]
      exact (treeGraph_adj_inr_inl F x (minClusterV hl huniv x)).mpr (minClusterV_spec hl huniv x)
    have hsidec : (toCladogram hl hne huniv hcard hroot).sideLeaves
        s((toCladogram hl hne huniv hcard hroot).leaf x, Sum.inl (minClusterV hl huniv x))
        ((toCladogram hl hne huniv hcard hroot).leaf x) = {x} :=
      Cladogram.sideLeaves_leaf_edge _ hadj
    have hkey : ∀ w : LaminarVertex F,
        (toCladogram hl hne huniv hcard hroot).sideLeaves
            s((toCladogram hl hne huniv hcard hroot).leaf x, Sum.inl (minClusterV hl huniv x)) w
            = {x} ∨
          (toCladogram hl hne huniv hcard hroot).sideLeaves
            s((toCladogram hl hne huniv hcard hroot).leaf x, Sum.inl (minClusterV hl huniv x)) w
            = {x}ᶜ := by
      intro w
      rcases (toCladogram hl hne huniv hcard hroot).inSide_or_inSide hadj (x := w) with hw | hw
      · left
        exact ((toCladogram hl hne huniv hcard hroot).sideLeaves_eq_of_inSide hw).trans hsidec
      · right
        exact (((toCladogram hl hne huniv hcard hroot).sideLeaves_eq_of_inSide hw).trans
          ((toCladogram hl hne huniv hcard hroot).sideLeaves_compl_adj hadj)).trans
          (congrArg (fun z : Finset X => zᶜ) hsidec)
    have htransfer : (toCladogram hl hne huniv hcard hroot).sideLeaves s(a, b) u
        = (toCladogram hl hne huniv hcard hroot).sideLeaves
            s((toCladogram hl hne huniv hcard hroot).leaf x,
              Sum.inl (minClusterV hl huniv x)) u :=
      congrArg (fun e => (toCladogram hl hne huniv hcard hroot).sideLeaves e u) hsym
    rcases hkey u with hh | hh
    · exact Or.inr ⟨x, Or.inl (hu.trans (htransfer.trans hh))⟩
    · exact Or.inr ⟨x, Or.inr (hu.trans (htransfer.trans hh))⟩

/-! ## 4. 相容 split 族 ⟹ cladogram（Aho 的 `Cladogram` 加强版） -/

/-- ★★★ **两两相容的（非平凡）split 族 ⟹ 存在 cladogram 定向展示全体**，
且该 cladogram 的每条边侧都被 `normFinset` 的成员（或单点）控制。

这是 `Phylo.Aho.compatible_exists_rootedTree` 的加强：
* 结论是 **`Cladogram`**（不是 `RootedTree`）；
* 展示是**定向的**（`IsSplitOf`，不换向）；
* 附带边侧刻画（供 C1 的 `↔` 使用）。

**构造**：规范簇族 `F = {s.cluster ρ | s ∈ fam}`（相容 ⟹ 镶嵌），
正规化 `normFinset F`（删单元素簇、加 `univ`），再用 `toCladogram` 建树。
`hroot` 由 `three_le_card_kids_add_dirs` 提供（这里是 `3 ≤ |X|` 的唯一用处）。 -/
theorem exists_cladogram_of_compatible (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X,
      (∀ s ∈ fam, M.IsSplitOf s) ∧
      (∀ s : Split X, M.IsSplitOf s →
        (∃ B ∈ normFinset (fam.image fun s => s.cluster ρ), B ≠ Finset.univ ∧
            (s.sideA = B ∨ s.sideA = Bᶜ)) ∨
        (∃ x : X, s.sideA = {x} ∨ s.sideA = {x}ᶜ)) := by
  classical
  have h2 : 2 ≤ Fintype.card X := by omega
  set F : Finset (Finset X) := fam.image (fun s => s.cluster ρ) with hF
  have hmemF : ∀ A : Finset X, A ∈ F ↔ ∃ s ∈ fam, s.cluster ρ = A := by
    intro A; rw [hF, Finset.mem_image]
  have hl : LaminarFamily F := by
    intro A hA B hB
    obtain ⟨s, hs, rfl⟩ := (hmemF A).mp hA
    obtain ⟨t, ht, rfl⟩ := (hmemF B).mp hB
    exact laminar_of_compatible_clusters (hcomp s hs t ht) rfl rfl
  set F' : Finset (Finset X) := normFinset F with hF'
  have hmemF' : ∀ B : Finset X, B ∈ F' ↔ B = Finset.univ ∨ (B ∈ F ∧ 2 ≤ B.card) := by
    intro B; rw [hF']; exact mem_normFinset
  have hl' : LaminarFamily F' := by rw [hF']; exact laminarFamily_normFinset hl
  have huniv' : (Finset.univ : Finset X) ∈ F' := by rw [hF']; exact univ_mem_normFinset
  have hcard' : ∀ B ∈ F', B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rcases (hmemF' B).mp hB with h | h
    · exact Or.inl h
    · exact Or.inr h.2
  have hne' : ∀ B ∈ F', B.Nonempty := nonempty_of_mem_of_hcard hcard' h2
  have hcompl' : ∀ B ∈ F', B ≠ Finset.univ → 2 ≤ Bᶜ.card := by
    intro B hB hBne
    have hBF : B ∈ F := ((hmemF' B).mp hB).resolve_left hBne |>.1
    obtain ⟨t, ht, htB⟩ := (hmemF B).mp hBF
    rw [← htB]
    rcases t.cluster_eq_sideA_or_compl ρ with hcl | hcl
    · rw [hcl, ← Split.sideB_eq_compl]; exact (hnt t ht).2
    · rw [hcl, compl_compl]; exact (hnt t ht).1
  have havoid' : ∀ B ∈ F', B ≠ Finset.univ → ρ ∉ B := by
    intro B hB hBne
    have hBF : B ∈ F := ((hmemF' B).mp hB).resolve_left hBne |>.1
    obtain ⟨t, ht, htB⟩ := (hmemF B).mp hBF
    rw [← htB]; exact t.notMem_cluster ρ
  have hroot : 3 ≤ (F'.filter fun B => IsChildOf F' Finset.univ B).card
      + (directElems F' Finset.univ).card :=
    three_le_card_kids_add_dirs h3 havoid' hcompl'
  refine ⟨toCladogram hl' hne' huniv' hcard' hroot, ?_, ?_⟩
  · -- 定向展示
    intro s hs
    have hBmemF : s.cluster ρ ∈ F := (hmemF _).mpr ⟨s, hs, rfl⟩
    have hBcard : 2 ≤ (s.cluster ρ).card := by
      rcases s.cluster_eq_sideA_or_compl ρ with h | h
      · rw [h]; exact (hnt s hs).1
      · rw [h, ← Split.sideB_eq_compl]; exact (hnt s hs).2
    have hBne : s.cluster ρ ≠ Finset.univ :=
      fun hh => s.notMem_cluster ρ (hh ▸ Finset.mem_univ ρ)
    have hBmemF' : s.cluster ρ ∈ F' := (hmemF' _).mpr (Or.inr ⟨hBmemF, hBcard⟩)
    have hsp := isSplitOf_splitOf hl' hne' huniv' hcard' hroot hBmemF' hBne
    rcases s.cluster_eq_sideA_or_compl ρ with hcl | hcl
    · exact Cladogram.isSplitOf_of_sideA_eq
        (show s.sideA = (splitOf (s.cluster ρ) (hne' _ hBmemF')
            (compl_nonempty_of_ne_univ hBne)).sideA by rw [splitOf_sideA, hcl]) hsp
    · refine Cladogram.isSplitOf_of_sideA_eq
        (show s.sideA = (splitOf (s.cluster ρ) (hne' _ hBmemF')
            (compl_nonempty_of_ne_univ hBne)).swap.sideA by
          rw [Split.swap_sideA, splitOf_sideB, hcl, compl_compl]) ?_
      exact (toCladogram hl' hne' huniv' hcard' hroot).isSplitOf_swap hsp
  · -- 边侧刻画
    intro s hs
    exact toCladogram_isSplitOf_cases hl' hne' huniv' hcard' hroot hs

/-! ## 5. C6 (i)：**相容情形 —— supertree 展示全部输入 split** -/

/-- ★★★ **MinCut supertree（相容情形）**：输入 split 集两两相容 ⟹
存在 cladogram **定向展示**全部输入 split。

这是 Semple–Steel (2000) **Theorem 4.3**「`T` 相容 ⟹ `M(T)` 展示 `T` 中每棵树」
在 **split 层**的对应物：一棵树的 split 系统就是它的全部信息，
「展示 split 集」即「展示这棵树」。

* `fam` 两两相容（`hcomp`）；
* `fam` 每个成员**非平凡**（两侧各 `≥ 2` 个叶，`hnt`）——**任意** `fam`（含平凡 split）由
  ★★★ `supertree_displays_of_pairwiseCompatible`（结论一样强，是本文理的推广）处理；
* `3 ≤ |X|`（`toCladogram` 的根非退化条件）。 -/
theorem supertree_exists_of_pairwiseCompatible {X : Type u} [Fintype X] [DecidableEq X]
    (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s ∈ fam, M.IsSplitOf s := by
  obtain ⟨M, hM, -⟩ := exists_cladogram_of_compatible fam ρ hcomp hnt h3
  exact ⟨M, hM⟩

/-- ★★★ **MinCut supertree（相容情形，**任意**输入集）**：输入 split 集**两两相容**（不要求非平凡）
⟹ 存在 cladogram **定向展示**（`IsSplitOf`，不换向）全部输入 split。

**比 `supertree_exists_of_pairwiseCompatible` 更一般**：不需要 `fam` 成员非平凡 ——
平凡 split（一侧只有 1 片叶）由任何树的**叶边**定向展示
（`isSplitOf_of_sideA_singleton` / `isSplitOf_of_sideB_singleton`），
非平凡部分交给 `supertree_exists_of_pairwiseCompatible`。 -/
theorem supertree_displays_of_pairwiseCompatible {X : Type u} [Fintype X] [DecidableEq X]
    (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t) (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s ∈ fam, M.IsSplitOf s := by
  classical
  set famN : Finset (Split X) :=
    fam.filter fun s : Split X => 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card with hfamN
  have hcompN : ∀ s ∈ famN, ∀ t ∈ famN, Split.Compatible s t :=
    fun s hs t ht => hcomp s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1
  have hntN : ∀ s ∈ famN, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
    fun s hs => (Finset.mem_filter.mp hs).2
  obtain ⟨M, hM⟩ := supertree_exists_of_pairwiseCompatible famN ρ hcompN hntN h3
  refine ⟨M, fun s hs => ?_⟩
  by_cases hsN : s ∈ famN
  · exact hM s hsN
  · rw [hfamN, Finset.mem_filter] at hsN
    by_cases ha : 2 ≤ s.sideA.card
    · have hpos : 0 < s.sideB.card := by
        simpa [Split.sideB] using Finset.card_pos.mpr (s.nonempty 1)
      have hlt : s.sideB.card < 2 := Nat.lt_of_not_le fun hb => hsN ⟨hs, ha, hb⟩
      have hcard1 : s.sideB.card = 1 := by omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
      exact Cladogram.isSplitOf_of_sideB_singleton M hx
    · have hpos : 0 < s.sideA.card := by
        simpa [Split.sideA] using Finset.card_pos.mpr (s.nonempty 0)
      have hlt : s.sideA.card < 2 := Nat.lt_of_not_le ha
      have hcard1 : s.sideA.card = 1 := by omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
      exact Cladogram.isSplitOf_of_sideA_singleton M hx

/-! ## 6. C1：严格共识（Day 1985） -/

section StrictConsensus

variable {ι : Type*}

/-- **严格共识的 split 集**：树族 `T` 中**所有树都展示**的 split（= split 集之交）。

与 `supportCount` / `majoritySplits`（`Phylo/Consensus.lean`）平行：
把「严格多数」换成「**全体**」。 -/
noncomputable def strictSplits (T : ι → Cladogram X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s : Split X => ∀ i, (T i).IsSplitOf s

/-- `s` 是**公共 split**（族中每棵树都展示它）。 -/
theorem mem_strictSplits {T : ι → Cladogram X} {s : Split X} :
    s ∈ strictSplits T ↔ ∀ i, (T i).IsSplitOf s := by
  classical
  simp [strictSplits]

/-- ★★ **严格共识：公共 split 两两相容**。

`fam` 中每个成员都是**任一棵** `T i` 的 split（`ι` 非空时取一个 `i`），
而一棵树的 split 系统两两相容（`pairwiseCompatible`）。

（与 `majority_compatible` 对比：那里需要**鸽笼原理**（严格多数的支持集必相交），
这里「全体」使鸽笼原理退化为「随便取一棵树」。） -/
theorem strict_compatible [Nonempty ι] (T : ι → Cladogram X) {s t : Split X}
    (hs : s ∈ strictSplits T) (ht : t ∈ strictSplits T) : Split.Compatible s t :=
  pairwiseCompatible (T (Classical.arbitrary ι)) s ((mem_strictSplits.mp hs) _)
    t ((mem_strictSplits.mp ht) _)

/-- `strictSplits` 对**换向**封闭（`swap` 不改成员资格）。 -/
theorem swap_mem_strictSplits (T : ι → Cladogram X) (s : Split X) :
    s.swap ∈ strictSplits T ↔ s ∈ strictSplits T := by
  rw [mem_strictSplits, mem_strictSplits]
  constructor
  · intro h i
    have h' := (T i).isSplitOf_swap (h i)
    rwa [Split.swap_swap] at h'
  · intro h i
    exact (T i).isSplitOf_swap (h i)

/-- 若 `s.sideA = t.sideA`、`t` 是公共 split，则 `s` 也是。 -/
theorem mem_strictSplits_of_sideA (T : ι → Cladogram X) {s t : Split X}
    (ht : t ∈ strictSplits T) (h : s.sideA = t.sideA) : s ∈ strictSplits T :=
  mem_strictSplits.mpr fun i =>
    Cladogram.isSplitOf_of_sideA_eq h ((mem_strictSplits.mp ht) i)

/-- 若 `s.sideA = t.sideB`、`t` 是公共 split，则 `s` 也是（走 `swap`）。 -/
theorem mem_strictSplits_of_sideB (T : ι → Cladogram X) {s t : Split X}
    (ht : t ∈ strictSplits T) (h : s.sideA = t.sideB) : s ∈ strictSplits T := by
  have h' : s.swap.sideA = t.sideA := by
    calc s.swap.sideA = s.sideB := Split.swap_sideA s
      _ = s.sideAᶜ := Split.sideB_eq_compl s
      _ = t.sideBᶜ := congrArg (fun z : Finset X => zᶜ) h
      _ = t.sideA := by rw [Split.sideB_eq_compl t, compl_compl]
  exact mem_strictSplits.mpr fun i =>
    (T i).isSplitOf_swap (Cladogram.isSplitOf_of_sideA_eq (s := s.swap) (t := t) h'
      ((mem_strictSplits.mp ht) i))

/-- `s.sideA` 是单点 ⟹ `s` 是公共 split（任何树都展示单点 split）。 -/
theorem mem_strictSplits_of_sideA_singleton (T : ι → Cladogram X) {s : Split X}
    {x : X} (h : s.sideA = {x}) : s ∈ strictSplits T :=
  mem_strictSplits.mpr fun i => Cladogram.isSplitOf_of_sideA_singleton (T i) h

/-- `s.sideA` 是**单点的补** ⟹ `s` 是公共 split（此时 `s.sideB` 是单点）。 -/
theorem mem_strictSplits_of_sideA_compl_singleton (T : ι → Cladogram X) {s : Split X} {x : X}
    (h : s.sideA = {x}ᶜ) : s ∈ strictSplits T :=
  mem_strictSplits.mpr fun i =>
    Cladogram.isSplitOf_of_sideB_singleton (T i) (by rw [Split.sideB_eq_compl, h, compl_compl])

set_option maxHeartbeats 800000 in
/-- ★★★ **严格共识树存在**（Day 1985；Aho–Buneman 收口）。

对任一树族 `T : ι → Cladogram X`（`ι` 非空、`3 ≤ |X|`），存在 cladogram `M` 使

    `M.IsSplitOf s ↔ ∀ i, (T i).IsSplitOf s`.

即：**共识树的 split 集恰好是公共 split 集**（不是「⊇」，而是 `↔`）——
这里 `IsSplitOf` 是**定向**的，故 `↔` 比 `majority_consensus_exists` 的展示强：
它同时锁定了每条边的**朝向**。

**证明**：取非平凡的公共 split 族 `fam`（平凡 split 由叶边自动展示，见
`mem_strictSplits_of_sideA_singleton` 等），`strict_compatible` 给出两两相容，
`exists_cladogram_of_compatible` 建树并给出边侧刻画，刻画把 `M` 的每条边侧
拉回 `fam` 的成员（或其换向）。 -/
theorem strict_consensus_exists [Nonempty ι] (T : ι → Cladogram X) (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s : Split X, M.IsSplitOf s ↔ ∀ i, (T i).IsSplitOf s := by
  classical
  obtain ⟨ρ⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card X by omega)
  set fam : Finset (Split X) :=
    (strictSplits T).filter fun s : Split X => 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card with hfam
  have hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t :=
    fun s hs t ht =>
      strict_compatible T (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1
  have hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
    fun s hs => (Finset.mem_filter.mp hs).2
  obtain ⟨M, hM, hcases⟩ := exists_cladogram_of_compatible fam ρ hcomp hnt h3
  refine ⟨M, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · -- `M` 的 split ⟹ 公共 split
    rcases hcases s hs with ⟨B, hB, hBne, hBA⟩ | ⟨x, hx⟩
    · have hBF : B ∈ fam.image (fun s => s.cluster ρ) :=
        ((mem_normFinset.mp hB).resolve_left hBne).1
      obtain ⟨t, ht, htB⟩ := Finset.mem_image.mp hBF
      have ht' : t ∈ strictSplits T := (Finset.mem_filter.mp ht).1
      rcases hBA with hBA | hBA
      · rcases t.cluster_eq_sideA_or_compl ρ with hcl | hcl
        · exact mem_strictSplits.mp (mem_strictSplits_of_sideA T ht' (by rw [hBA, ← htB, hcl]))
        · exact mem_strictSplits.mp (mem_strictSplits_of_sideB T ht'
            (by rw [hBA, ← htB, hcl, Split.sideB_eq_compl]))
      · rcases t.cluster_eq_sideA_or_compl ρ with hcl | hcl
        · exact mem_strictSplits.mp (mem_strictSplits_of_sideB T ht'
            (by rw [hBA, ← htB, hcl, Split.sideB_eq_compl]))
        · exact mem_strictSplits.mp (mem_strictSplits_of_sideA T ht'
            (by rw [hBA, ← htB, hcl, compl_compl]))
    · rcases hx with hx | hx
      · exact mem_strictSplits.mp (mem_strictSplits_of_sideA_singleton T hx)
      · exact mem_strictSplits.mp (mem_strictSplits_of_sideA_compl_singleton T hx)
  · -- 公共 split ⟹ `M` 的 split
    by_cases htriv : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card
    · exact hM s (Finset.mem_filter.mpr ⟨mem_strictSplits.mpr hs, htriv⟩)
    · by_cases ha : 2 ≤ s.sideA.card
      · have hpos : 0 < s.sideB.card := by
          simpa [Split.sideB] using Finset.card_pos.mpr (s.nonempty 1)
        have hlt : s.sideB.card < 2 := Nat.lt_of_not_le fun hb => htriv ⟨ha, hb⟩
        have hcard1 : s.sideB.card = 1 := by omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
        exact Cladogram.isSplitOf_of_sideB_singleton M hx
      · have hpos : 0 < s.sideA.card := by
          simpa [Split.sideA] using Finset.card_pos.mpr (s.nonempty 0)
        have hlt : s.sideA.card < 2 := Nat.lt_of_not_le ha
        have hcard1 : s.sideA.card = 1 := by omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
        exact Cladogram.isSplitOf_of_sideA_singleton M hx

end StrictConsensus

/-! ## 7. C6 (ii)：割层（图 `S_T`、块、分解）

Semple–Steel 的算法第 3–4 步：
1. 构造图 `S_T`（`S` = 叶集）：`{a,b}` 是边 ⟺ 存在输入树使 `a`、`b` 同在一个**非平凡**
   **合适簇**（proper cluster）中；
2. 若 `S_T` **不连通**，取其连通分支 `S₁,…,S_r`，对每个 `S_j` **递归**
   （`MINCUTSUPERTREE(T|S_j, w_j)`），最后把各子树的根接到一个新根。

本节的 split 层对应物：**合适簇 = 规范簇 `s.cluster ρ`**（避开 `ρ` 的那一侧，
正是「有根树的位于该边之下的叶集」）。于是：

* `cutGraph fam ρ` —— 图 `S_T`；
* `IsBlock G A` —— `G` 的一个连通分支；
* ★★ `block_separates` —— **每个输入 split 的规范簇要么整个落在块内、要么与块相离**。
  这是「分块 ⟹ 子问题互相独立」的合法性来源；
* ★★ `isBlock_compl` / ★ `block_subfamily_supertree` —— 补块也是块、块内子族仍有 supertree。

⚠️ **未形式化的层**（见 §8）：**最小权割的选取**（`S_T/E_max`、`E'`、Proposition 4.1）
与**粘合**（把各子树接到新根得到单一棵树）本文件**没有**做。 -/

section MinCut

/-- **割图 `S_T`**（Semple–Steel 算法的 `S_T`，split 层实现）。

`a ~ b` ⟺ `a ≠ b` 且存在输入 split `s ∈ fam`，使 `a`、`b` 同在一个**非平凡**规范簇
`s.cluster ρ` 中（`2 ≤ |s.cluster ρ|`，对应文献的「合适簇」`2 ≤ |C| < |S|`）。

（技术说明：`Adj` 已要求 `a ≠ b`，故**单元素簇本就产生不了边** ——
这里的 `2 ≤ |s.cluster ρ|` 只是与文献的「合适簇」对齐，不影响 `S_T` 的边集。） -/
def cutGraph (fam : Finset (Split X)) (ρ : X) : SimpleGraph X where
  Adj a b := a ≠ b ∧ ∃ s ∈ fam, 2 ≤ (s.cluster ρ).card ∧ a ∈ s.cluster ρ ∧ b ∈ s.cluster ρ
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.2, hs.2.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **块**：`G` 的一个连通分支（非空 + 对可达封闭）。 -/
def IsBlock (G : SimpleGraph X) (A : Finset X) : Prop :=
  A.Nonempty ∧ ∀ a ∈ A, ∀ b : X, G.Reachable a b → b ∈ A

/-- ★★ **「断开即分块」：块与每个输入 split 的规范簇要么包含、要么相离**。

若某个规范簇 `s.cluster ρ` 与块 `A` 相交但**不**含于 `A`，
则取 `a ∈ s.cluster ρ ∩ A`、`b ∈ s.cluster ρ \ A`：
`|s.cluster ρ| ≥ 2` 使 `{a,b}` 成为 `cutGraph` 的一条边，于是 `b` 与 `a` 可达，
被 `A` 的可达封闭性拉回 `A` —— 矛盾。

⇒ 分块后每个子问题**互相独立**（输入 split 不会横跨两个块）。 -/
theorem block_separates (fam : Finset (Split X)) (ρ : X) {A : Finset X}
    (hA : IsBlock (cutGraph fam ρ) A) {s : Split X} (hs : s ∈ fam) :
    s.cluster ρ ⊆ A ∨ Disjoint (s.cluster ρ) A := by
  classical
  by_contra hcon
  have h1 : ¬ s.cluster ρ ⊆ A := fun h => hcon (Or.inl h)
  have h2 : ¬ Disjoint (s.cluster ρ) A := fun h => hcon (Or.inr h)
  rw [Finset.not_subset] at h1
  obtain ⟨a, ha, haA⟩ := h1
  have hne : (s.cluster ρ ∩ A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact h2 (Finset.disjoint_iff_inter_eq_empty.mpr hemp)
  obtain ⟨b, hb⟩ := hne
  rw [Finset.mem_inter] at hb
  have hab : a ≠ b := fun h => haA (h ▸ hb.2)
  have hcard : 2 ≤ (s.cluster ρ).card := by
    have : 1 < (s.cluster ρ).card := Finset.one_lt_card.mpr ⟨a, ha, b, hb.1, hab⟩
    omega
  have hadj : (cutGraph fam ρ).Adj a b := ⟨hab, s, hs, hcard, ha, hb.1⟩
  exact haA (hA.2 b hb.2 a hadj.reachable.symm)

/-- ★★ **补块也是块**（连通分支的补是若干分支之并）。 -/
theorem isBlock_compl {G : SimpleGraph X} {A : Finset X} (hA : IsBlock G A)
    (hAc : (Aᶜ).Nonempty) : IsBlock G Aᶜ := by
  refine ⟨hAc, fun a ha b hab => ?_⟩
  rw [Finset.mem_compl] at ha ⊢
  intro hb
  exact ha (hA.2 b hb a hab.symm)

/-- ★★ **块内子族仍有 supertree**：块天然给出「子问题」，
而子问题仍满足 C6 (i) 的全部假设（两两相容、非平凡、`3 ≤ |X|`）—— **递归合法**。

（`_hA` 只用于表明「这是某个块的子问题」—— 子族的相容性与非平凡性直接从 `fam` 继承，
「块」本身的分解作用由 ★★ `block_separates` 承载。） -/
theorem block_subfamily_supertree {X : Type u} [Fintype X] [DecidableEq X]
    (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (h3 : 3 ≤ Fintype.card X) {A : Finset X} (_hA : IsBlock (cutGraph fam ρ) A) :
    ∃ M : Cladogram.{u, u} X, ∀ s ∈ fam, s.cluster ρ ⊆ A → M.IsSplitOf s := by
  classical
  set famA : Finset (Split X) := fam.filter fun s => s.cluster ρ ⊆ A with hfamA
  have hcompA : ∀ s ∈ famA, ∀ t ∈ famA, Split.Compatible s t :=
    fun s hs t ht => hcomp s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1
  have hntA : ∀ s ∈ famA, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card :=
    fun s hs => hnt s (Finset.mem_filter.mp hs).1
  obtain ⟨M, hM⟩ := supertree_exists_of_pairwiseCompatible famA ρ hcompA hntA h3
  exact ⟨M, fun s hs hsub => hM s (Finset.mem_filter.mpr ⟨hs, hsub⟩)⟩

end MinCut

/-! ## 8. 诚实边界（C6 的 (ii) 做到哪一层）

**做到**（本文件 §7）：
* 图 `S_T` 的定义（`cutGraph`）；
* 连通分支（`IsBlock`）的合法性与「块 ⟹ 每个输入 split 的规范簇不横跨两个块」
  （`block_separates`）—— 这正是「分块后递归」正确的**组合内核**；
* 补块（`isBlock_compl`）与「块内子问题仍满足 C6 (i) 的假设」（`block_subfamily_supertree`）。

**未做到**（照实报告）：
1. **最小权割的选取**：Semple–Steel §3 的加权图 `S_T/E_max`、
   「落在某个最小权割集里的边」之集合 `E'`，以及 Proposition 4.1
   （`e` 属于某最小权割集 ⟺ `c(G∖e) + w(e) = c(G)`）—— 需要「割集 / 连通分支 /
   基数最小化」一整层，本文件**未**形式化；
2. **粘合（join）**：把 `r` 棵子树的根接到一个新根、并证明**粘合后的树展示原输入**
   （算法第 6–8 步）—— 本文件**未**给出粘合构造；
   故本文件给出的是「**各子问题独立且有解**」，而**不是**「MinCut 算法返回的树展示全部输入」。
   注意：相容情形的**最终正确性**（C6 (i)）已由 `supertree_exists_of_pairwiseCompatible`
   独立给出，不依赖粘合。
-/
