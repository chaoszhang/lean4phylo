/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Supertree

/-!
# `Phylo.AdamsConsensus` —— Adams 共识（W11a 第 (2) 项）

文献：`references/md/Adams1972_ConsensusTechniquesComparison.md`。
本库此前 **0 处**提及 Adams（`grep -i adams Phylo/` 无命中），故本文件填充的是**真空缺**。

## 文献原文（JSTOR 扫描 OCR；关键定义段落可读）

Adams (1972) 对**有根树 + 内部节点无标签**的情形给出的**递归定义**
（md 第 481–496 行）：

> Thus the recursive definition of consensus for a set of terminals of rooted trees with
> unlabelled internal nodes is:
> 1) if the set contains exactly one terminal, the consensus is that terminal itself.
> 2) otherwise find the **LUB** of the set on each rival tree. Construct the **product
> partition** as above. The consensus of the set is a node with a branch leading to each
> consensus of a **non-null group** of the product partition.

「product partition」在同页 md 第 464–479 行：

> … consider the LUB of a set as a partition of that set expressed by the branching at that
> node. The partition of the LUB in the consensus tree is expressed by the **cross product**
> of the partition from one rival LUB with the partition of the other rival LUB. So, if there
> are `n` groups in the partition of one LUB and `m` groups in the partition of the other,
> then there are `mn` groups in the product partition, one for each **intersection** of a
> group from one tree and a group from the other. … **Null intersections are then ignored.**

## ⚠️ 对派单建议刻画的纠正（★C 核对文献的结论）

派单建议「Adams 共识 = 保留在**每棵**输入树里都是 nested（两两包含或相离）的簇」。
**该刻画与文献不符、且恒真无信息量**：一棵树的簇集**本身**就是两两 nested 的
（这正是 `LaminarFamily` / `toRootedTreeOfCard` 的输入条件）。
文献的真实内容是上面引用的**递归 product-partition**（各树在 LUB 处分支划分的**共同细化**），
本文件按**文献**实现。

## 形式化接口（本库「有根树 = 镶嵌簇族」的约定）

本库把有根树表示为**镶嵌簇族** `F : Finset (Finset X)`（`LaminarFamily F`、`univ ∈ F`、成员非空；
见 `Phylo/Laminar.lean`），由 `Phylo.toRootedTreeOfCard`（`Laminar.lean:1794`）变成 `RootedTree`。
故本文件入口是 `F : ι → Finset (Finset X)`：第 `i` 棵输入树的簇族。

## 主要结果

* `lubCluster F S`：`F` 中含 `S` 的**最小**成员（`S` 的 LUB）；
* `branchPart F A`：`A` 的**分支划分**（孩子簇 ∪ 直接元素的单点）—— 「the partition …
  expressed by the branching at that node」；
* `adamsPartition par S`：**乘积划分**（各树分支划分的**共同细化**，空交自动忽略）；
* ★★★ `adamsClusters F S`：**Adams 共识簇族**（上述递归定义；`termination_by S.card`）；
* ★★ `mem_adamsClusters` / `adamsClusters_laminar` / `adamsClusters_subset`：
  簇族刻画、**镶嵌性**（= 「它是一棵树」的全部内容）、成员含于 `S`；
* ★★★ `adams_consensus_exists`：**Adams 共识树存在** —— 存在 `RootedTree X`，
  它**定向展示**（`IsSplitOf`）Adams 共识的每个非平凡簇；
* ★★ §8：`Fin 4`、两棵树的**最小具体例子**（乘积划分算出、含/不含实证、`Exists` 形态）。

## ⚠️ 边界与诚实说明

1. **`adamsClusters` 不需要镶嵌假设**（递归按 `S.card` 终止：乘积块 ⊆ `S` 且**排除** `= S` 的块，
   见 `adamsPartition_block_lt`）。镶嵌性只在**忠实性**上用：★★ `meetBlock_ne_self` 说明
   **输入是镶嵌族且 `2 ≤ |S|` 时，「块 = S」根本不会发生**（故排除操作不丢信息）。
   `hF`/`huniv` 参数只出现在 `adams_consensus_exists`（走 `normFinset` 建树时需要）。
2. **`[Nonempty ι]`**：`ι` 空时「product partition」退化为 `{S}`，被排除操作挡掉，
   共识退化为 `{univ}` —— 定义**仍终止**，但已无 Adams 意义；`meetBlock_ne_self` 显式要求 `[Nonempty ι]`。
3. **未做**（见 §9）：Adams 共识的**计数性质**、Adams 与严格共识的**一般**关系。
-/

open Phylo

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. LUB：含 `S` 的最小簇 -/

/-- **含 `S` 的最小族成员**（有根树中 `S` 的 LUB）：所有含 `S` 的成员之**交**。
镶嵌性保证这个交本身仍是族成员（`lubCluster_mem`）。 -/
noncomputable def lubCluster (F : Finset (Finset X)) (S : Finset X) : Finset X :=
  Finset.univ.filter fun x => ∀ A ∈ F, S ⊆ A → x ∈ A

theorem mem_lubCluster {F : Finset (Finset X)} {S : Finset X} {x : X} :
    x ∈ lubCluster F S ↔ ∀ A ∈ F, S ⊆ A → x ∈ A := by
  classical
  simp [lubCluster]

/-- `S ⊆ lubCluster F S`。 -/
theorem subset_lubCluster (F : Finset (Finset X)) (S : Finset X) : S ⊆ lubCluster F S :=
  fun _ hx => mem_lubCluster.mpr fun _ _ hSA => hSA hx

/-- `lubCluster F S` 含于**任何**含 `S` 的族成员（最小性）。 -/
theorem lubCluster_subset_of_mem {F : Finset (Finset X)} {S A : Finset X}
    (hA : A ∈ F) (hSA : S ⊆ A) : lubCluster F S ⊆ A :=
  fun _ hx => (mem_lubCluster.mp hx) A hA hSA

set_option maxHeartbeats 400000 in
/-- ★★ **`lubCluster F S` 是族成员**（镶嵌 + `univ ∈ F` + `S` 非空）。

取「含 `S` 的成员中**基数最小**者」`A₀`（用 `|X| - card` 的最大值实现最小化）；
镶嵌性使所有含 `S` 的成员两两可比，故 `A₀` 恰是它们的交，即 `lubCluster F S`。 -/
theorem lubCluster_mem (hl : LaminarFamily F) (huniv : (Finset.univ : Finset X) ∈ F)
    {S : Finset X} (hS : S.Nonempty) : lubCluster F S ∈ F := by
  classical
  have hne : (F.filter fun A => S ⊆ A).Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨huniv, Finset.subset_univ S⟩⟩
  obtain ⟨A₀, hA₀mem, hA₀min⟩ :=
    Finset.exists_mem_eq_sup (F.filter fun A => S ⊆ A) hne
      (fun A : Finset X => Fintype.card X - A.card)
  obtain ⟨hA₀F, hA₀S⟩ := Finset.mem_filter.mp hA₀mem
  have hmin : ∀ A ∈ F, S ⊆ A → A₀.card ≤ A.card := by
    intro A hAF hSA
    have hle := Finset.le_sup (s := F.filter fun B => S ⊆ B)
      (f := fun B : Finset X => Fintype.card X - B.card)
      (Finset.mem_filter.mpr ⟨hAF, hSA⟩)
    rw [hA₀min] at hle
    have h1 : A.card ≤ Fintype.card X := Finset.card_le_univ A
    have h2 : A₀.card ≤ Fintype.card X := Finset.card_le_univ A₀
    omega
  have hkey : lubCluster F S = A₀ := by
    refine Finset.Subset.antisymm (lubCluster_subset_of_mem hA₀F hA₀S) ?_
    intro x hx
    rw [mem_lubCluster]
    intro A hAF hSA
    rcases hl A hAF A₀ hA₀F with h1 | h1 | h1
    · have hle : A.card ≤ A₀.card := Finset.card_le_card h1
      have hge : A₀.card ≤ A.card := hmin A hAF hSA
      rw [Finset.eq_of_subset_of_card_le h1 (by omega)]
      exact hx
    · exact h1 hx
    · exfalso
      rw [Finset.disjoint_iff_inter_eq_empty] at h1
      obtain ⟨t, ht⟩ := hS
      have ht' : t ∈ A ∩ A₀ := Finset.mem_inter.mpr ⟨hSA ht, hA₀S ht⟩
      rw [h1] at ht'
      exact Finset.notMem_empty t ht'
  rw [hkey]
  exact hA₀F

/-- LUB 下**没有孩子簇含 `S`**（否则该孩子是更小的、含 `S` 的族成员）。 -/
theorem not_subset_of_isChildOf_lub {F : Finset (Finset X)} {S C : Finset X}
    (hC : IsChildOf F (lubCluster F S) C) : ¬ (S ⊆ C) := by
  intro hSC
  exact hC.2.1.2 (lubCluster_subset_of_mem hC.1 hSC)

/-! ## 2. 分支划分（Adams 的「LUB 处的分支」） -/

/-- `IsChildOf` 的**可计算**可判定性（用 `ssubset_iff_subset_ne` 把 `⊂` 化为 `⊆ ∧ ≠`）。

有了它 `branchPart`（以及依赖它的 `lubBranchPart` / `adamsPartition`）**保持可计算**，
故 §7 的具体例子可以用 `decide` 判定。 -/
instance instDecidablePredIsChildOf (F : Finset (Finset X)) (A : Finset X) :
    DecidablePred (fun C => IsChildOf F A C) :=
  fun C => decidable_of_iff
    (C ∈ F ∧ (C ⊆ A ∧ C ≠ A) ∧ ∀ D ∈ F, (C ⊆ D ∧ C ≠ D) → ¬ (D ⊆ A ∧ D ≠ A))
    (by simp only [IsChildOf, Finset.ssubset_iff_subset_ne])

/-- `Finset` 的 `⊆` 的**可计算**可判定性（`subset_iff` + 有界量化）。

有了它 `LaminarFamily`（含 `⊆` 与 `Disjoint`）在具体实例上可用 `decide` 判定。 -/
instance instDecidableSubsetFinset (s t : Finset X) : Decidable (s ⊆ t) :=
  decidable_of_iff (∀ a ∈ s, a ∈ t) (by rw [Finset.subset_iff])

/-- **`A` 的分支划分**：`A` 的**孩子簇** ∪ 挂在 `A` 上的**直接元素**的单点集。

这是有根树在顶点 `A` 处的分支（Adams 1972：「the partition of that set expressed by the
branching at that node」）：`A` 的每个后代叶恰落在唯一一个分支里。 -/
noncomputable def branchPart (F : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  (F.filter fun C => IsChildOf F A C) ∪ (directElems F A).image (fun x => ({x} : Finset X))

theorem mem_branchPart {F : Finset (Finset X)} {A C : Finset X} :
    C ∈ branchPart F A ↔
      (C ∈ F ∧ IsChildOf F A C) ∨ (∃ x ∈ directElems F A, C = {x}) := by
  classical
  simp only [branchPart, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  tauto

/-- **`S` 在 `F` 中的分支划分**（先取 LUB）。 -/
noncomputable def lubBranchPart (F : Finset (Finset X)) (S : Finset X) : Finset (Finset X) :=
  branchPart F (lubCluster F S)

/-- ★★ **LUB 的每个元素都落在至少一个分支块里**：孩子簇或直接元素单点。
这是「分支划分**是** LUB 的一个划分」的存在性一半。 -/
theorem exists_mem_lubBranchPart {F : Finset (Finset X)} (hl : LaminarFamily F)
    (huniv : (Finset.univ : Finset X) ∈ F) {S : Finset X} (hS : S.Nonempty)
    {x : X} (hx : x ∈ lubCluster F S) : ∃ C ∈ lubBranchPart F S, x ∈ C := by
  classical
  have hlub : lubCluster F S ∈ F := lubCluster_mem hl huniv hS
  by_cases hd : x ∈ directElems F (lubCluster F S)
  · refine ⟨{x}, ?_, Finset.mem_singleton_self x⟩
    simp only [lubBranchPart, mem_branchPart]
    exact Or.inr ⟨x, hd, rfl⟩
  · obtain ⟨B, hBF, hxB, hBA⟩ := exists_ssubset_of_not_mem_directElems hl hlub hx hd
    obtain ⟨C, hC, hxC⟩ := exists_isChildOf_mem (F := F) ⟨B, hBF, hxB, hBA⟩
    refine ⟨C, ?_, hxC⟩
    simp only [lubBranchPart, mem_branchPart]
    exact Or.inl ⟨hC.1, hC⟩

/-! ## 3. 乘积划分（product partition） -/

/-- **`x` 的 meet 块**：与 `x` 在**每棵树的每个分支块**里同进同出的 `S` 的元素。

即 Adams 的「one for each intersection of a group from one tree and a group from the other」：
各树分支划分的**共同细化**块。 -/
noncomputable def meetBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (par : ι → Finset (Finset X)) (S : Finset X) (x : X) : Finset X :=
  S.filter fun y => ∀ i, ∀ C ∈ par i, (x ∈ C ↔ y ∈ C)

theorem mem_meetBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    {par : ι → Finset (Finset X)} {S : Finset X} {x y : X} :
    y ∈ meetBlock par S x ↔ y ∈ S ∧ ∀ i, ∀ C ∈ par i, (x ∈ C ↔ y ∈ C) := by
  classical
  simp [meetBlock]

theorem meetBlock_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (par : ι → Finset (Finset X)) (S : Finset X) (x : X) : meetBlock par S x ⊆ S :=
  fun _ hy => (mem_meetBlock.mp hy).1

/-- ★★ **Adams 的乘积划分**：各树分支划分的**共同细化**。

空交自动忽略：块只对 `x ∈ S` 取（`S.image`），而块内必含 `x`，故块非空。 -/
noncomputable def adamsPartition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (par : ι → Finset (Finset X)) (S : Finset X) : Finset (Finset X) :=
  S.image fun x => meetBlock par S x

theorem mem_adamsPartition {ι : Type*} [Fintype ι] [DecidableEq ι]
    {par : ι → Finset (Finset X)} {S B : Finset X} :
    B ∈ adamsPartition par S ↔ ∃ x ∈ S, meetBlock par S x = B := by
  classical
  simp [adamsPartition]

theorem adamsPartition_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {par : ι → Finset (Finset X)} {S B : Finset X} (hB : B ∈ adamsPartition par S) :
    B ⊆ S := by
  obtain ⟨x, -, rfl⟩ := mem_adamsPartition.mp hB
  exact meetBlock_subset par S x

/-- ★★ **乘积划分的块两两相等或相离**（它确实是 `S` 的一个划分）。 -/
theorem adamsPartition_eq_or_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {par : ι → Finset (Finset X)} {S B B' : Finset X}
    (hB : B ∈ adamsPartition par S) (hB' : B' ∈ adamsPartition par S)
    (hne : (B ∩ B').Nonempty) : B = B' := by
  classical
  obtain ⟨x, -, rfl⟩ := mem_adamsPartition.mp hB
  obtain ⟨x', -, rfl⟩ := mem_adamsPartition.mp hB'
  obtain ⟨z, hz⟩ := hne
  rw [Finset.mem_inter] at hz
  have hzx := (mem_meetBlock.mp hz.1).2
  have hzx' := (mem_meetBlock.mp hz.2).2
  ext y
  rw [mem_meetBlock, mem_meetBlock]
  constructor
  · rintro ⟨hyS, hy⟩
    exact ⟨hyS, fun i C hC => (hzx' i C hC).trans ((hzx i C hC).symm.trans (hy i C hC))⟩
  · rintro ⟨hyS, hy⟩
    exact ⟨hyS, fun i C hC => (hzx i C hC).trans ((hzx' i C hC).symm.trans (hy i C hC))⟩

/-- ★★ **乘积块是 `S` 的真子集**（只要它不是 `S` 自己）—— 递归的终止性来源。 -/
theorem adamsPartition_block_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {par : ι → Finset (Finset X)} {S B : Finset X}
    (hB : B ∈ adamsPartition par S) (hne : B ≠ S) : B.card < S.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨adamsPartition_subset hB, hne⟩)

/-- ★★★ **镶嵌输入下「块 = `S`」不会发生**（`2 ≤ |S|`、`ι` 非空）——
即乘积划分真的把 `S` 拆细，递归不丢信息，`adamsClusters` 的排除操作是**空操作**。

若某块 `= S`，取 `y₀ ∈ S`：`y₀` 落在 LUB 的某个分支块 `C₀` 里，于是由 meet 条件 `S ⊆ C₀`。
但 `C₀` 只能是**孩子簇**（与 `not_subset_of_isChildOf_lub` 矛盾）
或**直接元素的单点**（则 `|S| ≤ 1`，与 `2 ≤ |S|` 矛盾）。 -/
theorem meetBlock_ne_self {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → Finset (Finset X)) (hF : ∀ i, LaminarFamily (F i))
    (huniv : ∀ i, (Finset.univ : Finset X) ∈ F i)
    {S : Finset X} (hS : 2 ≤ S.card) (x : X) :
    meetBlock (fun i => lubBranchPart (F i) S) S x ≠ S := by
  classical
  intro hEq
  obtain ⟨y₀, hy₀S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hmem : ∀ y ∈ S, ∀ i, ∀ C ∈ lubBranchPart (F i) S, (x ∈ C ↔ y ∈ C) := by
    intro y hy i C hC
    have hy' : y ∈ meetBlock (fun i => lubBranchPart (F i) S) S x := by rw [hEq]; exact hy
    exact (mem_meetBlock.mp hy').2 i C hC
  have hy₀lub : y₀ ∈ lubCluster (F i₀) S := subset_lubCluster (F i₀) S hy₀S
  obtain ⟨C₀, hC₀mem, hy₀C₀⟩ :=
    exists_mem_lubBranchPart (hF i₀) (huniv i₀) ⟨y₀, hy₀S⟩ hy₀lub
  have hxC₀ : x ∈ C₀ := (hmem y₀ hy₀S i₀ C₀ hC₀mem).mpr hy₀C₀
  have hSC₀ : S ⊆ C₀ := fun y hy => (hmem y hy i₀ C₀ hC₀mem).mp hxC₀
  rcases (mem_branchPart.mp hC₀mem) with ⟨-, hchild⟩ | ⟨z, -, hC₀eq⟩
  · exact not_subset_of_isChildOf_lub hchild hSC₀
  · rw [hC₀eq] at hSC₀
    have h1 : S.card ≤ 1 := by
      have h2 := Finset.card_le_card hSC₀
      simpa using h2
    omega

/-! ## 4. Adams 共识（递归定义，Adams 1972 第 481–496 行） -/

omit [Fintype X] in
/-- `P.attach.biUnion` 的成员判定（把 subtype 上的 biUnion 拉回原集合）。 -/
theorem mem_attach_biUnion {P : Finset (Finset X)} {f : Finset X → Finset (Finset X)}
    {A : Finset X} : A ∈ P.attach.biUnion (fun B => f B.1) ↔ ∃ B ∈ P, A ∈ f B := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨b, -, hb⟩
    exact ⟨b.1, b.2, hb⟩
  · rintro ⟨B, hB, hB'⟩
    exact ⟨⟨B, hB⟩, by simp, hB'⟩

/-- ★★★ **Adams 共识的簇族**（Adams 1972 第 481–496 行的递归定义）。

* 节点 `S` 自己是一个簇；
* 外加**乘积划分**的每个「不等于 `S`」的块的 Adams 共识。

「`≠ S`」对应文献的「**null intersections are then ignored**」与「块真细化 `S`」：
在镶嵌输入且 `2 ≤ |S|` 时该条件自动成立（★★ `meetBlock_ne_self`），故不丢簇；
`|S| ≤ 1` 时 `S` 的块就是 `S` 自己，被排除，于是递归停在 `{S}` —— 正是文献的基例。

**终止性**：块 ⊆ `S` 且 ≠ `S` ⟹ 基数为真减（`adamsPartition_block_lt`），按 `S.card` 递归。 -/
noncomputable def adamsClusters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) (S : Finset X) : Finset (Finset X) :=
  {S} ∪ ((adamsPartition (fun i => lubBranchPart (F i) S) S).filter
        (fun B => B ≠ S)).attach.biUnion (fun B => adamsClusters F B.1)
termination_by S.card
decreasing_by
  have hB : B.1 ∈ adamsPartition (fun i => lubBranchPart (F i) S) S :=
    (Finset.mem_filter.mp B.2).1
  have hne : B.1 ≠ S := (Finset.mem_filter.mp B.2).2
  exact adamsPartition_block_lt hB hne

/-- ★★ **Adams 簇的刻画**：`A` 是 `S` 处的簇 ⟺ `A = S`，或 `A` 是某个（≠ `S` 的）
乘积块的 Adams 簇。 -/
theorem mem_adamsClusters {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Finset (Finset X)} {S A : Finset X} :
    A ∈ adamsClusters F S ↔ A = S ∨
      ∃ B ∈ adamsPartition (fun i => lubBranchPart (F i) S) S,
        B ≠ S ∧ A ∈ adamsClusters F B := by
  rw [adamsClusters.eq_def]
  simp only [Finset.mem_union, Finset.mem_singleton, mem_attach_biUnion, Finset.mem_filter]
  tauto

/-! ## 5. 镶嵌性与「含于 `S`」 -/

set_option maxHeartbeats 800000 in
/-- ★★★ **Adams 簇族镶嵌，且成员含于 `S`**（按 `|S|` 强归纳；**无需**镶嵌假设）。

两个簇若相交：若来自同一乘积块，用归纳假设；若来自不同块，块相离
（`adamsPartition_eq_or_disjoint`）；若其一为 `S`，由「成员含于 `S`」立得。 -/
theorem adamsClusters_laminar_and_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) :
    ∀ S : Finset X, LaminarFamily (adamsClusters F S) ∧
      ∀ A ∈ adamsClusters F S, A ⊆ S := by
  classical
  suffices h : ∀ n, ∀ S : Finset X, S.card ≤ n →
      LaminarFamily (adamsClusters F S) ∧ ∀ A ∈ adamsClusters F S, A ⊆ S by
    exact fun S => h S.card S le_rfl
  intro n
  induction n with
  | zero =>
      -- `|S| = 0`：乘积划分必空（否则块 ⊆ `S` 且 ≠ `S` 而基数相等），故簇族 = `{S}`
      intro S hS
      have aux : ∀ B, B ∈ adamsPartition (fun i => lubBranchPart (F i) S) S → B ≠ S → False := by
        intro B hB hBne
        have h1 : B ⊆ S := adamsPartition_subset hB
        have h2 : B.card ≤ S.card := Finset.card_le_card h1
        exact hBne (Finset.eq_of_subset_of_card_le h1 (by omega))
      refine ⟨?_, ?_⟩
      · intro A hA A' hA'
        rcases (mem_adamsClusters.mp hA) with h | ⟨B, hB, hBne, -⟩
        · rcases (mem_adamsClusters.mp hA') with h' | ⟨B', hB', hB'ne, -⟩
          · rw [h, h']; exact Or.inl (Finset.Subset.refl S)
          · exact (aux B' hB' hB'ne).elim
        · exact (aux B hB hBne).elim
      · intro A hA
        rcases (mem_adamsClusters.mp hA) with h | ⟨B, hB, hBne, -⟩
        · rw [h]
        · exact (aux B hB hBne).elim
  | succ n ih =>
      intro S hS
      have hsub : ∀ A ∈ adamsClusters F S, A ⊆ S := by
        intro A hA
        rcases (mem_adamsClusters.mp hA) with hAeq | ⟨B, hB, hBne, hAB⟩
        · rw [hAeq]
        · have hBS : B ⊆ S := adamsPartition_subset hB
          have hBlt : B.card ≤ n := by
            have := adamsPartition_block_lt hB hBne
            omega
          exact ((ih B hBlt).2 A hAB).trans hBS
      refine ⟨?_, hsub⟩
      intro A hA A' hA'
      by_cases hne : (A ∩ A').Nonempty
      · rcases (mem_adamsClusters.mp hA) with hAeq | ⟨B, hB, hBne, hAB⟩
        · rw [hAeq]
          exact Or.inr (Or.inl (hsub A' hA'))
        · rcases (mem_adamsClusters.mp hA') with hA'eq | ⟨B', hB', hB'ne, hA'B'⟩
          · rw [hA'eq]
            exact Or.inl (hsub A hA)
          · have hBlt : B.card ≤ n := by
              have := adamsPartition_block_lt hB hBne
              omega
            have hB'lt : B'.card ≤ n := by
              have := adamsPartition_block_lt hB' hB'ne
              omega
            rcases eq_or_ne B B' with hBB | hBB
            · rw [← hBB] at hA'B'
              exact (ih B hBlt).1 A hAB A' hA'B'
            · have hdisj : Disjoint B B' := by
                rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
                intro hcon
                exact hBB (adamsPartition_eq_or_disjoint hB hB' hcon)
              exact Or.inr (Or.inr (Disjoint.mono ((ih B hBlt).2 A hAB)
                ((ih B' hB'lt).2 A' hA'B') hdisj))
      · exact Or.inr (Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hne)))

/-- ★★★ **Adams 簇族的镶嵌性**（= 「它是一棵树」的全部组合内容）。 -/
theorem adamsClusters_laminar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) (S : Finset X) :
    LaminarFamily (adamsClusters F S) :=
  (adamsClusters_laminar_and_subset F S).1

/-- ★★ **Adams 簇族的成员含于 `S`**。 -/
theorem adamsClusters_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) (S : Finset X) :
    ∀ A ∈ adamsClusters F S, A ⊆ S :=
  (adamsClusters_laminar_and_subset F S).2

/-- ★★ **`S` 自己的簇总在 Adams 共识里**（递归的根）。 -/
theorem self_mem_adamsClusters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) (S : Finset X) : S ∈ adamsClusters F S :=
  mem_adamsClusters.mpr (Or.inl rfl)

theorem univ_mem_adamsClusters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) :
    (Finset.univ : Finset X) ∈ adamsClusters F Finset.univ :=
  self_mem_adamsClusters F Finset.univ

/-! ## 6. Adams 共识树存在 -/

/-- 由簇 `A` 与它的补构成的 split（`A ≠ univ` 保证补非空）。 -/
noncomputable def clusterSplit (A : Finset X) (hAne : A ≠ Finset.univ) (hAcard : 2 ≤ A.card) :
    Split X :=
  splitOf A (Finset.card_pos.mp (by omega)) (compl_nonempty_of_ne_univ hAne)

@[simp] theorem clusterSplit_sideA {A : Finset X} (hAne : A ≠ Finset.univ) (hAcard : 2 ≤ A.card) :
    (clusterSplit A hAne hAcard).sideA = A :=
  splitOf_sideA ..

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
/-- ★★★ **Adams 共识树存在**（Adams 1972；镶嵌 ⟹ 树）。

设 `F : ι → Finset (Finset X)` 是 `ι` 棵有根树的簇族（镶嵌、含 `univ`、成员非空可由
`2 ≤ |X|` 与正规化保证），则存在有根树 `T`（`RootedTree X`），它**定向展示**
（`IsSplitOf`，不换向）Adams 共识的**每个非平凡簇**：

    `∀ A ∈ adamsClusters F univ, A ≠ univ → 2 ≤ |A| → T.IsSplitOf (clusterSplit A …)`。

**证明**：`adamsClusters_laminar` 给镶嵌、`univ_mem_adamsClusters` 给根；
`normFinset` 正规化后用 `toRootedTreeOfCard` 建树，
`leafSide_parentEdge_of_card` 说明每个非 `univ` 成员都是某条边的叶侧。 -/
theorem adams_consensus_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Finset (Finset X)) (hF : ∀ i, LaminarFamily (F i))
    (huniv : ∀ i, (Finset.univ : Finset X) ∈ F i) (h2 : 2 ≤ Fintype.card X) :
    ∃ T : RootedTree.{u, u} X, ∀ (A : Finset X) (_ : A ∈ adamsClusters F Finset.univ)
      (hAne : A ≠ Finset.univ) (hAc : 2 ≤ A.card),
      T.IsSplitOf (clusterSplit A hAne hAc) := by
  classical
  set G : Finset (Finset X) := normFinset (adamsClusters F Finset.univ) with hG
  have hl : LaminarFamily (adamsClusters F Finset.univ) := adamsClusters_laminar F Finset.univ
  have hl' : LaminarFamily G := by rw [hG]; exact laminarFamily_normFinset hl
  have huniv' : (Finset.univ : Finset X) ∈ G := by rw [hG]; exact univ_mem_normFinset
  have hcard' : ∀ B ∈ G, B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rw [hG, mem_normFinset] at hB
    rcases hB with h | h
    · exact Or.inl h
    · exact Or.inr h.2
  have hne' : ∀ B ∈ G, B.Nonempty := nonempty_of_mem_of_hcard hcard' h2
  refine ⟨toRootedTreeOfCard hl' huniv' hcard' h2, ?_⟩
  intro A hA hAne hAc
  have hAG : A ∈ G := by
    rw [hG, mem_normFinset]
    exact Or.inr ⟨hA, hAc⟩
  have hleaf : leafSide G (parentEdge hl' hne' huniv' A hAG hAne)
      (Sum.inl (⟨A, hAG⟩ : ↥G)) = A :=
    leafSide_parentEdge_of_card hl' huniv' hcard' h2 hAG hAne
  refine ⟨Sum.inl (⟨A, hAG⟩ : ↥G),
    Sum.inl (parentV hl' hne' huniv' (⟨A, hAG⟩ : ↥G) hAne), ?_,
    Sum.inl (⟨A, hAG⟩ : ↥G), ?_⟩
  · rw [toRootedTreeOfCard_graph]
    exact (treeGraph_adj_inl_inl G ⟨A, hAG⟩
      (parentV hl' hne' huniv' (⟨A, hAG⟩ : ↥G) hAne)).mpr
      (Or.inl (isParentOf_parentOf (A := A) hl' hne' huniv' hAG hAne))
  · show (clusterSplit A hAne hAc).sideA
      = leafSide G s(Sum.inl (⟨A, hAG⟩ : ↥G),
          Sum.inl (parentV hl' hne' huniv' (⟨A, hAG⟩ : ↥G) hAne)) (Sum.inl (⟨A, hAG⟩ : ↥G))
    rw [clusterSplit_sideA]
    exact hleaf.symm

/-! ## 7. 反空真（★C）：最小具体例子上端到端

`X = Fin 4`，两棵有根树（簇族形式）：

* 树 1：`((0,1),(2,3))` —— `F₁ = {univ, {0,1}, {2,3}}`；
* 树 2：`((0,1),2,3)` —— `F₂ = {univ, {0,1}}`。

**手算 Adams 共识**（Adams 1972 第 481–496 行）：

| 步骤 | 树 1 | 树 2 |
|---|---|---|
| `S = univ` 的 LUB | `univ` | `univ` |
| 分支划分 | `{{0,1},{2,3}}` | `{{0,1},{2},{3}}` |

乘积划分 = 所有交，空交忽略：
`{0,1}∩{0,1}={0,1}`、`{0,1}∩{2}=∅`、`{0,1}∩{3}=∅`、`{2,3}∩{0,1}=∅`、
`{2,3}∩{2}={2}`、`{2,3}∩{3}={3}` ⟹ 块 `{0,1}, {2}, {3}`。
再在 `{0,1}` 上递归：两树 LUB 都是 `{0,1}`，分支划分都是 `{{0},{1}}` ⟹ 块 `{0},{1}`。

⇒ **Adams 共识簇族** = `{univ, {0,1}, {2}, {3}}`。
✅ **`{0,1}` 在**（两树共同的樱花）；✅ **`{2,3}` 不在**（只在树 1 里）。

下面把乘积划分**算出**，并实证含/不含（`decide` 可判的小有限集）。 -/

/-- 例子用的叶集 `X = Fin 4`。 -/
abbrev ExX := Fin 4

/-- 树 1 的簇族 `F₁ = {univ, {0,1}, {2,3}}`。 -/
def exF₁ : Finset (Finset ExX) := {Finset.univ, {0, 1}, {2, 3}}

/-- 树 2 的簇族 `F₂ = {univ, {0,1}}`。 -/
def exF₂ : Finset (Finset ExX) := {Finset.univ, {0, 1}}

theorem exF₁_laminar : LaminarFamily exF₁ := by
  intro A hA B hB
  fin_cases hA <;> fin_cases hB <;>
    first
      | exact Or.inl (Finset.subset_univ _)
      | exact Or.inl (Finset.Subset.refl _)
      | exact Or.inr (Or.inl (Finset.subset_univ _))
      | exact Or.inr (Or.inr (by rw [Finset.disjoint_iff_inter_eq_empty]; decide))

theorem exF₂_laminar : LaminarFamily exF₂ := by
  intro A hA B hB
  fin_cases hA <;> fin_cases hB <;>
    first
      | exact Or.inl (Finset.subset_univ _)
      | exact Or.inl (Finset.Subset.refl _)
      | exact Or.inr (Or.inl (Finset.subset_univ _))

/-- 两棵树的簇族族 `Fin 2 → Finset (Finset ExX)`。 -/
def exFam : Fin 2 → Finset (Finset ExX) := fun i => if i = 0 then exF₁ else exF₂

theorem exFam_laminar : ∀ i, LaminarFamily (exFam i) := by
  intro i
  fin_cases i
  · exact exF₁_laminar
  · exact exF₂_laminar

theorem exFam_univ : ∀ i, (Finset.univ : Finset ExX) ∈ exFam i := by
  intro i
  fin_cases i <;> decide

/-- ★★ **最小例子的乘积划分算出来**：`univ` 处的乘积划分恰是 `{{0,1},{2},{3}}`。 -/
theorem ex_adamsPartition :
    adamsPartition (fun i => lubBranchPart (exFam i) (Finset.univ : Finset ExX))
      (Finset.univ : Finset ExX) = ({{0, 1}, {2}, {3}} : Finset (Finset ExX)) := by
  decide

/-- ★★ **反空真**：最小例子的 Adams 共识含**非平凡**簇 `{0,1}`（不是「只有 `univ`」）。 -/
theorem ex_adamsClusters_mem :
    ({0, 1} : Finset ExX) ∈ adamsClusters exFam Finset.univ := by
  rw [mem_adamsClusters]
  exact Or.inr ⟨{0, 1}, by rw [ex_adamsPartition]; decide, by decide,
    self_mem_adamsClusters exFam {0, 1}⟩

/-- ★★★ **最小例子区分 Adams 与「并集」**：`{2,3}` 只在树 1 里，**不**在 Adams 共识中。
（结合 `ex_adamsClusters_mem`，非平凡簇恰是 `{0,1}`。） -/
theorem ex_adamsClusters_not_mem :
    ({2, 3} : Finset ExX) ∉ adamsClusters exFam Finset.univ := by
  rw [mem_adamsClusters]
  rintro (h | ⟨B, hB, -, hAB⟩)
  · exact absurd h (by decide)
  · have hsub : ({2, 3} : Finset ExX) ⊆ B := adamsClusters_subset exFam B _ hAB
    rw [ex_adamsPartition] at hB
    fin_cases hB
    · exact absurd (hsub (show (2 : ExX) ∈ ({2, 3} : Finset ExX) by decide)) (by decide)
    · have hc : (2 : ℕ) ≤ 1 := Finset.card_le_card hsub
      omega
    · have hc : (2 : ℕ) ≤ 1 := Finset.card_le_card hsub
      omega

/-- ★★★ **最小例子上端到端**：真的造出一棵展示 Adams 共识全部非平凡簇的有根树。 -/
theorem ex_adams_consensus_exists :
    ∃ T : RootedTree.{0, 0} ExX, ∀ (A : Finset ExX) (_ : A ∈ adamsClusters exFam Finset.univ)
      (hAne : A ≠ Finset.univ) (hAc : 2 ≤ A.card),
      T.IsSplitOf (clusterSplit A hAne hAc) :=
  adams_consensus_exists exFam exFam_laminar exFam_univ (by decide)

/-! ## 8. 显式缺口

1. **Adams 共识的计数性质**（如「Adams 共识至多和每棵输入树一样精细」、
   `|adamsClusters| ≤ |F i|` 之类）**未做**：需要簇族间的基数比较层。
2. **Adams 与严格共识的**一般**关系**（哪个包含哪个、一般不等）**未做**；
   本文件只有最小例子的实证（`ex_adamsClusters_mem` / `ex_adamsClusters_not_mem`）。
3. **`clustersOf` ↔ `adamsClusters` 的桥**只做了单向（`toRootedTreeOfCard` 方向）；
   「从 `RootedTree` 取出簇族再喂给 `adamsClusters`」这一层未接。
4. **`k ≥ 3` 棵树的例子**未做（最小例子只到 2 棵树）。
-/
