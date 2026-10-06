/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Phylo.Core
import Phylo.Mathlib.Walk

/-!
# `Phylo.Split` —— 划分族与 split（M2 地基）

`CONCEPTS.md` §3.4 决策：建「**划分族**」——

* `KPartition α n` —— 一般 `n`-块划分，作**共享基础**；
* `Split α := KPartition α 2` —— 二分，单独立**专用 API**（兼容性 / Buneman 压在它上面）；
* `Tripartition` / `Quadripartition` 各语义化定义（蓝图 ASTRAL 用），**不硬塞进 `kPartition`**。

⚠️ 命名：叫 `KPartition` 而非 `Partition` —— Mathlib 已有 `Partition α`（`Set (Set α)`，**任意多块**），
两者同名不同物，`open` 即撞。
-/

variable {α : Type*}

/-! ## 自建小引理（Mathlib 缺；将来可迁入 `Phylo/Mathlib/`） -/

/-- **孤立点只与自身可达**。 -/
theorem reachable_eq_of_isIsolated {V : Type*} {G : SimpleGraph V} {a u : V}
    (h : G.IsIsolated a) (hr : G.Reachable a u) : u = a := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ _ => exact absurd hadj (h _)

/-- **两侧的相容性**（§3.4：相容 ⟺ 一侧包含另一侧，或互补）。

不依赖 `Split` 结构 —— 便于先在树上证明，再经 `Split.compatible_of_sides` 抬到 `Split`。 -/
def SidesCompatible {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = Finset.univ

/-- **相容性对补侧不变**（四项恰好对应轮换）：
`Aᶜ ⊆ B ↔ A ∪ B = univ`、`B ⊆ Aᶜ ↔ Disjoint A B`、`Disjoint Aᶜ B ↔ B ⊆ A`、`Aᶜ ∪ B = univ ↔ A ⊆ B`。

这条让「情形 2」可以整体换到**补侧**处理。 -/
theorem sidesCompatible_compl_left {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} : SidesCompatible Aᶜ B ↔ SidesCompatible A B := by
  have h1 : Aᶜ ⊆ B ↔ A ∪ B = Finset.univ := by
    constructor
    · intro h
      ext x
      refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
      by_cases hx : x ∈ A
      · exact Finset.mem_union.mpr (Or.inl hx)
      · exact Finset.mem_union.mpr (Or.inr (h (by simpa using hx)))
    · intro h x hx
      rcases Finset.mem_union.mp (by rw [h]; exact Finset.mem_univ x) with h' | h'
      · exact absurd h' (by simpa using hx)
      · exact h'
  have h2 : B ⊆ Aᶜ ↔ Disjoint A B := by
    rw [Finset.disjoint_left]
    constructor
    · intro h x hA hB
      have hx := h hB
      simp only [Finset.mem_compl] at hx
      exact hx hA
    · intro h x hx
      simp only [Finset.mem_compl]
      exact fun hA => h hA hx
  have h3 : Disjoint Aᶜ B ↔ B ⊆ A := by
    rw [Finset.disjoint_left]
    constructor
    · intro h x hx
      by_contra hA
      have hx' := h (by simpa [Finset.mem_compl] using hA)
      exact hx' hx
    · intro h x hx hB
      have hx' := hx
      simp only [Finset.mem_compl] at hx'
      exact hx' (h hB)
  have h4 : Aᶜ ∪ B = Finset.univ ↔ A ⊆ B := by
    constructor
    · intro h x hx
      rcases Finset.mem_union.mp (by rw [h]; exact Finset.mem_univ x) with h' | h'
      · exact absurd hx (by simpa using h')
      · exact h'
    · intro h
      ext x
      refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
      by_cases hx : x ∈ A
      · exact Finset.mem_union.mpr (Or.inr (h hx))
      · exact Finset.mem_union.mpr (Or.inl (by simpa using hx))
  simp only [SidesCompatible]
  constructor <;> intro h <;> rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (h1.mp h)))
  · exact Or.inr (Or.inr (Or.inl (h2.mp h)))
  · exact Or.inr (Or.inl (h3.mp h))
  · exact Or.inl (h4.mp h)
  · exact Or.inr (Or.inr (Or.inr (h4.mpr h)))
  · exact Or.inr (Or.inr (Or.inl (h3.mpr h)))
  · exact Or.inr (Or.inl (h2.mpr h))
  · exact Or.inl (h1.mpr h)

/-- **相容性对称**。 -/
theorem sidesCompatible_comm {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} : SidesCompatible A B ↔ SidesCompatible B A := by
  constructor <;> intro h <;> rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl (disjoint_comm.mpr h)))
  · exact Or.inr (Or.inr (Or.inr (by rw [Finset.union_comm]; exact h)))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl (disjoint_comm.mpr h)))
  · exact Or.inr (Or.inr (Or.inr (by rw [Finset.union_comm]; exact h)))

/-- **相容性对第二侧的补不变**。 -/
theorem sidesCompatible_compl_right {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} : SidesCompatible A Bᶜ ↔ SidesCompatible A B :=
  sidesCompatible_comm.trans (sidesCompatible_compl_left.trans sidesCompatible_comm)

/-- **相容 + 避开 `ρ` ⟹ 嵌套或相离**（四种情形中「并 = 全集」被排除）。

这是「相容 ⟹ 存在树」的关键化简：**树构造只需处理镶嵌族**。 -/
theorem laminar_of_sidesCompatible_of_notMem {α : Type*} [Fintype α] [DecidableEq α]
    {ρ : α} {A B : Finset α} (h : SidesCompatible A B) (hA : ρ ∉ A) (hB : ρ ∉ B) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    have : ρ ∈ A ∪ B := h ▸ Finset.mem_univ ρ
    rcases Finset.mem_union.mp this with h' | h'
    · exact hA h'
    · exact hB h'

/-- **镶嵌族**：任意两个成员嵌套或相离（梯级树的组合骨架）。 -/
def LaminarFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- **两两相容族避开 `ρ` 后是镶嵌族** —— 「相容 ⟹ 存在树」的核心化简。 -/
theorem laminarFamily_of_pairwise {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Finset α)} {ρ : α}
    (h : ∀ A ∈ F, ∀ B ∈ F, SidesCompatible A B) (havoid : ∀ A ∈ F, ρ ∉ A) :
    LaminarFamily F :=
  fun A hA B hB => laminar_of_sidesCompatible_of_notMem (h A hA B hB) (havoid A hA) (havoid B hB)

/-- **`k`-块划分**：把 `α` 分成 `n` 个**两两不交、非空、并为全体**的块。

§3.4：这是「划分族」的共享基础。 -/
structure KPartition (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ) where
  /-- 第 `i` 块。 -/
  parts : Fin n → Finset α
  /-- 不同块两两不交。 -/
  pairwise_disjoint : ∀ i j : Fin n, i ≠ j → Disjoint (parts i) (parts j)
  /-- 所有块并为全集。 -/
  union_eq_univ : Finset.univ.biUnion parts = Finset.univ
  /-- 每块非空。 -/
  nonempty : ∀ i : Fin n, (parts i).Nonempty

/-- **split（二分）**：`KPartition` 在 `n = 2` 的特例。

§3.4：`Split` 单独立专用 API（兼容性判定 / Buneman 定理都压在它上面）。
底参数化在**任意类型** `α` 上 —— quartet 的配对是 `Split ↥S`（§3.5），离不开这一条。 -/
abbrev Split (α : Type*) [Fintype α] [DecidableEq α] := KPartition α 2

namespace Split

variable [Fintype α] [DecidableEq α]

/-- split 的第一侧（`Fin 2` 的 `0`）。 -/
def sideA (s : Split α) : Finset α := s.parts 0

/-- split 的第二侧（`Fin 2` 的 `1`）。 -/
def sideB (s : Split α) : Finset α := s.parts 1

/-- 两侧不交。 -/
theorem disjoint_sides (s : Split α) : Disjoint s.sideA s.sideB :=
  s.pairwise_disjoint 0 1 (by decide)

/-- 两侧并为全集。§3.4：`Fin 2` 索引把两侧有序化，判等需商掉 `swap`（见 `Split.swap`）。 -/
theorem union_sides (s : Split α) : s.sideA ∪ s.sideB = Finset.univ := by
  have h := s.union_eq_univ
  rw [← h]
  ext x
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, sideA, sideB]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi

/-- **相容（compatible）**：两个 split `A|B` 与 `A'|B'` 的四个交
`A∩A'`、`A∩B'`、`B∩A'`、`B∩B'` 中**至少一个为空**。

（文献：Semple & Steel；平凡 split 与任何 split 相容。） -/
def Compatible (s t : Split α) : Prop :=
  Disjoint s.sideA t.sideA ∨ Disjoint s.sideA t.sideB ∨
  Disjoint s.sideB t.sideA ∨ Disjoint s.sideB t.sideB

/-- 相容性对称。 -/
theorem compatible_comm (s t : Split α) : Compatible s t ↔ Compatible t s := by
  simp only [Compatible, disjoint_comm]
  tauto

/-- `sideB = univ \ sideA`（由「并 = 全集 + 不交」立得）。 -/
theorem sideB_eq_sdiff (s : Split α) : s.sideB = Finset.univ \ s.sideA := by
  ext x
  rw [Finset.mem_sdiff]
  constructor
  · intro hx
    refine ⟨Finset.mem_univ _, fun hA => ?_⟩
    exact (Finset.disjoint_left.mp s.disjoint_sides) hA hx
  · rintro ⟨_, hx⟩
    have h : x ∈ s.sideA ∪ s.sideB := by rw [s.union_sides]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp h with h' | h'
    · exact absurd h' hx
    · exact h'

/-- **一侧包含 ⟹ 相容**（`A ⊆ A'` 给出 `A ∩ B' = ∅`）。 -/
theorem compatible_of_subset_left {s t : Split α} (h : s.sideA ⊆ t.sideA) : Compatible s t := by
  refine Or.inr (Or.inl ?_)
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [t.sideB_eq_sdiff] at hx'
  exact (Finset.mem_sdiff.mp hx').2 (h hx)

/-- **一侧包含 ⟹ 相容**（`A' ⊆ A` 给出 `B ∩ A' = ∅`）。 -/
theorem compatible_of_subset_right {s t : Split α} (h : t.sideA ⊆ s.sideA) : Compatible s t := by
  refine Or.inr (Or.inr (Or.inl ?_))
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [s.sideB_eq_sdiff] at hx
  exact (Finset.mem_sdiff.mp hx).2 (h hx')

/-- **两侧不交 ⟹ 相容**。 -/
theorem compatible_of_disjoint {s t : Split α} (h : Disjoint s.sideA t.sideA) : Compatible s t :=
  Or.inl h

/-- **两侧并 = 全集 ⟹ 相容**（`B ∩ B' = ∅`）。 -/
theorem compatible_of_union {s t : Split α} (h : s.sideA ∪ t.sideA = Finset.univ) :
    Compatible s t := by
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [Finset.disjoint_left, s.sideB_eq_sdiff, t.sideB_eq_sdiff]
  intro x hx hy
  have hmem : x ∈ s.sideA ∪ t.sideA := by rw [h]; exact Finset.mem_univ x
  rcases Finset.mem_union.mp hmem with h' | h'
  · exact (Finset.mem_sdiff.mp hx).2 h'
  · exact (Finset.mem_sdiff.mp hy).2 h'

/-- **两侧相容 ⟹ 对应 split 相容**。 -/
theorem compatible_of_sides {s t : Split α}
    (h : SidesCompatible s.sideA t.sideA) : Compatible s t := by
  rcases h with h | h | h | h
  · exact compatible_of_subset_left h
  · exact compatible_of_subset_right h
  · exact compatible_of_disjoint h
  · exact compatible_of_union h

/-- `ρ` 恰在两侧之一。 -/
theorem mem_sideB_iff_not_mem_sideA (s : Split α) (ρ : α) : ρ ∈ s.sideB ↔ ρ ∉ s.sideA := by
  constructor
  · intro h h'
    exact (Finset.disjoint_left.mp s.disjoint_sides) h' h
  · intro h
    have hmem : ρ ∈ s.sideA ∪ s.sideB := by rw [s.union_sides]; exact Finset.mem_univ ρ
    rcases Finset.mem_union.mp hmem with h' | h'
    · exact absurd h' h
    · exact h'

/-- `sideB` 是 `sideA` 的补。 -/
theorem sideB_eq_compl (s : Split α) : s.sideB = s.sideAᶜ := s.sideB_eq_sdiff

/-- `Compatible` 的另一半：由相容性推出两侧相容（互补的两侧互相「让位」）。 -/
theorem sidesCompatible_of_compatible {s t : Split α} (h : Compatible s t) :
    SidesCompatible s.sideA t.sideA := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inl fun x hx => ?_
    by_contra hx'
    exact (Finset.disjoint_left.mp h) hx
      (by rw [t.sideB_eq_sdiff]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx'⟩)
  · refine Or.inr (Or.inl fun x hx => ?_)
    by_contra hx'
    exact (Finset.disjoint_left.mp h)
      (by rw [s.sideB_eq_sdiff]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx'⟩) hx
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext x
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    rcases Finset.mem_union.mp (by rw [s.union_sides]; exact Finset.mem_univ x) with h' | h'
    · exact Finset.mem_union.mpr (Or.inl h')
    · refine Finset.mem_union.mpr (Or.inr ?_)
      by_contra hx'
      exact (Finset.disjoint_left.mp h) h' ((Split.mem_sideB_iff_not_mem_sideA t x).mpr hx')

/-- **`Compatible` ⟺ 两侧相容**（两个方向都好用，是 cluster 化简的支点）。 -/
theorem compatible_iff_sides {s t : Split α} :
    Compatible s t ↔ SidesCompatible s.sideA t.sideA :=
  ⟨sidesCompatible_of_compatible, compatible_of_sides⟩

/-- **规范 cluster**：避开 `ρ` 的那一侧（每个 split 恰有一侧不含 `ρ`）。

这是「相容 ⟹ 存在树」里「选代表」的一步 —— 全部 cluster 都避开 `ρ`，于是两两镶嵌。 -/
noncomputable def cluster (s : Split α) (ρ : α) : Finset α :=
  if ρ ∈ s.sideA then s.sideB else s.sideA

/-- `cluster` 确实避开 `ρ`。 -/
theorem notMem_cluster (s : Split α) (ρ : α) : ρ ∉ s.cluster ρ := by
  unfold cluster
  split_ifs with h
  · intro hb
    exact ((s.mem_sideB_iff_not_mem_sideA ρ).mp hb) h
  · exact h

/-- `cluster` 要么是 `sideA`、要么是它的补。 -/
theorem cluster_eq_sideA_or_compl (s : Split α) (ρ : α) :
    s.cluster ρ = s.sideA ∨ s.cluster ρ = s.sideAᶜ := by
  unfold cluster
  split_ifs with h
  · exact Or.inr s.sideB_eq_compl
  · exact Or.inl rfl

/-- **相容 split 的规范 cluster 两两相容**（配合 `notMem_cluster` 立得镶嵌）。 -/
theorem sidesCompatible_cluster {s t : Split α} (h : Compatible s t) (ρ : α) :
    SidesCompatible (s.cluster ρ) (t.cluster ρ) := by
  have hbase : SidesCompatible s.sideA t.sideA := compatible_iff_sides.mp h
  rcases s.cluster_eq_sideA_or_compl ρ with hs | hs <;>
    rcases t.cluster_eq_sideA_or_compl ρ with ht | ht
  · rw [hs, ht]; exact hbase
  · rw [hs, ht]; exact sidesCompatible_compl_right.mpr hbase
  · rw [hs, ht]; exact sidesCompatible_compl_left.mpr hbase
  · rw [hs, ht]
    exact sidesCompatible_compl_right.mpr (sidesCompatible_compl_left.mpr hbase)

/-- 把 split 的第 `i` 侧限制到子集 `Y`（得到 `↥Y` 上的子集）。 -/
noncomputable def restrictSide (s : Split α) (Y : Finset α) (i : Fin 2) : Finset ↥Y :=
  Finset.univ.filter fun a => (a : α) ∈ s.parts i

/-- `restrictSide` 保持不交性。 -/
theorem disjoint_restrictSide (s : Split α) (Y : Finset α) :
    Disjoint (s.restrictSide Y 0) (s.restrictSide Y 1) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [restrictSide, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact (Finset.disjoint_left.mp s.disjoint_sides) ha hb

/-- **restriction（限制到 `Y`）**：`A|B ↦ (A∩Y)|(B∩Y)`。

§3.7 / Bryant–Steel、Semple & Steel §3.9：**restriction 的标准定义就在 split 层面**
（`Cl(T|Y) = {C∩Y : C ∈ Cl(T), C∩Y ≠ ∅}`），因此**不需要造新的树** —— 这正是选
route B 的收益。

（两侧各与 `Y` 相交非空的要求，作为假设传入；退化情形 `A∩Y=∅` 对应平凡 split。） -/
noncomputable def restrict (s : Split α) (Y : Finset α)
    (hA : (s.restrictSide Y 0).Nonempty) (hB : (s.restrictSide Y 1).Nonempty) :
    Split ↥Y where
  parts := fun i => s.restrictSide Y i
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact s.disjoint_restrictSide Y
    · exact disjoint_comm.mp (s.disjoint_restrictSide Y)
    · exact absurd rfl hij
  union_eq_univ := by
    ext a
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    have hmem : (a : α) ∈ s.sideA ∪ s.sideB := by
      rw [s.union_sides]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hmem with h | h
    · exact Finset.mem_biUnion.mpr ⟨0, by simpa [restrictSide, sideA] using h⟩
    · exact Finset.mem_biUnion.mpr ⟨1, by simpa [restrictSide, sideB] using h⟩
  nonempty := by
    intro i
    fin_cases i
    · simpa [restrictSide] using hA
    · simpa [restrictSide] using hB

/-- **交换两侧**。`Fin 2` 索引把两侧有序化，`swap` 给出反向 —— 判等需商掉它（§3.4）。

用 `i ↦ i + 1`（`Fin 2` 上的模 2 加法即对换）实现，避免 `Equiv` 带来的噪音。 -/
def swap (s : Split α) : Split α where
  parts := fun i => s.parts (i + 1)
  pairwise_disjoint := by
    intro i j hij
    refine s.pairwise_disjoint (i + 1) (j + 1) (fun h => hij ?_)
    revert h; fin_cases i <;> fin_cases j <;> simp
  union_eq_univ := by
    have h2 : ∀ i : Fin 2, (i + 1 : Fin 2) + 1 = i := by intro i; fin_cases i <;> rfl
    rw [← s.union_eq_univ]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i + 1, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i + 1, by rw [h2 i]; exact hi⟩
  nonempty := fun i => s.nonempty (i + 1)

/-- `swap` 把 `sideA` 与 `sideB` 对调。 -/
@[simp] theorem swap_sideA (s : Split α) : s.swap.sideA = s.sideB := rfl

@[simp] theorem swap_sideB (s : Split α) : s.swap.sideB = s.sideA := by
  show s.parts ((1 : Fin 2) + 1) = s.parts 0
  norm_num

end Split

/-! ## 树 → split 系统 -/

namespace Cladogram

open Classical
open SimpleGraph

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 删去边 `e` 后，与顶点 `u` **同侧**（在 `T - e` 中可达）的**叶集**。

§3.4：这是「删边 ⟹ bipartition」的直接实现。用 `Reachable` 表述，
以便接上 Mathlib 的 `IsBridge`（树中每条边都是桥）。 -/
noncomputable def sideLeaves (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : Finset X :=
  Finset.univ.filter fun x => (T.graph.deleteEdges {e}).Reachable (T.leaf x) u

/-- `sideLeaves` 的成员判定（定义展开）。 -/
theorem mem_sideLeaves (T : Cladogram X) {e : Sym2 T.V} {u : T.V} {x : X} :
    x ∈ T.sideLeaves e u ↔ (T.graph.deleteEdges {e}).Reachable (T.leaf x) u := by
  simp [sideLeaves]

/-- **树中每条边都是桥**：删去边 `⟦u,v⟧` 后，`u` 与 `v` 在 `T - e` 中不再可达。

（白蹭 Mathlib：`isAcyclic_iff_forall_adj_isBridge` + `isBridge_iff`。） -/
theorem not_reachable_deleteEdges_of_adj (T : Cladogram X) {u v : T.V}
    (h : T.graph.Adj u v) :
    ¬ (T.graph.deleteEdges {s(u, v)}).Reachable u v :=
  isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) h)

/-- 端点不在**对方**一侧（由「边是桥」立得）—— 边侧分离性的核心。 -/
theorem not_mem_sideLeaves_of_adj (T : Cladogram X) {u v : T.V}
    (h : T.graph.Adj u v) {x : X} (hx : T.leaf x = v) :
    x ∉ T.sideLeaves s(u, v) u := by
  rw [T.mem_sideLeaves, hx]
  exact fun hr => T.not_reachable_deleteEdges_of_adj h (reachable_comm.mpr hr)

/-- 叶标签落在自己所在的那一侧 —— 给出边侧**非空性**的来源。 -/
theorem mem_sideLeaves_self (T : Cladogram X) (e : Sym2 T.V) (x : X) :
    x ∈ T.sideLeaves e (T.leaf x) :=
  T.mem_sideLeaves.mpr
    (SimpleGraph.Walk.nil : (T.graph.deleteEdges {e}).Walk (T.leaf x) (T.leaf x)).reachable

/-- 叶 `T.leaf x` 在**删去它的边**后成为孤立点（度为 1 ⇒ 唯一邻居）。 -/
theorem isIsolated_leaf_deleteEdges (T : Cladogram X) {x : X} {b : T.V}
    (h : T.graph.Adj (T.leaf x) b) :
    (T.graph.deleteEdges {s(T.leaf x, b)}).IsIsolated (T.leaf x) := by
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨b', _hb', huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  intro w hw
  rw [deleteEdges_adj] at hw
  obtain ⟨hadj, hnotin⟩ := hw
  rw [huniq w hadj, (huniq b h).symm] at hnotin
  exact hnotin (by simp)

/-- **叶边给出平凡 split**：若 `a = T.leaf x` 且 `a` 与 `b` 相邻，
则 `a` 一侧的叶集恰为 `{x}`（删边后 `a` 孤立）。

这是 §3.4「边 ↔ bipartition」在叶边上的退化情形，也是 `Σ(T) ∪ Σ_triv(T)` 里平凡 split 的来源。 -/
theorem sideLeaves_leaf_edge (T : Cladogram X) {x : X} {b : T.V}
    (h : T.graph.Adj (T.leaf x) b) :
    T.sideLeaves s(T.leaf x, b) (T.leaf x) = {x} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨T.mem_sideLeaves_self _ x, ?_⟩
  intro y hy
  rw [T.mem_sideLeaves] at hy
  exact T.leaf.injective
    (reachable_eq_of_isIsolated (T.isIsolated_leaf_deleteEdges h) (reachable_comm.mpr hy))

/-- 边 `e`（取 `u` 侧）给出的 **split**：两侧为「`u` 侧的叶」与「其余叶」。

    ※ `nonempty` 两侧非空对系统发生树恒成立（每个顶点都能走到叶，因为 `Cladogram`
    的度 1 顶点正是叶），故此处作为假设传入。 -/
noncomputable def splitOfEdge (T : Cladogram X) (e : Sym2 T.V) (u : T.V)
    (hA : (T.sideLeaves e u).Nonempty)
    (hB : (Finset.univ \ T.sideLeaves e u).Nonempty) : Split X where
  parts := fun i => if i = 0 then T.sideLeaves e u else Finset.univ \ T.sideLeaves e u
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Finset.disjoint_sdiff, disjoint_comm]
  union_eq_univ := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      by_cases h : x ∈ T.sideLeaves e u
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simp [h]⟩
  nonempty := by
    intro i
    fin_cases i
    · exact hA
    · exact hB

/-- `s` 是树 `T` 的**一条边的 split**：`s` 的某一侧恰是「删去某条边后某一侧的叶集」。

§3.4：删边 `e = ⟦a,b⟧` ⟹ bipartition。直接以**相邻点对**给出（等价于 `edgeSet`，
但省去从 `Sym2` 提取端点的麻烦）。 -/
def IsSplitOf (T : Cladogram X) (s : Split X) : Prop :=
  ∃ (a b : T.V) (_ : T.graph.Adj a b) (u : T.V), s.sideA = T.sideLeaves s(a, b) u

/-- 树 `T` 的**全部边的 split 集**（§3.4 的三级对应之一：边 ↔ bipartition）。

⚠️ 这是**无序 split 的有序表示**：每条边的两个方向都出现在这个集合里
（`Split.sideA`/`sideB` 的 `Fin 2` 索引所致）。因 `Compatible` 对换侧不变，
这对「两两相容」与后续的 Splits-Equivalence 陈述均无影响。 -/
def splits (T : Cladogram X) : Set (Split X) :=
  {s | T.IsSplitOf s}

/-- 树的 split 系统**两两相容**（这就是 Splits-Equivalence 的判据）。 -/
def PairwiseCompatible (T : Cladogram X) : Prop :=
  ∀ s ∈ T.splits, ∀ t ∈ T.splits, Split.Compatible s t

/-! ### 「同侧」关系 —— 树层面相容性证明的地基 -/

/-- `v` 与 `u` 在删去边 `e` 后**同侧**（可达）——`sideLeaves` 的顶点版。 -/
def inSide (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) : Prop :=
  (T.graph.deleteEdges {e}).Reachable u v

theorem inSide_self (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : T.inSide e u u :=
  Reachable.refl _

theorem inSide_comm (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) :
    T.inSide e u v ↔ T.inSide e v u :=
  reachable_comm

theorem inSide_trans (T : Cladogram X) (e : Sym2 T.V) {u v w : T.V}
    (huv : T.inSide e u v) (hvw : T.inSide e v w) : T.inSide e u w :=
  huv.trans hvw

/-- `sideLeaves` 与 `inSide` 的一致性。 -/
theorem mem_sideLeaves_iff_inSide (T : Cladogram X) {e : Sym2 T.V} {u : T.V} {x : X} :
    x ∈ T.sideLeaves e u ↔ T.inSide e u (T.leaf x) := by
  rw [T.mem_sideLeaves]
  exact reachable_comm

/-- **`c,d` 分居边 `e₁` 两侧 ⟹ `⟦c,d⟧ = e₁`**。

（`T - e₁` 的两侧之间没有边，故跨越该割的 `T`-边只能是 `e₁`。） -/
theorem eq_of_adj_of_not_inSide (T : Cladogram X) {e₁ : Sym2 T.V} {u₁ c d : T.V}
    (hcd : T.graph.Adj c d) (hc : T.inSide e₁ u₁ c) (hd : ¬ T.inSide e₁ u₁ d) :
    s(c, d) = e₁ := by
  by_contra hne
  have hadj' : (T.graph.deleteEdges {e₁}).Adj c d :=
    deleteEdges_adj.mpr ⟨hcd, by simpa using hne⟩
  exact hd (hc.trans hadj'.reachable)

/-- **关键观察**：若 `⟦c,d⟧ ≠ e₁` 且 `c,d` 相邻，则 `c,d` 在 `e₁` 的**同一侧**。

于是两条边 `e₁`、`e₂` 的相对位置只有两种互斥情形 —— 分析量减半。 -/
theorem inSide_congr_of_adj (T : Cladogram X) {e₁ : Sym2 T.V} {u₁ c d : T.V}
    (hcd : T.graph.Adj c d) (hne : s(c, d) ≠ e₁) :
    T.inSide e₁ u₁ c ↔ T.inSide e₁ u₁ d := by
  constructor
  · intro hc
    by_contra hd
    exact hne (T.eq_of_adj_of_not_inSide hcd hc hd)
  · intro hd
    by_contra hc
    have h := T.eq_of_adj_of_not_inSide hcd.symm hd hc
    rw [Sym2.eq_swap] at h
    exact hne h

/-- **旁侧连通性（引理 C）**：若 `p,q` 在 `e₁` 同侧，且该侧**不含** `e₂ = ⟦c,d⟧` 的端点，
则 `p,q` 在 `T - e₂` 中仍可达。

证明：`T - e₁` 中的 walk 提升到 `T`（`Walk.mapLe`）后，其支持集仍落在 `p` 的可达类内，
故不含 `c,d`，从而删去 `e₂` 不影响 —— 用 `reachable_deleteEdges_of_support_notMem`。 -/
theorem inSide_deleteEdges_of_inSide (T : Cladogram X)
    {e₁ e₂ : Sym2 T.V} {c d p q : T.V} (he₂ : e₂ = s(c, d))
    (hside : T.inSide e₁ p q) (hc : ¬ T.inSide e₁ p c) (hd : ¬ T.inSide e₁ p d) :
    T.inSide e₂ p q := by
  obtain ⟨p'⟩ := hside
  refine reachable_deleteEdges_of_support_notMem (p'.mapLe (deleteEdges_le {e₁})) ?_
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro w hw
  have hwX : T.inSide e₁ p w := reachable_of_mem_support p' hw
  rw [he₂, Sym2.mem_iff]
  rintro (rfl | rfl)
  · exact hc hwX
  · exact hd hwX

/-- **主引理（情形 1）**：若 `e₂` 的端点 `c,d` **都不在** `u₁` 侧，
则 `sideLeaves e₁ u₁` 与 `sideLeaves e₂ u₂` 相容。

（该侧在 `T - e₂` 中连通 ⟹ 整个侧要么落在 `u₂` 侧、要么落在其补侧。） -/
theorem sidesCompatible_sideLeaves_of_not_inSide (T : Cladogram X)
    {e₁ e₂ : Sym2 T.V} {u₁ u₂ c d : T.V} (he₂ : e₂ = s(c, d))
    (hc : ¬ T.inSide e₁ u₁ c) (hd : ¬ T.inSide e₁ u₁ d) :
    SidesCompatible (T.sideLeaves e₁ u₁) (T.sideLeaves e₂ u₂) := by
  by_cases h : ∃ p, T.inSide e₁ u₁ p ∧ T.inSide e₂ u₂ p
  · -- 存在点同时在两侧：整侧 ⊆ u₂ 侧 ⟹ A ⊆ A'
    obtain ⟨p, hp₁, hp₂⟩ := h
    refine Or.inl fun y hy => ?_
    rw [T.mem_sideLeaves_iff_inSide] at hy ⊢
    have hc' : ¬ T.inSide e₁ (T.leaf y) c := fun h' => hc (hy.trans h')
    have hd' : ¬ T.inSide e₁ (T.leaf y) d := fun h' => hd (hy.trans h')
    have hside : T.inSide e₁ (T.leaf y) p := hy.symm.trans hp₁
    exact hp₂.trans ((T.inSide_comm e₂ (T.leaf y) p).mp
      (T.inSide_deleteEdges_of_inSide he₂ hside hc' hd'))
  · -- 无交 ⟹ Disjoint
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [T.mem_sideLeaves_iff_inSide] at hy hy'
    exact h ⟨T.leaf y, hy, hy'⟩

/-- **删边后每点与端点之一同侧**（树中删边恰得两个连通分量）。

对 `a — b` 相邻，任意 `x` 在 `T - ⟦a,b⟧` 中与 `a` 或 `b` 可达。

证明：取 `T` 中 `x → a` 的 walk 归纳。若某步正是边 `⟦a,b⟧`，则该步只能通向终点 `a`
（否则 `a` 在路径中重复），故其前缀已到 `b`。 -/
theorem inSide_or_inSide (T : Cladogram X) {a b x : T.V} (hab : T.graph.Adj a b) :
    T.inSide s(a, b) x a ∨ T.inSide s(a, b) x b := by
  obtain ⟨p⟩ := T.isTree.connected x a
  refine SimpleGraph.Walk.recOn (motive := fun u v _ =>
    v = a → T.inSide s(a, b) u a ∨ T.inSide s(a, b) u b) p ?_ ?_ rfl
  · intro u hu
    subst hu
    exact Or.inl (Reachable.refl _)
  · intro u v w hadj q ih hw
    by_cases h : s(u, v) = s(a, b)
    · rcases Sym2.eq_iff.mp h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj' : (T.graph.deleteEdges {s(a, b)}).Adj u v :=
        deleteEdges_adj.mpr ⟨hadj, by simpa using h⟩
      rcases ih hw with ih | ih
      · exact Or.inl (hadj'.reachable.trans ih)
      · exact Or.inr (hadj'.reachable.trans ih)

/-- **`e` 的两端点分居两侧**（否则 `T - e` 中 `a` 与 `b` 可达，与「边是桥」矛盾）。 -/
theorem not_inSide_both (T : Cladogram X) {a b y : T.V} (hab : T.graph.Adj a b) :
    ¬ (T.inSide s(a, b) a y ∧ T.inSide s(a, b) b y) := by
  rintro ⟨h1, h2⟩
  exact T.not_reachable_deleteEdges_of_adj hab (h1.trans h2.symm)

/-- **边 `⟦a,b⟧` 的两侧互为补**（由 2 类性 + 两端点分居两侧）。 -/
theorem sideLeaves_compl_adj (T : Cladogram X) {a b : T.V} (hab : T.graph.Adj a b) :
    T.sideLeaves s(a, b) b = (T.sideLeaves s(a, b) a)ᶜ := by
  ext x
  rw [Finset.mem_compl, T.mem_sideLeaves_iff_inSide, T.mem_sideLeaves_iff_inSide]
  constructor
  · intro hb ha
    exact T.not_inSide_both hab ⟨ha, hb⟩
  · intro hb
    rcases T.inSide_or_inSide hab (x := T.leaf x) with h | h
    · exact absurd ((T.inSide_comm _ _ _).mp h) hb
    · exact (T.inSide_comm _ _ _).mp h

/-- **同侧基准可换**：若 `u` 与 `a` 在 `e` 同侧，则 `u` 侧即 `a` 侧。 -/
theorem sideLeaves_eq_of_inSide (T : Cladogram X) {e : Sym2 T.V} {u a : T.V}
    (h : T.inSide e u a) : T.sideLeaves e u = T.sideLeaves e a := by
  ext x
  rw [T.mem_sideLeaves_iff_inSide, T.mem_sideLeaves_iff_inSide]
  exact ⟨fun hu => h.symm.trans hu, fun ha => h.trans ha⟩

/-- **主引理（一般情形）**：任意两条边的 split 侧集相容。

分析：`e₁` 与 `e₂` 的端点相对位置由 `inSide_congr_of_adj` 压缩为两情形；
情形 1 直接由 `sidesCompatible_sideLeaves_of_not_inSide`；
情形 2 用**补侧轮换** + `sideLeaves_compl_adj` 化归到情形 1。 -/
theorem sidesCompatible_sideLeaves (T : Cladogram X)
    {a b c d : T.V} (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d) (u₁ u₂ : T.V) :
    SidesCompatible (T.sideLeaves s(a, b) u₁) (T.sideLeaves s(c, d) u₂) := by
  by_cases hsame : s(c, d) = s(a, b)
  · -- 两边相同：`u₁`、`u₂` 各归到 `a`/`b` 侧，两侧要么相同、要么互补
    rw [hsame]
    rcases T.inSide_or_inSide hab (x := u₁) with h1 | h1 <;>
      rcases T.inSide_or_inSide hab (x := u₂) with h2 | h2
    · rw [T.sideLeaves_eq_of_inSide h1, T.sideLeaves_eq_of_inSide h2]
      exact Or.inl (Finset.Subset.refl _)
    · rw [T.sideLeaves_eq_of_inSide h1, T.sideLeaves_eq_of_inSide h2, T.sideLeaves_compl_adj hab]
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [Finset.disjoint_left]
      intro x hx hxc
      exact (Finset.mem_compl.mp hxc) hx
    · rw [T.sideLeaves_eq_of_inSide h1, T.sideLeaves_eq_of_inSide h2, T.sideLeaves_compl_adj hab]
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [Finset.disjoint_left]
      intro x hx hxc
      exact (Finset.mem_compl.mp hx) hxc
    · rw [T.sideLeaves_eq_of_inSide h1, T.sideLeaves_eq_of_inSide h2]
      exact Or.inl (Finset.Subset.refl _)
  · have hcongr : T.inSide s(a, b) u₁ c ↔ T.inSide s(a, b) u₁ d :=
      T.inSide_congr_of_adj hcd hsame
    by_cases hin : T.inSide s(a, b) u₁ c
    · -- 情形 2：`c,d` 都在 `u₁` 侧 —— 换到补侧，化归情形 1
      rcases T.inSide_or_inSide hab (x := u₁) with hua | hub
      · have hca : T.inSide s(a, b) a c := hua.symm.trans hin
        have hda : T.inSide s(a, b) a d := hua.symm.trans (hcongr.mp hin)
        have hc' : ¬ T.inSide s(a, b) b c := fun h => T.not_inSide_both hab ⟨hca, h⟩
        have hd' : ¬ T.inSide s(a, b) b d := fun h => T.not_inSide_both hab ⟨hda, h⟩
        have hres := T.sidesCompatible_sideLeaves_of_not_inSide
          (e₁ := s(a, b)) (e₂ := s(c, d)) (u₁ := b) (u₂ := u₂) rfl hc' hd'
        have hres' : SidesCompatible (T.sideLeaves s(a, b) a)ᶜ (T.sideLeaves s(c, d) u₂) := by
          rw [← T.sideLeaves_compl_adj hab]; exact hres
        simpa [T.sideLeaves_eq_of_inSide hua] using sidesCompatible_compl_left.mp hres'
      · have hcb : T.inSide s(a, b) b c := hub.symm.trans hin
        have hdb : T.inSide s(a, b) b d := hub.symm.trans (hcongr.mp hin)
        have hc' : ¬ T.inSide s(a, b) a c := fun h => T.not_inSide_both hab ⟨h, hcb⟩
        have hd' : ¬ T.inSide s(a, b) a d := fun h => T.not_inSide_both hab ⟨h, hdb⟩
        have hres := T.sidesCompatible_sideLeaves_of_not_inSide
          (e₁ := s(a, b)) (e₂ := s(c, d)) (u₁ := a) (u₂ := u₂) rfl hc' hd'
        have hcompl : T.sideLeaves s(a, b) a = (T.sideLeaves s(a, b) b)ᶜ := by
          ext x
          simp only [Finset.mem_compl, T.mem_sideLeaves_iff_inSide]
          constructor
          · intro ha hb
            exact T.not_inSide_both hab ⟨ha, hb⟩
          · intro hb
            rcases T.inSide_or_inSide hab (x := T.leaf x) with h | h
            · exact h.symm
            · exact absurd h.symm hb
        have hres' : SidesCompatible (T.sideLeaves s(a, b) b)ᶜ (T.sideLeaves s(c, d) u₂) := by
          rw [← hcompl]; exact hres
        simpa [T.sideLeaves_eq_of_inSide hub] using sidesCompatible_compl_left.mpr hres'
    · -- 情形 1：`c,d` 都不在 `u₁` 侧
      exact T.sidesCompatible_sideLeaves_of_not_inSide rfl hin
        (fun h => hin (hcongr.mpr h))

/-- **平凡 split 必被展示**：每个叶 `x` 的 `{x}` 都出现在 `T` 的 split 系统里（`|X| ≥ 2`）。

（§3.4：`Σ(T)` 含全部平凡 split —— 这是 `Σ(T) = Σ ∪ Σ_triv(X)` 里 `Σ_triv` 的部分。） -/
theorem exists_isSplitOf_singleton (T : Cladogram X) [Nontrivial X] (x : X) :
    ∃ s : Split X, T.IsSplitOf s ∧ s.sideA = {x} := by
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨b, hb, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  obtain ⟨y, hy⟩ := exists_ne x
  have hA : (T.sideLeaves s(T.leaf x, b) (T.leaf x)).Nonempty :=
    ⟨x, T.mem_sideLeaves_self _ x⟩
  have hB : (Finset.univ \ T.sideLeaves s(T.leaf x, b) (T.leaf x)).Nonempty :=
    ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, by
      rw [T.sideLeaves_leaf_edge hb, Finset.mem_singleton]
      exact hy⟩⟩
  refine ⟨T.splitOfEdge s(T.leaf x, b) (T.leaf x) hA hB,
    ⟨T.leaf x, b, hb, T.leaf x, rfl⟩, ?_⟩
  show T.sideLeaves s(T.leaf x, b) (T.leaf x) = {x}
  exact T.sideLeaves_leaf_edge hb

end Cladogram

/-- **Splits-Equivalence 的「树 ⟹ 相容」方向**：树的 split 系统两两相容。

（`CONCEPTS.md` §3.4 里 Splits-Equivalence 定理的一半；另一半
「相容 ⟹ 存在树」需要劈顶点引理。） -/
theorem pairwiseCompatible {X : Type*} [Fintype X] [DecidableEq X] (T : Cladogram X) :
    T.PairwiseCompatible := by
  intro s hs t ht
  change T.IsSplitOf s at hs
  change T.IsSplitOf t at ht
  obtain ⟨a, b, hab, u₁, h1⟩ := hs
  obtain ⟨c, d, hcd, u₂, h2⟩ := ht
  refine Split.compatible_of_sides ?_
  rw [h1, h2]
  exact T.sidesCompatible_sideLeaves hab hcd u₁ u₂

/-! ## cluster 化简（「相容 ⟹ 存在树」的入口） -/

/-- **相容 split 的规范 cluster 两两镶嵌** —— 树构造只需处理镶嵌族。

（由 `sidesCompatible_cluster` + 两侧都避开 `ρ`，用 `laminar_of_sidesCompatible_of_notMem`。） -/
theorem laminar_of_compatible_clusters {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} {s t : Split α} {ρ : α}
    (h : Split.Compatible s t) (hA : A = s.cluster ρ) (hB : B = t.cluster ρ) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  subst hA
  subst hB
  exact laminar_of_sidesCompatible_of_notMem (Split.sidesCompatible_cluster h ρ)
    (s.notMem_cluster ρ) (t.notMem_cluster ρ)
