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

/-- `s` 是树 `T` 的**一条边的 split**：`s` 的某一侧恰是「删某条边后某一侧的叶集」。

§3.4：删边 `e` ⟹ bipartition。`u` 取边的两端点即得两个方向。 -/
def IsSplitOf (T : Cladogram X) (s : Split X) : Prop :=
  ∃ (e : Sym2 T.V) (u : T.V), s.sideA = T.sideLeaves e u

/-- 树 `T` 的**全部边的 split 集**（§3.4 的三级对应之一：边 ↔ bipartition）。

⚠️ 这是**无序 split 的有序表示**：每条边的两个方向都出现在这个集合里
（`Split.sideA`/`sideB` 的 `Fin 2` 索引所致）。因 `Compatible` 对换侧不变，
这对「两两相容」与后续的 Splits-Equivalence 陈述均无影响。 -/
def splits (T : Cladogram X) : Set (Split X) :=
  {s | T.IsSplitOf s}

/-- 树的 split 系统**两两相容**（这就是 Splits-Equivalence 的判据）。 -/
def PairwiseCompatible (T : Cladogram X) : Prop :=
  ∀ s ∈ T.splits, ∀ t ∈ T.splits, Split.Compatible s t

end Cladogram

/-! ## 两侧的相容性（不依赖 `Split`，便于在树上直接证明） -/

/-- **两侧的相容性**（§3.4：相容 ⟺ 一侧包含另一侧，或互补）。

不依赖 `Split` 结构 —— 便于在树上直接证明后，再经 `compatible_of_sides` 抬到 `Split`。 -/
def SidesCompatible {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = Finset.univ

/-- 两侧相容 ⟹ 对应 split 相容。 -/
theorem Split.compatible_of_sides {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Split α} (h : SidesCompatible s.sideA t.sideA) : Split.Compatible s t := by
  rcases h with h | h | h | h
  · exact Split.compatible_of_subset_left h
  · exact Split.compatible_of_subset_right h
  · exact Split.compatible_of_disjoint h
  · exact Split.compatible_of_union h
