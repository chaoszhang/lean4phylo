/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Phylo.Core

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

end Split

/-! ## 树 → split 系统 -/

namespace Cladogram

open Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 删去边 `e` 后，与顶点 `u` 同侧（落在同一连通分量）的**叶集**。

§3.4：这是「删边 ⟹ bipartition」的直接实现。 -/
noncomputable def sideLeaves (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : Finset X :=
  Finset.univ.filter fun x =>
    (T.graph.deleteEdges {e}).connectedComponentMk (T.leaf x) =
      (T.graph.deleteEdges {e}).connectedComponentMk u

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
