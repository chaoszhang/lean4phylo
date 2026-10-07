/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Binary
import Phylo.Algorithm.Cherry

/-!
# `Phylo.Algorithm.NNI` —— 最近邻交换（Nearest Neighbour Interchange, NNI）

## 概念（文献口径）

**NNI** 是系统发生树上最基本的**局部拓扑重排**操作。教科书写法（Atlantis Press 的重排操作综述；
亦见 Semple & Steel, *Phylogenetics* (2003) §2.4、Felsenstein 2004）：

> **NNI** means swapping two subtrees that are incident to the same **internal edge**.

精确的图论语义：设无根树 `T` 的内部边 `e = {u,v}`（两端都非叶）。删去 `e`，得到两个连通分量
`C_u`、`C_v`。设 `u` 在 `C_u` 中的邻居为 `a, b`（子树 `A₁, A₂`），`v` 在 `C_v` 中的邻居为
`c, d`（子树 `B₁, B₂`）。则 `e` 的 NNI 操作把「`u` 接 `a, b`」与「`v` 接 `c, d`」重新配对：

```
        a   b          c   d                 a   b          c   d
         \ /            \ /                   \ /            \ /
          u ----------- v         ⟶           u ----------- v
        A₁ A₂          B₁ B₂                A₁ B₁          A₂ B₂
   （原树：e 的 split 为 A₁A₂ | B₁B₂）   （NNI：e 的新 split 为 A₁B₁ | A₂B₂）
```

于是**边 `e` 的 NNI 邻域恰有 3 个成员**（含自身 —— 自身由「不交换」给出），对应边 `e` 的
**三种分解（resolution）**。在**叶**层面（binary 树，`a,b,c,d` 都是叶）这三者是：

| 分解 | 边 split |
|---|---|
| 原始 | `{a,b} \| {c,d}` |
| NNI-1 | `{a,c} \| {b,d}` |
| NNI-2 | `{a,d} \| {b,c}` |

即**同一个 quartet 的三种拓扑**（NNI **不保持** quartet 系统 —— 它恰好改动一个 quartet）。
这是 NNI 与 SPR/TBR 的分水岭：SPR/TBR 是更大的邻域（`NNI ⊂ SPR ⊂ TBR`）。

## 本文件做到哪、缺什么

本文件是 **split 层**（纯组合，不造新树）：

* `Split.nniParts` / `Split.nniResolvent` —— 分裂的 **NNI 分解**：
  给定 `A|B` 与 `A₁ ⊆ A`、`B₁ ⊆ B`（各自非空），产出 `A₁∪B₁ | A₂∪B₂`
  （`A₂ := A \ A₁`、`B₂ := B \ B₁`）；`nniResolvent_sideA` / `nniResolvent_sideB`；
* ★★ `nniResolvent_compatible` —— **NNI 分解与母 split 相容**；
* ★★★ `nniResolvent_swap_incompatible` —— **同一母 split 的两个互补分解互不相容**
  ⇒ 它们**不能**被同一棵树展示。

⬜ **缺**（下一批）：树层操作 `nniT'`（真的构造第二棵树）、NNI 邻域关系（对称性）、
NNI 距离的度量性、局部相容性引理（「不穿越 `e` 的 split 都与 `e` 的三个分解相容」）、
`QuartetDecidesTree` 的 NNI 证书。

## 文献

* Semple & Steel, *Phylogenetics* (2003), §2.4（NNI 与树空间）；
* Robinson (1971)「tree rearrangement」；Felsenstein (2004) §4；
* Atlantis Press 重排操作综述（NNI/SPR/TBR/LPR/LLI 定义）；见 `CONCEPTS.md` §2.6。
-/

universe u

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## NNI 分解（split 层）

⚠️ **Lean 技术备注（踩坑记录）**：本文件的分块证明走
「`Fin.cases` 定义 + `subst` 变量」，而**不用** `fin_cases`：
本版 Lean 的 `fin_cases` 把 `Fin 2` 的字面量写成 `(fun i => i) ⟨0, ⋯⟩`，
无法与 `nniParts … 0` 做 `rw` 匹配（`simp` 也归约不动）。
只有 `subst` 把**变量**换成字面量后，`nniParts` 才保持可归约形式。 -/

/-- NNI 分解的**块函数**：`0 ↦ A₁ ∪ B₁`、`1 ↦ (A \ A₁) ∪ (B \ B₁)`。

用 `Fin.cases`（而非 `if i = 0`）实现 —— 这样 `nniParts … 0` 与 `nniParts … 1` 都是 **`rfl`**。 -/
noncomputable def nniParts (s : Split α) (A₁ B₁ : Finset α) : Fin 2 → Finset α :=
  Fin.cases (A₁ ∪ B₁) fun _ : Fin 1 => (s.sideA \ A₁) ∪ (s.sideB \ B₁)

/-- `nniParts` 在 `0` 处的值（定义相等）。 -/
theorem nniParts_zero (s : Split α) (A₁ B₁ : Finset α) : s.nniParts A₁ B₁ 0 = A₁ ∪ B₁ := rfl

/-- `nniParts` 在 `1` 处的值（定义相等）。 -/
theorem nniParts_one (s : Split α) (A₁ B₁ : Finset α) :
    s.nniParts A₁ B₁ 1 = (s.sideA \ A₁) ∪ (s.sideB \ B₁) := rfl

/-- **NNI 分解（resolvent）**：把 split `A|B` 换成 `(A₁ ∪ B₁) | (A₂ ∪ B₂)`，
其中 `A₂ := A \ A₁`、`B₂ := B \ B₁`。

假设：`hA₁`（`A₁` 非空）、`hA₂`（`A \ A₁` 非空 —— 保证第二块非空）、
`hA₁sub`/`hB₁sub`（`A₁ ⊆ A`、`B₁ ⊆ B`）。 -/
noncomputable def nniResolvent (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB) : Split α where
  parts := s.nniParts A₁ B₁
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    by_cases hi : i = 0
    · subst hi
      rw [nniParts_zero] at hx
      by_cases hj : j = 0
      · subst hj
        exact absurd rfl hij
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst hj1
        rw [nniParts_one] at hy
        rcases Finset.mem_union.mp hx with hx1 | hx1 <;>
          rcases Finset.mem_union.mp hy with hy1 | hy1
        · exact (Finset.mem_sdiff.mp hy1).2 hx1
        · exact (Finset.disjoint_left.mp s.disjoint_sides) (hA₁sub hx1) (Finset.mem_sdiff.mp hy1).1
        · have hya : x ∈ s.sideA := (Finset.mem_sdiff.mp hy1).1
          have hxb : x ∈ s.sideB := hB₁sub hx1
          exact (Finset.disjoint_left.mp s.disjoint_sides) hya hxb
        · exact (Finset.mem_sdiff.mp hy1).2 hx1
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      rw [nniParts_one] at hx
      by_cases hj : j = 0
      · subst hj
        rw [nniParts_zero] at hy
        rcases Finset.mem_union.mp hx with hx1 | hx1 <;>
          rcases Finset.mem_union.mp hy with hy1 | hy1
        · exact (Finset.mem_sdiff.mp hx1).2 hy1
        · have hxa : x ∈ s.sideA := (Finset.mem_sdiff.mp hx1).1
          have hyb : x ∈ s.sideB := hB₁sub hy1
          exact (Finset.disjoint_left.mp s.disjoint_sides) hxa hyb
        · have hxb : x ∈ s.sideB := (Finset.mem_sdiff.mp hx1).1
          have hya : x ∈ s.sideA := hA₁sub hy1
          exact (Finset.disjoint_left.mp s.disjoint_sides.symm) hxb hya
        · exact (Finset.mem_sdiff.mp hx1).2 hy1
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst hj1
        exact absurd rfl hij
  union_eq_univ := by
    ext x
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    rw [Finset.mem_biUnion]
    have hx : x ∈ s.sideA ∪ s.sideB := by rw [s.union_sides]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · by_cases hA : x ∈ A₁
      · exact ⟨0, Finset.mem_univ _, by rw [nniParts_zero]; exact Finset.mem_union_left _ hA⟩
      · exact ⟨1, Finset.mem_univ _, by
          rw [nniParts_one]
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hA⟩)⟩
    · by_cases hB : x ∈ B₁
      · exact ⟨0, Finset.mem_univ _, by rw [nniParts_zero]; exact Finset.mem_union_right _ hB⟩
      · exact ⟨1, Finset.mem_univ _, by
          rw [nniParts_one]
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hB⟩)⟩
  nonempty := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [nniParts_zero]
      exact Finset.union_nonempty.mpr (Or.inl hA₁)
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      rw [nniParts_one]
      exact Finset.union_nonempty.mpr (Or.inl hA₂)

/-- **分解的第一侧**：`A₁ ∪ B₁`。 -/
@[simp] theorem nniResolvent_sideA (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).sideA = A₁ ∪ B₁ :=
  nniParts_zero s A₁ B₁

/-- **分解的第二侧**：`(A \ A₁) ∪ (B \ B₁)`。 -/
@[simp] theorem nniResolvent_sideB (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).sideB
      = (s.sideA \ A₁) ∪ (s.sideB \ B₁) :=
  nniParts_one s A₁ B₁


/-! ## ⬜ 未完成：相容性与互补分解的不相容

**目标 1（相容）**：`(s.nniResolvent A₁ B₁ …).Compatible s`。
证明只需一条：分解的**第二块** `A₂ ∪ B₂ = (A \ A₁) ∪ (B \ B₁)` 完全落在 `B` 内，
故与 `A` 不交。所需假设：`hA₂B : s.sideA \ A₁ ⊆ s.sideB`、`hB₂B : s.sideB \ B₁ ⊆ s.sideB`。

**目标 2（不相容）**：同一母 split 的两个互补分解互不相容。
叶层面：`{a,b}|{c,d}` 的两个 NNI 分解 `{a,c}|{b,d}` 与 `{a,d}|{b,c}` 互不相容 ——
这正是「NNI 邻域除自身外各成员互不相同」的组合根据。
`nniResolvent_sideA` / `nniResolvent_sideB` 已把两个分解的两侧展开为四块的并
（`A₁∪B₁`、`(A\A₁)∪(B\B₁)`、`A₁∪B₂`、`(A\A₁)∪(B\B₂)`），故取 `x ∈ A₂`
即可逐一击破 `Compatible` 的四个「分侧不交」条件。

## ⚠️ 本版 Lean 的两大坑（务必先读，已实测）

1. **`fin_cases` 的字面量不可归约**。`fin_cases i`（`i : Fin 2`）把字面量写成
   `(fun i => i) ⟨0, ⋯⟩`，与 `nniParts … 0` 无法 `rw` 匹配，`simp` 也归约不动。
   ⇒ **必须**用 `by_cases hi : i = 0` + `subst hi`，让变量被换成真字面量。
2. **`h : Disjoint S T` 在 `rcases hc with h | h | h | h` 之后不能当函数用**
   （`h hx hy` 会报 `expected type ?m ⊆ …`，即被误解析成 `LE.le`）。
   ⇒ **必须**写 `(Finset.disjoint_left.mp h) hx hy`；
   且 `Finset.disjoint_left.mp h : ∀ a, a ∈ S → a ∉ T`（**第一侧在前**）。 -/

end Split
