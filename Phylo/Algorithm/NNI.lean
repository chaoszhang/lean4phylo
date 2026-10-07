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
* ★★ `nniResolvent_incompatible_parent` —— **分解与母 split 不相容**
  （「NNI 恰好改动 `e` 的 split」）；
* ★★★ `nniResolvent_swap_incompatible` / `nniResolvent_three_incompatible` ——
  **三个分解（自身 + 两个 NNI）两两不相容** ⇒ 它们**不能**被同一棵树展示。
  合起来就是「边 `e` 的 NNI 邻域恰有 3 个互不相同的成员」。

⚠️ **注意**：旧版本把第一条写成「**相容**」，那是**假命题**（见下节修正记录）。

⬜ **缺**（下一批）：树层操作 `nniT'`（真的构造第二棵树）、NNI 邻域关系（对称性）、
NNI 距离的度量性、局部相容性引理（「不穿越 `e` 的 split 都与 `e` 的三个分解相容」——
⚠️ 见下节的**反例**：这条必须用到「`t` 是 `T` 的 split」，不能只在四块上做组合）、
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


/-! ## NNI 分解的（不）相容性

⚠️ **修正记录（2026-10-08）**：本文件旧注释把「分解与母 split 相容」列为待证的 ★★ 目标，
**那是假命题**。设 `A = A₁ ⊔ A₂`、`B = B₁ ⊔ B₂`，则

* `S₀ = A₁A₂ | B₁B₂`（母 split，即 `e` 原来的 split）；
* `S₁ = A₁B₁ | A₂B₂`（NNI-1，即 `nniResolvent A₁ B₁`）；
* `S₂ = A₁B₂ | A₂B₁`（NNI-2，即 `nniResolvent A₁ B₂`，`B₂ := B \ B₁`）；

三者的**四个交**分别含 `A₁`、`A₂`、`B₁`、`B₂`，全非空 —— 故三者**两两不相容**。
叶层面即同一个 quartet 的三种拓扑 `{a,b}|{c,d}`、`{a,c}|{b,d}`、`{a,d}|{b,c}` 互不相容。

（旧「相容」大概是混淆了以下事实：NNI 之后**除 `e` 以外的边** split 不变 —— 那些 split
与 `S₁` 相容；但母 split `S₀` 本身**一定**与 `S₁` 不相容，这正是「NNI 恰好改动 `e` 的 split」。）

⬜ **真正待证的局部相容性引理**：怎样刻画「与 `S₀, S₁, S₂` 全相容」的 split？
**不能**只说「与 `S₀` 相容且 `≠ S₀`」——反例：四块取 `A₁={a₁,a₂}`、`A₂={a₃}`、
`B₁={b₁,b₂}`、`B₂={b₃}`，另有一块 `R={r}` 在 `e` 之外，则 `t = A₁A₂B₁ | B₂R`
与 `S₀`、`S₁` 都相容却与 `S₂` 不相容（`C∩A₁B₂ ∋ a₁`、`C∩A₂B₁ ∋ a₃`、
`D∩A₁B₂ ∋ b₂`、`D∩A₂B₁ ∋ r`）。因此该引理**必须**用到「`t` 是 `T` 的 split」
（即 `t` 来自树中的某条边），而不能只在四块上做组合。

⚠️ **本版 Lean 的两大坑（务必先读，已实测）**

1. **`fin_cases` 的字面量不可归约**。`fin_cases i`（`i : Fin 2`）把字面量写成
   `(fun i => i) ⟨0, ⋯⟩`，与 `nniParts … 0` 无法 `rw` 匹配，`simp` 也归约不动。
   ⇒ **必须**用 `by_cases hi : i = 0` + `subst hi`，让变量被换成真字面量。
2. **`h : Disjoint S T` 在 `rcases hc with h | h | h | h` 之后不能当函数用**
   （`h hx hy` 会报 `expected type ?m ⊆ …`，即被误解析成 `LE.le`）。
   ⇒ **必须**写 `(Finset.disjoint_left.mp h) hx hy`；
   且 `Finset.disjoint_left.mp h : ∀ a, a ∈ S → a ∉ T`（**第一侧在前**）。

3. 证 `Nonempty` 时**先** `refine ⟨x, ?_⟩` **再** `rw [Finset.mem_inter, …]`：
   `Nonempty` 是 `∃ x, x ∈ s`，在它上面直接 `rw [Finset.mem_inter]` 找不到 `∈ ∩` 的匹配。 -/

/-- ★★ **NNI 分解与母 split 不相容** —— 「NNI 恰好改动 `e` 的 split」。

四个交的见证依次是 `A₁`、`B₁`、`A₂`、`B₂`，故需四块都非空。 -/
theorem nniResolvent_incompatible_parent (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hB₂ : (s.sideB \ B₁).Nonempty) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).Incompatible s := by
  rw [incompatible_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hA₁.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideA]
      exact ⟨Finset.mem_union_left _ hx, hA₁sub hx⟩
  · exact hB₁.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideA]
      exact ⟨Finset.mem_union_right _ hx, hB₁sub hx⟩
  · exact hA₂.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideB]
      exact ⟨Finset.mem_union_left _ hx, (Finset.mem_sdiff.mp hx).1⟩
  · exact hB₂.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideB]
      exact ⟨Finset.mem_union_right _ hx, (Finset.mem_sdiff.mp hx).1⟩

/-- ★★★ **同一母 split 的两个互补 NNI 分解互不相容**。

`S₁ = A₁B₁ | A₂B₂` 与 `S₂ = A₁B₂ | A₂B₁`（`B₂ := B \ B₁`）的四个交分别含
`A₁`、`B₁`、`B₂`、`A₂`。 -/
theorem nniResolvent_swap_incompatible (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hB₂ : (s.sideB \ B₁).Nonempty) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).Incompatible
      (s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset) := by
  rw [incompatible_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hA₁.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideA, nniResolvent_sideA]
      exact ⟨Finset.mem_union_left _ hx, Finset.mem_union_left _ hx⟩
  · exact hB₁.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideA, nniResolvent_sideB]
      exact ⟨Finset.mem_union_right _ hx, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hB₁sub hx, fun h => (Finset.mem_sdiff.mp h).2 hx⟩)⟩
  · exact hB₂.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideB, nniResolvent_sideA]
      exact ⟨Finset.mem_union_right _ hx, Finset.mem_union_right _ hx⟩
  · exact hA₂.mono fun x hx => by
      rw [Finset.mem_inter, nniResolvent_sideB, nniResolvent_sideB]
      exact ⟨Finset.mem_union_left _ hx, Finset.mem_union_left _ hx⟩

/-- ★★★ **边 `e` 的三个分解两两不相容** —— NNI 邻域的 3 个成员互不相同。

即 `S₀ ⊥ S₁`、`S₁ ⊥ S₂`、`S₂ ⊥ S₀`（`S₂ := nniResolvent A₁ B₂`、`B₂ := B \ B₁`）。 -/
theorem nniResolvent_three_incompatible (s : Split α) (A₁ B₁ : Finset α)
    (hA₁ : A₁.Nonempty) (hA₂ : (s.sideA \ A₁).Nonempty)
    (hA₁sub : A₁ ⊆ s.sideA) (hB₁sub : B₁ ⊆ s.sideB)
    (hB₁ : B₁.Nonempty) (hB₂ : (s.sideB \ B₁).Nonempty) :
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).Incompatible s ∧
    (s.nniResolvent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub).Incompatible
      (s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset) ∧
    (s.nniResolvent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub Finset.sdiff_subset).Incompatible s := by
  refine ⟨s.nniResolvent_incompatible_parent A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub hB₁ hB₂,
    s.nniResolvent_swap_incompatible A₁ B₁ hA₁ hA₂ hA₁sub hB₁sub hB₁ hB₂, ?_⟩
  refine s.nniResolvent_incompatible_parent A₁ (s.sideB \ B₁) hA₁ hA₂ hA₁sub
    Finset.sdiff_subset hB₂ ?_
  obtain ⟨x, hx⟩ := hB₁
  exact ⟨x, Finset.mem_sdiff.mpr
    ⟨hB₁sub hx, fun h => (Finset.mem_sdiff.mp h).2 hx⟩⟩

end Split
