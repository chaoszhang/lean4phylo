/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Phylo.Core

/-!
# `Phylo.Algorithm.Cherry` —— 樱桃（cherry）

`CONCEPTS.md` §5 的 M5 算法层地基。**cherry** `{a,b}` 指两个叶共享一个公共邻居 ——
这是 NJ / UPGMA / 贪心归约类算法的**基本归约单元**（「每棵树都有 cherry」是它们的起点）。

本文件只搭**定义与基本性质层**；「每棵树都有 cherry」的存在性定理需要直径 / 分支论证，
留作下一步。
-/

namespace Cladogram

open SimpleGraph

variable {X : Type*} (T : Cladogram X)

/-- **樱桃（cherry）**：叶 `a`、`b` **共享一个公共邻居** `v`。

（`a ≠ b` 显式列出，便于直接使用；`v` 必为内部顶点，见 `not_isLeaf_common`。） -/
def IsCherry (a b : X) : Prop :=
  a ≠ b ∧ ∃ v : T.V, T.graph.Adj (T.leaf a) v ∧ T.graph.Adj (T.leaf b) v

/-- 樱桃关系**对称**。 -/
theorem isCherry_symm {a b : X} (h : T.IsCherry a b) : T.IsCherry b a :=
  ⟨h.1.symm, by obtain ⟨v, h1, h2⟩ := h.2; exact ⟨v, h2, h1⟩⟩

/-- 樱桃关系是对称关系。 -/
theorem isCherry_comm (a b : X) : T.IsCherry a b ↔ T.IsCherry b a :=
  ⟨isCherry_symm T, isCherry_symm T⟩

/-- 樱桃的公共邻居**不是叶**（叶的度是 1，不可能同时邻接两个不同的叶）。 -/
theorem IsCherry.not_isLeaf_common {a b : X} (h : T.IsCherry a b) {v : T.V}
    (h1 : T.graph.Adj (T.leaf a) v) (h2 : T.graph.Adj (T.leaf b) v) : ¬ T.IsLeaf v := by
  intro hv
  obtain ⟨w, _hw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv.degree_eq_one
  exact h.1 (T.leaf.injective ((huniq _ h1.symm).trans (huniq _ h2.symm).symm))

/-- 樱桃的公共邻居度不为 2（由 `no_degree_two`）—— 故实际度 ≥ 3。 -/
theorem IsCherry.degree_common_ne_two {a b : X} (h : T.IsCherry a b) {v : T.V}
    (h1 : T.graph.Adj (T.leaf a) v) (h2 : T.graph.Adj (T.leaf b) v) :
    T.graph.degree v ≠ 2 :=
  T.no_degree_two v

/-- 樱桃的公共邻居**不是** `a`、`b` 的像（度为 1 的叶不可能邻接自身以外的两个顶点）。 -/
theorem IsCherry.leaf_ne_common {a b : X} (h : T.IsCherry a b) {v : T.V}
    (h1 : T.graph.Adj (T.leaf a) v) : T.leaf a ≠ v :=
  fun heq => h1.ne heq

end Cladogram
