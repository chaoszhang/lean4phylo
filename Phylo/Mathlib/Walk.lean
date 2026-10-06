/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# `Phylo.Mathlib.Walk` —— Mathlib 缺、本库自建的 walk / 可达性引理

`SCAFFOLD.md` §2 与 `CONCEPTS.md` §4.2：`Phylo/Mathlib/` 存放「Mathlib 尚未提供、本库自建」的
声明，便于将来回灌 Mathlib。

本文件的引理都是 **图论通用** 的，服务于 `Phylo.Split` 里 Splits-Equivalence 的
「树 ⟹ split 系统两两相容」方向。
-/

open SimpleGraph

variable {V : Type*}

namespace SimpleGraph

/-- 三角形边 `s(u,v)` 含其起点。 -/
theorem start_mem_adj_edge {G : SimpleGraph V} {u v : V} (_h : G.Adj u v) : u ∈ s(u, v) :=
  Sym2.mem_iff.mpr (Or.inl rfl)

/-- **walk 支持集的每个顶点都从起点可达**。 -/
theorem reachable_of_mem_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    ∀ {w : V}, w ∈ p.support → G.Reachable u w := by
  induction p with
  | nil =>
    intro w hw
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact Reachable.refl _
  | cons hadj p ih =>
    intro w hw
    rw [Walk.support_cons hadj p] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Reachable.refl _
    · exact Reachable.trans hadj.reachable (ih hw)

/-- **若 walk 的支持集不含边 `e` 的端点，则删去 `e` 后仍可达**。 -/
theorem reachable_deleteEdges_of_support_notMem {G : SimpleGraph V} {e : Sym2 V} {u v : V}
    (p : G.Walk u v) (h : ∀ w ∈ p.support, w ∉ e) :
    (G.deleteEdges {e}).Reachable u v := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj p ih =>
    refine Reachable.trans ?_ (ih ?_)
    · refine (deleteEdges_adj.mpr ⟨hadj, ?_⟩).reachable
      intro hmem
      simp only [Set.mem_singleton_iff] at hmem
      exact h _ (Walk.start_mem_support _) (hmem ▸ start_mem_adj_edge hadj)
    · intro w hw
      exact h w (by rw [Walk.support_cons hadj p]; exact List.mem_cons_of_mem _ hw)

end SimpleGraph
