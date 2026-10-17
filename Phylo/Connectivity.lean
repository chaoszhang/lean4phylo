/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PerfectPhylogeny

/-!
# `Phylo.Connectivity` —— 「连通顶点集」层（W22 任务 B ① 的第一块器材）

## 目标（派单顺序第 ① 条）

`BinaryConnectedEqualsSideGap`（`PerfectPhylogeny.lean:475`）：

```text
(∃ ℓ : T.V → Bool, (∀ x, ℓ (T.leaf x) = true ↔ x ∈ A) ∧
    ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s})  ↔  DisplaysBinary T A
```

★ 这是「一件器材通三条」的枢纽（W21 C2 的卡点 ＋ B-1 的卡点 ＋ 多状态判据的最短路径）。

## 两半的精确卡点（W22 实测）

* **`⟸`（易半）**：由 `DisplaysBinary T A`（`= A = ∅ ∨ A = univ ∨ T.IsSideOf A`）造 `ℓ`。
  需要三个事实：`∅` 连通（**平凡** ✓）· `univ` 连通（**本文件已给** ✓ `isConnectedSet_univ`）·
  **一条边的叶侧连通**（⟸ ★ **仍缺**：要「删边后可达 ⟹ 存在 `Walk.support` 全在该侧」，
  即把 `Reachable` 的 walk 改造成「删边后的 walk」并搬回原图）。
* **`⟹`（难半）**：两个互补连通集 ⟹ `A` 是某条边的叶侧。
  需要**树中「割边唯一」**：若 `(S, Sᶜ)` 两侧都连通，则跨割边**恰一条** ——
  两条跨割边 ＋ 两侧内部的 walk 会拼出一个**圈** ⇒ 与「树无圈」矛盾。
  ★ 库内**无**此论证（`SimpleGraph` 的圈/连通性分析层缺位）。

## 本文件交付

| 器材 | 状态 |
|---|---|
| `isConnectedSet_univ` —— 树的**全体顶点**连通（`IsConnectedSet T.graph univ`） | ✅ 已证 |
| `isConnectedSet_empty` —— **空集**连通（空真） | ✅ 已证 |

★ 这两条是 `⟸` 半的两个退化情形；剩下的「边侧连通」与 `⟹` 半各需一层新器材，
按派单纪律 **如实收档**（见上），**不**把要证的命题变成假设 ✓。
-/

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- ★ **树的全体顶点连通**：任两点之间都有 walk（support 落在 `univ` 里是空真）。

直接用库内 `Cladogram.existsUnique_path`（`Core.lean:83`，白蹭 Mathlib 的
`isTree_iff_existsUnique_path`）取出唯一路径，**不需要**碰 Mathlib 的树连通 API。 -/
theorem isConnectedSet_univ (T : Cladogram.{u, u} X) :
    IsConnectedSet T.graph (Set.univ : Set T.V) := by
  intro u _ v _
  obtain ⟨p, -, -⟩ := T.existsUnique_path u v
  exact ⟨p, fun _ _ => Set.mem_univ _⟩

omit [Fintype X] [DecidableEq X] in
/-- **空集连通**（空真）：`∀ u ∈ ∅, …` 无元素可挑。 -/
theorem isConnectedSet_empty (T : Cladogram.{u, u} X) :
    IsConnectedSet T.graph (∅ : Set T.V) := by
  intro u hu
  exact absurd hu (Set.notMem_empty u)

/-- ★★ **一条边的**一侧**连通**：`{v | inSide e u v}`（删去 `e` 后 `u` 的可达类）在**原图**中连通。

这是 `⟸` 半的最后一件器材（`BinaryConnectedEqualsSideGap`）：
`IsConnectedSet` 要的是「u′ 到 v′ 存在 walk 且 **support 全在该侧**」。

**证明**（抄库内 `inSide_deleteEdges_of_inSide` 的 API 用法，`Split.lean`）：
`u′ ↔ u ↔ v′` 在 `T - e` 中可达 ⇒ 由 `Reachable.trans` 直接得 `T - e` 中 `u′ → v′` 的 walk `r`；
把它用 `Walk.mapLe (deleteEdges_le {e})` **提升**回 `T`，`support_mapLe_eq_support` 说 support **不变**；
最后 `reachable_of_mem_support r hw` 给「`u′` 可达 `w`」，与 `hu′` 拼出 `u` 可达 `w` ⇒ `w` 在该侧 ✓。 -/
theorem inSide_isConnectedSet (T : Cladogram.{u, u} X) (e : Sym2 T.V) (u : T.V) :
    IsConnectedSet T.graph {v | T.inSide e u v} := by
  intro u' hu' v' hv'
  obtain ⟨r⟩ := ((T.inSide_comm e u u').mp hu').trans hv'
  refine ⟨r.mapLe (SimpleGraph.deleteEdges_le {e}), ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro w hw
  exact hu'.trans (SimpleGraph.reachable_of_mem_support r hw)
