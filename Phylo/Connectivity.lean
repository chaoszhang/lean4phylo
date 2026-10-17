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
