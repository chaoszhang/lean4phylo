/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Core

/-!
# `Phylo.TreeDistance` —— 树的距离演算（`Phylogram.dist` 的工具层）

**为什么需要本文件**：`Phylo/Core.lean` 只**定义**了 `Phylogram.wExt` / `walkDist` / `dist` ——
全库关于 `dist` 的引理**只有** `dist_self`。而

* **T0.3**（Weller 2023 的 leaf-status 论证）的 Lemma 1 / 2 / 3，以及
* **T0.2** 的挂叶距离分解（`graftPhylogram` 的 `dist` 记账）

**都要**用「唯一路径的边权和」的演算：单边即该边权 · 路径上取点可加 · 对称 · 非负 ·
`walkDist` 沿 `append` / `reverse` 的行为。

## 已完成（本文件）

* `wExt_eq_w` / `wExt_eq_zero` / `wExt_nonneg` —— 边权扩展的三条基本性质；
* `walkDist_nil` / `walkDist_append` / `walkDist_reverse` / `walkDist_nonneg`；
* ★ `dist_eq_walkDist_of_isPath` —— **主引理**：任意 `IsPath` walk 的 `walkDist` 就是 `dist`
  （由 `Cladogram.existsUnique_path` 的唯一性）⇒ 此后**一切** `dist` 计算都归约成
  「造一条 `IsPath` walk + 算它的边权和」；
* `dist_comm` / `dist_nonneg` / `dist_eq_wExt_of_adj` / `dist_eq_w_of_adj`；
* ★★ `dist_eq_add_of_mem_support` —— **路径上取点则距离可加**（Lemma 1/2/3 的核心工具）。

## ⚠️ 命名约定（协调用，勿随意改）

本文件的声明一律放在**独立命名空间 `Phylo.TreeDist`** 里 —— 这是**故意的、临时性的**：
`Phylo/BunemanGraft.lean`（T0.2 的挂叶手术）**由另一个 agent 并行开发**，
它同样需要这套演算；若两处在同一命名空间产出同名声明，
T0.2 收口登记 `import` 时会 `environment already contains …` **炸掉全量构建**。
⇒ 独立命名空间使两者**不可能撞名**；T0.2 收口时再决定合并方向（见 `HANDOVER.md` §4.2 T0.3 节）。
-/

universe u v

namespace Phylo

namespace TreeDist

open SimpleGraph

variable {X : Type u}

/-! ## `wExt`：边权到全部顶点对的扩展 -/

section WExt

variable (T : Phylogram.{u, v} X)

/-- 是边时 `wExt` 就是 `w`。 -/
theorem wExt_eq_w {e : Sym2 T.V} (h : e ∈ T.graph.edgeSet) : T.wExt e = T.w ⟨e, h⟩ := by
  rw [Phylogram.wExt]
  exact dite_eq_left h

/-- 不是边时 `wExt` 为 `0`。 -/
theorem wExt_eq_zero {e : Sym2 T.V} (h : e ∉ T.graph.edgeSet) : T.wExt e = 0 := by
  rw [Phylogram.wExt]
  exact dite_eq_right h

/-- `wExt` 非负。 -/
theorem wExt_nonneg (e : Sym2 T.V) : 0 ≤ T.wExt e := by
  by_cases h : e ∈ T.graph.edgeSet
  · rw [wExt_eq_w T h]
    exact T.w_nonneg ⟨e, h⟩
  · rw [wExt_eq_zero T h]

end WExt

/-! ## `walkDist`：一条 `Walk` 的加权长度 -/

section WalkDist

variable (T : Phylogram.{u, v} X) {a b c : T.V}

/-- 空 walk 长度为 `0`。 -/
theorem walkDist_nil : T.walkDist (SimpleGraph.Walk.nil : T.graph.Walk a a) = 0 := by
  simp [Phylogram.walkDist, SimpleGraph.Walk.edges]

/-- `walkDist` 沿 `append` **可加**。 -/
theorem walkDist_append (p : T.graph.Walk a b) (q : T.graph.Walk b c) :
    T.walkDist (p.append q) = T.walkDist p + T.walkDist q := by
  simp [Phylogram.walkDist, SimpleGraph.Walk.edges_append, List.sum_append]

/-- 反向走不改变长度。 -/
theorem walkDist_reverse (p : T.graph.Walk a b) :
    T.walkDist p.reverse = T.walkDist p := by
  simp [Phylogram.walkDist, SimpleGraph.Walk.edges_reverse, List.sum_reverse]

/-- `walkDist` 非负（边权非负）。 -/
theorem walkDist_nonneg (p : T.graph.Walk a b) : 0 ≤ T.walkDist p := by
  rw [Phylogram.walkDist]
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
  exact wExt_nonneg T e

end WalkDist

/-! ## `dist`：唯一路径的 `walkDist`

`dist u v` 取的是**唯一路径**（`Cladogram.existsUnique_path`）的 `walkDist`。
以下全部经由**主引理**：任何 `IsPath` 的 walk 就是那条唯一路径。 -/

section Dist

variable (T : Phylogram.{u, v} X) {a b c : T.V}

/-- ★ **主引理**：任意 `IsPath` 的 walk 都是那条唯一路径，故其 `walkDist` **就是** `dist`。

⇒ 此后一切 `dist` 计算都归约成「造一条 `IsPath` walk + 算它的边权和」。 -/
theorem dist_eq_walkDist_of_isPath (p : T.graph.Walk a b) (hp : p.IsPath) :
    T.dist a b = T.walkDist p := by
  have h : p = (T.existsUnique_path a b).choose := (T.existsUnique_path a b).choose_spec.2 p hp
  rw [Phylogram.dist, h]

/-- `dist` **对称**。 -/
theorem dist_comm (a b : T.V) : T.dist a b = T.dist b a := by
  have hp : (T.existsUnique_path b a).choose.reverse.IsPath :=
    SimpleGraph.Walk.IsPath.reverse (T.existsUnique_path b a).choose_spec.1
  rw [dist_eq_walkDist_of_isPath T _ hp,
    dist_eq_walkDist_of_isPath T _ (T.existsUnique_path b a).choose_spec.1, walkDist_reverse]

/-- `dist` **非负**。 -/
theorem dist_nonneg (a b : T.V) : 0 ≤ T.dist a b := by
  rw [dist_eq_walkDist_of_isPath T _ (T.existsUnique_path a b).choose_spec.1]
  exact walkDist_nonneg T _

/-- **相邻两点的距离就是该边的 `wExt`**（单边走一次）。 -/
theorem dist_eq_wExt_of_adj (h : T.graph.Adj a b) :
    T.dist a b = T.wExt s(a, b) := by
  rw [dist_eq_walkDist_of_isPath T (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)
    (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simpa using h.ne))]
  simp [Phylogram.walkDist, SimpleGraph.Walk.edges]

/-- **相邻两点的距离等于该边的权**（`wExt` 形式去掉 `dite`）。 -/
theorem dist_eq_w_of_adj (h : T.graph.Adj a b) :
    T.dist a b = T.w ⟨s(a, b), (SimpleGraph.mem_edgeSet T.graph).mpr h⟩ := by
  rw [dist_eq_wExt_of_adj T h]
  exact wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr h)

/-- ★★ **路径上取点则距离可加**（Lemma 1/2/3 的核心工具）：

若 `c` 落在 `a→b` 的唯一路径上，则 `dist a b = dist a c + dist c b`。 -/
theorem dist_eq_add_of_mem_support (p : T.graph.Walk a b) (hp : p.IsPath) (hc : c ∈ p.support) :
    T.dist a b = T.dist a c + T.dist c b := by
  have hsplit : (p.takeUntil c hc).append (p.dropUntil c hc) = p :=
    SimpleGraph.Walk.take_spec p hc
  have hp' : ((p.takeUntil c hc).append (p.dropUntil c hc)).IsPath := by
    rw [hsplit]; exact hp
  have h1 : T.dist a b = T.walkDist p := dist_eq_walkDist_of_isPath T p hp
  have h2 : T.dist a c = T.walkDist (p.takeUntil c hc) :=
    dist_eq_walkDist_of_isPath T _ (SimpleGraph.Walk.IsPath.of_append_left hp')
  have h3 : T.dist c b = T.walkDist (p.dropUntil c hc) :=
    dist_eq_walkDist_of_isPath T _ (SimpleGraph.Walk.IsPath.of_append_right hp')
  -- ⚠️ 不能直接 `rw [← hsplit]`：`hc` 的类型依赖 `p`，抽象出的 motive 不合法。
  --    故只在**左侧**做这次替换（`conv_lhs`），随后即可用 `walkDist_append`。
  have h4 : T.walkDist p = T.walkDist (p.takeUntil c hc) + T.walkDist (p.dropUntil c hc) := by
    conv_lhs => rw [← hsplit]
    rw [walkDist_append]
  rw [h1, h2, h3, h4]

/-- ★★ **拼起来仍是路径 ⟹ 距离沿拼接点可加**：

若 `p.append q` 是 `IsPath`，则 `dist a c = dist a b + dist b c`。

（比 `dist_eq_add_of_mem_support` 更实用：它只要**两条路能拼成一条路径**，
不必先把拼接点从 `support` 里找出来；两方向都由主引理 + `walkDist_append` 直接给出。） -/
theorem dist_eq_add_of_isPath_append {a b c : T.V} (p : T.graph.Walk a b) (q : T.graph.Walk b c)
    (hpq : (p.append q).IsPath) :
    T.dist a c = T.dist a b + T.dist b c := by
  rw [dist_eq_walkDist_of_isPath T _ hpq, walkDist_append,
    ← dist_eq_walkDist_of_isPath T p (SimpleGraph.Walk.IsPath.of_append_left hpq),
    ← dist_eq_walkDist_of_isPath T q (SimpleGraph.Walk.IsPath.of_append_right hpq)]

end Dist

end TreeDist

end Phylo
