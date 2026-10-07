/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Buneman

/-!
# `Phylo.BunemanGraft` —— Buneman 归纳步的**图手术**（挂两片叶）

**文献**：P. Buneman, *A Note on the Metric Properties of Trees*,
J. Combinatorial Theory (B) **17** (1974) 48–50，
`references/md/Buneman1974_MetricPropertiesOfTrees.md` **第 74–121 行**（Theorem 2 的归纳证明）。

**转录 vs 改编**：本文件是**改编**。`Phylo/Buneman.lean` 已把第 78–121 行的**全部算术**做完
（选极大三元组、扩张相异度 `δ'`、挂叶恒等式 (2a)/(2b)）；本文件补第 119–121 行
「*p and q can then be attached by edges of weight `d(p,t)` and `d(q,t)`*」的**图论内容**：
把一棵 `Phylogram` 的一片叶 `t` 改造成度 3 的内部顶点，接上两片新叶。

顶点编码用 `V ⊕ Fin 2`：`Sum.inl v` = 旧顶点，`Sum.inr i` = 第 `i` 片新叶。
旧顶点之间的邻接 `(graftGraph G t).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b`
（★ `Phylo.graftGraph_adj_inl_inl`），故 `graftGraph G t` 是把 `G` 原样嵌入、再加两条挂边。

## ★ 已证内容（本文件）

* **★★★ `Phylo.graftGraph`** —— 挂叶手术的**图**（`SimpleGraph (V ⊕ Fin 2)`）。
* **★★★ `Phylo.graftGraph_adj_inl_inl`** —— 旧顶点之间的邻接**与原图一致**（挂叶不动旧边）。
* **★★★ `Phylo.graftGraph_adj_inl_inr`** / **★★★ `Phylo.graftGraph_adj_inr_inl`** ——
  两条挂边：`Sum.inl x` 与第 `i` 片新叶相邻 **⟺** `x = t`。
* **★★★ `Phylo.graftGraph_adj_not_inr_inr`** —— 两片新叶之间**无边**（这正是「新叶度 1、
  故 `leaf_iff_degree_one` 成立」的来源）。

## ⬜ 诚实边界（本文件**不**声称的）

* **⬜ `Phylo.graftGraph_isTree`**（挂叶后仍是树）、**⬜ `Phylo.graftCladogram`** /
  **⬜ `Phylo.graftPhylogram`**（`no_degree_two` / `leaf_iff_degree_one`）、
  **⬜ `Phylo.graftPhylogram_dist_leaf`**（`dist` 记账：旧点到旧点不变，`p`、`q` 到旧点
  用 `Dissimilarity.attach_left` / `attach_right` 分解为 `ρ + T'.dist (T'.leaf t) ·`）——
  均**尚未**落地（本文件目前只有图与邻接接口；无 `sorry`、无 `axiom`）。

* **⬜ `Dissimilarity.InductiveAssembly` 与 `Phylo/Buneman.lean` 的缺口 —— 精确边界**：

  Buneman 第 116–121 行的收缩把**新点 `t`** 加进较小集合 `S' = S ∖ {p,q} ∪ {t}`，
  于是 `t` 是较小问题的**标签**，在 `Cladogram`（`leaf_iff_degree_one` + `no_degree_two`）
  下 `t` 必是较小树 `T'` 的**叶**（度 1）。**计数核对**：`T'` 有 `|V'|` 个顶点、
  `|E'| = |V'| − 1` 条边；`graftGraph` 加 2 个顶点、2 条边，得
  `|E(graftGraph)| = |V'| + 1 = |V(graftGraph)| − 1` —— **恰是树所要求的计数**，
  且新叶度 1、`t` 由 1 变 3、其余旧点度数不变：故**本文件选定的「挂到 `t` 本身」是正确手术**
  （挂到别的旧点上会让 `t` 变孤立点或度 2，反而破坏 `IsTree` / `no_degree_two`）。

  真正未闭合的是 `InductiveAssembly` 对**小基数**的要求：`t` 由 (2a)/(2b) 只在
  `S ∖ {p,q}` 上被**距离数据**确定，而 `Cladogram` 的顶点集必须**恰好**承载
  `leaf_iff_degree_one`（每个度 1 顶点都是标签）。当 `|S| = 3` 时 `S' = {t, r}`
  只有 2 个标签，`T'` 是单单一条边、`t` 是它的叶；挂上 `p`、`q` 后 `t` 度 3，
  得到的是**三点星形** `K_{1,3}`（`p, q, r` 三个标签共用一个非标签中心 `t`）——
  它不是任何 `Phylogram X` 的「叶恰为 `X`」形式。这正是 Buneman 第 74 行
  「For any metric on a set of order three it is easy to construct the appropriate tree」
  必须**单独**处理的基例，故 `InductiveAssembly` 的完整证明需要
  `|Y| = 3`（三点星形）与 `|Y| = 4`（四点星形）两个基例 + 本文件的挂叶手术。
-/

noncomputable section

open SimpleGraph

universe u

namespace Phylo

variable {V : Type*}

/-- ★★★ **挂叶图**（Buneman 第 119–121 行的图手术）：在 `G` 上把两片新叶
`Sum.inr 0`、`Sum.inr 1` 接到旧顶点 `Sum.inl t` 上，旧顶点之间的邻接与 `G` 完全一致。 -/
def graftGraph (G : SimpleGraph V) (t : V) : SimpleGraph (V ⊕ Fin 2) where
  Adj a b :=
    (∃ x y : V, G.Adj x y ∧ a = Sum.inl x ∧ b = Sum.inl y) ∨
    (a = Sum.inl t ∧ (b = Sum.inr 0 ∨ b = Sum.inr 1)) ∨
    (b = Sum.inl t ∧ (a = Sum.inr 0 ∨ a = Sum.inr 1))
  symm := Std.Symm.mk fun a b h => by
    rcases h with ⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
    · exact Or.inl ⟨y, x, hxy.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inr ⟨rfl, Or.inr h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  loopless := Std.Irrefl.mk fun a h => by
    rcases h with ⟨x, y, hxy, ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha] at hb
      exact hxy.ne (Sum.inl.inj hb)
    · subst ha
      rcases hb with h | h
      · exact nomatch h
      · exact nomatch h
    · subst ha
      rcases hb with h | h
      · exact nomatch h
      · exact nomatch h

/-- ★★★ 旧顶点之间的邻接与原图一致（挂叶不动旧边）。 -/
@[simp] theorem graftGraph_adj_inl_inl {G : SimpleGraph V} {t x y : V} :
    (graftGraph G t).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y := by
  constructor
  · intro h
    rcases h with ⟨x', y', hxy, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Sum.inl.inj h1) ▸ (Sum.inl.inj h2) ▸ hxy
    · rcases h2 with h | h <;> exact nomatch h
    · rcases h2 with h | h <;> exact nomatch h
  · intro h
    exact Or.inl ⟨x, y, h, rfl, rfl⟩

/-- ★★★ **挂边**：`Sum.inl x` 与第 `i` 片新叶相邻 ⟺ `x = t`。 -/
@[simp] theorem graftGraph_adj_inl_inr {G : SimpleGraph V} {t x : V} {i : Fin 2} :
    (graftGraph G t).Adj (Sum.inl x) (Sum.inr i) ↔ x = t := by
  constructor
  · intro h
    rcases h with ⟨x', y', _, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · exact Sum.inl.inj h1
    · simp_all
  · intro h
    subst h
    fin_cases i
    · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- ★★★ 挂边的对称形式。 -/
@[simp] theorem graftGraph_adj_inr_inl {G : SimpleGraph V} {t y : V} {i : Fin 2} :
    (graftGraph G t).Adj (Sum.inr i) (Sum.inl y) ↔ y = t := by
  rw [SimpleGraph.adj_comm]
  exact graftGraph_adj_inl_inr

/-- ★★ 两片新叶之间**没有**边（这正是「度 1」的来源）。 -/
theorem graftGraph_adj_not_inr_inr {G : SimpleGraph V} {t : V} {i j : Fin 2} :
    ¬(graftGraph G t).Adj (Sum.inr i) (Sum.inr j) := by
  intro h
  rcases h with ⟨x', y', _, h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · simp_all
  · simp_all
  · simp_all

end Phylo
