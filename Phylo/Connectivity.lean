/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PerfectPhylogeny

/-!
# `Phylo.Connectivity` —— 「连通顶点集」层（W22 任务 B ①：**本文件已收官**）

## 目标（派单顺序第 ① 条）

`BinaryConnectedEqualsSideGap`（`PerfectPhylogeny.lean:475`）：

```text
(∃ ℓ : T.V → Bool, (∀ x, ℓ (T.leaf x) = true ↔ x ∈ A) ∧
    ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s})  ↔  DisplaysBinary T A
```

★ 这是「一件器材通三条」的枢纽（W21 C2 的卡点 ＋ B-1 的卡点 ＋ 多状态判据的最短路径）。

## 本文件交付（★ **B-① 已收口**：`BinaryConnectedEqualsSideGap_holds`）

| 器材 | 用途 | 状态 |
|---|---|---|
| `isConnectedSet_univ` | `univ` 连通 | ✅ |
| `isConnectedSet_empty` | `∅` 连通（空真） | ✅ |
| `inSide_isConnectedSet` | **一条边的叶侧**连通（`⟸` 半的最后一件） | ✅ |
| `SimpleGraph.exists_adj_crossing` | **跨界 walk 必有跨界边**（`⟹` 半取割边） | ✅ |
| `inSide_of_walk_edges_notMem` | 避开 `e` 的 walk ⟹ 同侧（`Walk.toDeleteEdge`） | ✅ |
| `compl_inSide` / `compl_inSide'` | **`e` 一侧的补 = 另一端点一侧** | ✅ |
| `inSide_iff_of_isConnectedSet` | `⟹` 半的引擎：`true` 纤维恰是 `s(x,y)` 的 `x` 侧 | ✅ |
| `displaysBinary_to_connected` | `⟸` 半 | ✅ |
| `connected_to_displaysBinary` | `⟹` 半 | ✅ |
| **`BinaryConnectedEqualsSideGap_holds`** | **缺口本体** | ✅ **收口** |

## ★ W22-2 修正上一轮记录的「卡点」（诚实订正，两者都**不存在**）

上一轮把 `⟹` 半记成两个硬卡点，实际**都是误记**：

1. ~~「需要树中「割边唯一」：两条跨割边拼出圈 ⇒ 与无圈矛盾；库内无圈/连通分析层」~~
   ⇒ **不需要**。给定**一条**跨割边 `s(x,y)` 后，「`ℓ`-真纤维 = `x` 侧」由
   `inSide_or_inSide`（二分性）＋ `not_inSide_both`（互斥性）＋
   `not_reachable_deleteEdges_of_adj`（边是桥）**双向**互含即得，全程不出现「圈」。
2. ~~「`⟹` 半需自建 `SimpleGraph` 无圈论证层」~~ ⇒ 只需 15 行的
   `SimpleGraph.exists_adj_crossing`（`Walk.recOn` 一次归纳）。

★ 教训：判断「缺件」前必须**先查库内已有器材**（`inSide_*` 族在 `Split.lean`、
`not_reachable_deleteEdges_of_adj` 在 `Split.lean:540` 都在此前的「缺件清单」里被漏掉）。
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

/-! ## §2 `⟹` 半与 `⟸` 半的器材（W22 续做）

★ **W22-2 修正上一轮的判断**：上一轮记「`⟹` 半需自建 `SimpleGraph` 无圈论证层」——**过头了**。
库内其实已有三件现成器材：

| 器材 | 位置 | 用途 |
|---|---|---|
| `Cladogram.inSide_or_inSide` | `Split.lean:730` | 删边后每点必与两端点之一同侧（**二分性**） |
| `Cladogram.not_inSide_both` | `Split.lean:750` | 两端点不分居同侧（**互斥性**） |
| `Cladogram.not_reachable_deleteEdges_of_adj` | `Split.lean:540` | 树中每条边是桥（`IsAcyclic` ＋ `isBridge_iff`） |

⇒ **根本不需要「圈」这一层**：唯一需要自建的是「跨界 walk 必有跨界边」这一条组合事实
（本文件 `SimpleGraph.exists_adj_crossing`，15 行），以及「`e` 一侧的补 = 另一端点一侧」。
**「割边唯一」也不必单独证**（上一轮把它列为卡点，实际用不上）：给定**一条**跨割边
`s(x,y)` 后，`{v | ℓ v = true}` 与 `s(x,y)` 的 `x` 侧由上面三件器材**双向**互含。 -/

namespace SimpleGraph

omit [Fintype X] [DecidableEq X] in
/-- ★ **跨界 walk 必有跨界边**：若 `a ∈ U`、`b ∉ U`，则 `a → b` 的 walk 必含一条
一端在 `U` 内、一端在 `U` 外的边，且该边两端都在 walk 的支持集里。

（与 `Phylo.LeafStatus` 的 `Cladogram.exists_adj_crossing` 同一论证，此处对**任意**
`SimpleGraph` 陈述，供 `Cladogram` 层直接用。） -/
theorem exists_adj_crossing {V : Type*} {G : SimpleGraph V} {U : Set V} {a b : V}
    (p : G.Walk a b) (ha : a ∈ U) (hb : b ∉ U) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ x ∈ U ∧ y ∉ U := by
  refine Walk.recOn (motive := fun u v q => u ∈ U → v ∉ U →
      ∃ x ∈ q.support, ∃ y ∈ q.support, G.Adj x y ∧ x ∈ U ∧ y ∉ U) p ?_ ?_ ha hb
  · intro u hu hnu
    exact absurd hu hnu
  · intro u v ww hadj q ih hu hnw
    by_cases hc : v ∈ U
    · obtain ⟨x, hx, y, hy, hadj', hxU, hyU⟩ := ih hc hnw
      exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hadj', hxU, hyU⟩
    · exact ⟨u, Walk.start_mem_support _, v, List.mem_cons_of_mem _ (Walk.start_mem_support q),
        hadj, hu, hc⟩

end SimpleGraph

omit [Fintype X] [DecidableEq X] in
/-- ★ **避开边 `e` 的 walk 落在 `T - e` 里** ⟹ `u` 与 `v` 同侧（`Walk.toDeleteEdge`）。 -/
theorem inSide_of_walk_edges_notMem (T : Cladogram.{u, u} X) {e : Sym2 T.V} {u v : T.V}
    (p : T.graph.Walk u v) (h : e ∉ p.edges) : T.inSide e u v :=
  (p.toDeleteEdge e h).reachable

/-- ★★ **`e` 一侧的补恰是另一端点一侧**（树中删边恰得两个连通分量）。

`⟹` 用二分性 `inSide_or_inSide` 排掉「同侧」那一支；`⟸` 用互斥性 `not_inSide_both`。
★ 这是 `⟹` 半**不需要**「割边唯一」的原因：把「补」直接算成对面端点那一侧。 -/
theorem compl_inSide (T : Cladogram.{u, u} X) {a b u : T.V} (hab : T.graph.Adj a b)
    (hua : T.inSide s(a, b) u a) :
    {v : T.V | ¬ T.inSide s(a, b) u v} = {v : T.V | T.inSide s(a, b) b v} := by
  ext v
  constructor
  · intro hv
    rcases T.inSide_or_inSide hab (x := v) with h | h
    · exact absurd (hua.trans ((T.inSide_comm _ _ _).mp h)) hv
    · exact (T.inSide_comm _ _ _).mp h
  · intro hv hu
    exact T.not_inSide_both hab
      ⟨(T.inSide_comm _ _ _).mp hua, hv.trans ((T.inSide_comm _ _ _).mp hu)⟩

/-- `compl_inSide` 的**对称版**（改由另一端点定侧）。 -/
theorem compl_inSide' (T : Cladogram.{u, u} X) {a b u : T.V} (hab : T.graph.Adj a b)
    (hub : T.inSide s(a, b) u b) :
    {v : T.V | ¬ T.inSide s(a, b) u v} = {v : T.V | T.inSide s(a, b) a v} := by
  ext v
  constructor
  · intro hv
    rcases T.inSide_or_inSide hab (x := v) with h | h
    · exact (T.inSide_comm _ _ _).mp h
    · exact absurd (hub.trans ((T.inSide_comm _ _ _).mp h)) hv
  · intro hv hu
    exact T.not_inSide_both hab
      ⟨hv.trans ((T.inSide_comm _ _ _).mp hu), (T.inSide_comm _ _ _).mp hub⟩

/-- ★★ **`⟹` 半的引擎**：若 `ℓ` 的两个纤维都连通、`x — y` 是一条**跨界边**
（`ℓ x = true`、`ℓ y = false`），则 `true` 纤维恰是 `s(x,y)` 的 `x` 侧顶点集。

两个方向各用一件器材：
* `→`：`S` 连通给出**整条落在 `S` 内**的 walk；它不能走过 `s(x,y)`（否则另一端点 `y`
  会落进 `S`）⇒ 由 `inSide_of_walk_edges_notMem` 得同侧；
* `←`：反设 `ℓ z = false`，`Sᶜ` 连通给出整条落在 `Sᶜ` 内的 walk `z → y`，它同样绕开
  `s(x,y)` ⇒ `z` 同时与 `x`、与 `y` 同侧 ⇒ `x,y` 在 `T - e` 中可达，与「边是桥」矛盾。 -/
theorem inSide_iff_of_isConnectedSet (T : Cladogram.{u, u} X) (ℓ : T.V → Bool)
    (hcon : ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s})
    {x y : T.V} (hxy : T.graph.Adj x y) (hx : ℓ x = true) (hy : ℓ y = false) :
    ∀ z : T.V, (ℓ z = true ↔ T.inSide s(x, y) z x) := by
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := hcon true z hz x hx
    have hedges : s(x, y) ∉ p.edges := by
      intro hmem
      have hys : y ∈ p.support :=
        SimpleGraph.Walk.mem_support_of_mem_edges hmem (by rw [Sym2.mem_iff]; exact Or.inr rfl)
      have h1 : ℓ y = true := hp y hys
      rw [hy] at h1
      exact absurd h1 (by simp)
    exact inSide_of_walk_edges_notMem T p hedges
  · intro hz
    by_contra hnot
    have hzf : ℓ z = false := by
      cases h : ℓ z <;> simp_all
    obtain ⟨q, hq⟩ := hcon false z hzf y hy
    have hedges : s(x, y) ∉ q.edges := by
      intro hmem
      have hxs : x ∈ q.support :=
        SimpleGraph.Walk.mem_support_of_mem_edges hmem (by rw [Sym2.mem_iff]; exact Or.inl rfl)
      have h1 : ℓ x = false := hq x hxs
      rw [hx] at h1
      exact absurd h1 (by simp)
    have hzy : T.inSide s(x, y) z y := inSide_of_walk_edges_notMem T q hedges
    exact T.not_reachable_deleteEdges_of_adj hxy (((T.inSide_comm _ _ _).mp hz).trans hzy)

omit [DecidableEq X] in
/-- ★★ **`⟸` 半**：`DisplaysBinary T A` ⟹ 存在两侧都连通的 `ℓ`。

三个析取项各造一个 `ℓ`：
* `A = ∅` ⇒ `ℓ ≡ false`（`false` 纤维 `univ`、`true` 纤维 `∅`）；
* `A = univ` ⇒ `ℓ ≡ true`（对偶）；
* `T.IsSideOf A`（`A = sideLeaves e u`）⇒ `ℓ v := decide (T.inSide e v u)`，
  两纤维分别是 `u` 侧（`inSide_isConnectedSet`）与它的补（由 `compl_inSide` 化归到
  **另一端点**那一侧，仍是 `inSide_isConnectedSet`）。 -/
theorem displaysBinary_to_connected (T : Cladogram.{u, u} X) (A : Finset X)
    (h : DisplaysBinary T A) :
    ∃ ℓ : T.V → Bool, (∀ x : X, ℓ (T.leaf x) = true ↔ x ∈ A) ∧
      ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s} := by
  classical
  rcases h with hA | hA | hS
  · refine ⟨fun _ => false, ?_, ?_⟩
    · intro x
      rw [hA]
      simp
    · intro s
      cases s
      · have h₁ : {v : T.V | (fun _ : T.V => false) v = false} = Set.univ := by
          ext v; simp
        rw [h₁]; exact isConnectedSet_univ T
      · have h₂ : {v : T.V | (fun _ : T.V => false) v = true} = (∅ : Set T.V) := by
          ext v; simp
        rw [h₂]; exact isConnectedSet_empty T
  · refine ⟨fun _ => true, ?_, ?_⟩
    · intro x
      rw [hA]
      simp
    · intro s
      cases s
      · have h₁ : {v : T.V | (fun _ : T.V => true) v = false} = (∅ : Set T.V) := by
          ext v; simp
        rw [h₁]; exact isConnectedSet_empty T
      · have h₂ : {v : T.V | (fun _ : T.V => true) v = true} = Set.univ := by
          ext v; simp
        rw [h₂]; exact isConnectedSet_univ T
  · obtain ⟨a, b, hab, u, hAu⟩ := hS
    refine ⟨fun v => decide (T.inSide s(a, b) v u), ?_, ?_⟩
    · intro x
      rw [hAu, decide_eq_true_iff, T.mem_sideLeaves_iff_inSide]
      exact T.inSide_comm _ _ _
    · intro s
      cases s
      · have hset : {v : T.V | decide (T.inSide s(a, b) v u) = false}
            = {v : T.V | ¬ T.inSide s(a, b) u v} := by
          ext v
          show (decide (T.inSide s(a, b) v u) = false) ↔ ¬ T.inSide s(a, b) u v
          rw [decide_eq_false_iff_not, T.inSide_comm]
        rw [hset]
        by_cases hua : T.inSide s(a, b) u a
        · rw [compl_inSide T hab hua]
          exact inSide_isConnectedSet T s(a, b) b
        · have hub : T.inSide s(a, b) u b := by
            rcases T.inSide_or_inSide hab (x := u) with h | h
            · exact absurd h hua
            · exact h
          rw [compl_inSide' T hab hub]
          exact inSide_isConnectedSet T s(a, b) a
      · have hset : {v : T.V | decide (T.inSide s(a, b) v u) = true}
            = {v : T.V | T.inSide s(a, b) u v} := by
          ext v
          show (decide (T.inSide s(a, b) v u) = true) ↔ T.inSide s(a, b) u v
          rw [decide_eq_true_iff, T.inSide_comm]
        rw [hset]
        exact inSide_isConnectedSet T s(a, b) u

omit [DecidableEq X] in
/-- ★★ **`⟹` 半**：两侧都连通的 `ℓ` ⟹ `DisplaysBinary T A`。

三分：`ℓ` 恒真 ⇒ `A = univ`；`ℓ` 恒假 ⇒ `A = ∅`；否则取 `ℓ b = true`、`ℓ a = false`
两点，`b → a` 的 walk 必有一条跨界边 `x — y`（`ℓ x = true`、`ℓ y = false`），
再由 `inSide_iff_of_isConnectedSet` 得 `A = sideLeaves s(x,y) x`。 -/
theorem connected_to_displaysBinary (T : Cladogram.{u, u} X) (A : Finset X) (ℓ : T.V → Bool)
    (hℓ : ∀ x : X, ℓ (T.leaf x) = true ↔ x ∈ A)
    (hcon : ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s}) : DisplaysBinary T A := by
  classical
  by_cases huniv : ∀ v : T.V, ℓ v = true
  · exact Or.inr (Or.inl (Finset.eq_univ_of_forall fun x => (hℓ x).mp (huniv (T.leaf x))))
  by_cases hemp : ∀ v : T.V, ℓ v = false
  · refine Or.inl ?_
    ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    have h1 : ℓ (T.leaf x) = true := (hℓ x).mpr hx
    rw [hemp (T.leaf x)] at h1
    exact absurd h1 (by simp)
  · simp only [not_forall] at huniv hemp
    obtain ⟨b, hb⟩ := hemp
    obtain ⟨a, ha⟩ := huniv
    have hb' : ℓ b = true := by cases h : ℓ b <;> simp_all
    have ha' : ℓ a = false := by cases h : ℓ a <;> simp_all
    have haS : ¬ (ℓ a = true) := by rw [ha']; exact by simp
    obtain ⟨p⟩ := T.isTree.connected b a
    obtain ⟨x, -, y, -, hxy, hxU, hyU⟩ :=
      SimpleGraph.exists_adj_crossing (G := T.graph) (U := {v : T.V | ℓ v = true}) p hb' haS
    have hy' : ℓ y = false := by cases h : ℓ y <;> simp_all
    refine Or.inr (Or.inr ⟨x, y, hxy, x, ?_⟩)
    ext z
    have h1 : (T.inSide s(x, y) (T.leaf z) x) ↔ (z ∈ T.sideLeaves s(x, y) x) := by
      rw [T.mem_sideLeaves_iff_inSide, T.inSide_comm]
    exact (hℓ z).symm.trans
      ((inSide_iff_of_isConnectedSet T ℓ hcon hxy hxU hy' (T.leaf z)).trans h1)

omit [DecidableEq X] in
/-- ★★★ **缺口 B-① 收口**：`BinaryConnectedEqualsSideGap`（`PerfectPhylogeny.lean:475`）
——「两个状态类都连通」与「1-类是某条边的叶侧」**等价**（r = 2 时 `IsConnectedSet`
与 `IsSideOf` 一致）。

派单里它是「**一件器材通三条**」的枢纽：`⟸` 半给出「连通」侧的构造，
`⟹` 半给出「连通 ⟹ 边侧」的判定。`def` 本体按纪律**逐字保留**
（`list_gaps.sh` 口径 B 由本定理判定为「已收口」）。 -/
theorem BinaryConnectedEqualsSideGap_holds : BinaryConnectedEqualsSideGap (X := X) := by
  intro T A
  exact ⟨fun ⟨ℓ, hℓ, hcon⟩ => connected_to_displaysBinary T A ℓ hℓ hcon,
    fun h => displaysBinary_to_connected T A h⟩
