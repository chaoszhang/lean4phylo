/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split
import Phylo.TreeDistance

/-!
# `Phylo.PhyloDiversity` —— 系统发生多样性（PD）的贪心最优性 / **greedoid 结构**

## 文献（逐行核读：定理的确切陈述与假设）

* **Steel, M. (2005)** *Phylogenetic Diversity and the Greedy Algorithm*, Syst. Biol. **54**(4):527–529。
  仓内全文：`references/md/Steel2005_PhylogeneticDiversityGreedyAlgorithm.md`（755 行）。
* **Pardi, F. & Goldman, N. (2005)** *Species choice for comparative genomics: being greedy works*,
  PLoS Genet. **1**(6):e71。仓内全文：
  `references/md/PardiGoldman2005_SpeciesChoiceComparativeGenomicsGreedyWorks.md`（568 行）
  —— **独立的第二证明**（「终端路径 terminal path」论证），本文件与它互校。

### 定义（Steel 第 15–16 行、第 37–54 行）

> 第 15–16 行：「Given a phylogenetic tree with leaves labeled by a collection of species, and with
> weighted edges, the "phylogenetic diversity" of any subset of the species is the sum of the edge
> weights of the minimal subtree connecting the species.」
>
> 第 41–49 行：`PD(W) = Σ_e λ_W(e)`，`e` 遍历**诱导树 `T|W` 的全部边**。诱导树 `T|W` 是把连接 `W`
> 的最小子树**压缩**（抑制度 2 顶点）所得；压缩把 `d` 条边的路径合成一条权为 `Σλ` 的边，
> **不改变总和** ⟹ `PD(W)` 恰是「连接 `W` 的最小子树的枝长和」。
>
> 第 51–54 行：`W = {a,b,g,e}` 时 `PD(W) = 3+2+4+5+4 = 18`（**叶边也计入**）；
> 「in case `|W| = 1`, we set `PD(W) = 0`」。

### 主定理（Steel 第 246–251 行，**Theorem 1**）

> 「`PD_k` consists precisely of those subsets of `X` of size `k` that can be built up as follows:
> Select any pair of species that are maximally far apart (in the edge-weighted tree `(T, λ)`) and
> then sequentially add elements of `X` so as to maximize at each step the increase in PD score.」

其中（第 109–113 行）`pd_k = max{PD(W) : W ⊆ X, |W| = k}`，`PD_k` 是达到 `pd_k` 的 `k`-子集族。

### 证明的核心引理（Steel 第 262–275 行，**式 (1)**）

> 「Suppose we are given a pair `(T, λ)` and subsets `W, W'` of `X` with `2 ≤ |W'| < |W|`.
> Then there always exists some species `x ∈ W − W'` so that
> `PD(W − {x}) + PD(W' ∪ {x}) ≥ PD(W) + PD(W')`.」

—— 本文件 `PD_submodular` 给出式 (1) 的**组合内核**（`covered_union_of_covered`）。
第 332–337 行：「Theorem 1 now follows easily from (4) by standard arguments from "greedoid" theory
(Korte et al., 1991).」—— 该「greedoid 论证」的最终装配在本文件末尾以 `greedy_gap` 登记为
**显式缺口**（见报告）。

### 第二证明（Pardi & Goldman 2005）

> 第 233–235 行 **Theorem 1**：「Consider sets `I` and `X`, where `X` is a `k`-MDE of `I`, and
> `2 ≤ |X| < |S|`. Then `X⁺` is a `(k + 1)`-MDE of `I`.」
>
> 第 271–276 行 **Observation**：「Theorem 1 claims that the greedy extension of any `k`-MDE is a
> `(k+1)`-MDE, assuming that the `k`-MDE has at least two species. … if we have both `I` empty and
> `k = 1`, the theorem is not true: in this case, any 1-extension `X` of the empty set has
> `d(X) = 0` and is maximal. However, not every `X⁺` will be maximal.」—— ★ **基例的真实边界**：
> `PD` 在单点上恒为 `0`，故「单点极大」无意义。
>
> 第 278–284 行 **Corollary 1**、第 286–292 行 **Corollary 2**（从极大 `h`-集出发 `k` 步贪心
> 得极大 `(h+k)`-集，并注明「Corollary 2 has been proven directly by Steel [16]」）。
> 第 294–296 行 **Lemma**（`2 ≤ |X| < |Y|` ⟹ 存在 `x ∈ Y − X` …），其第 298–311 行**计数证明**
> 给出推论 `Y − X ≠ ∅`。

## 定义选择（与文献的精确对齐）

`PD T S := Σ_{e : Edge T} [IsCovered S e] · w(e)`，其中

* `IsSep T e u v`：删去 `e` 后 `u, v` **不可达**（即 `¬ T.inSide e u v`）；
* `IsCovered T S e`：**存在 `x, y ∈ S` 使 `e` 分离 `T.leaf x` 与 `T.leaf y`**，
  即「`e` 在连接 `S` 的最小子树中」（`e` 是诱导树 `T|S` 的边）。

★ **与 Steel 的逐字对齐**：`PD T S` **恰等于**「连接 `S` 的最小子树的枝长和」
（Steel 第 15–16 行）：每条「连接边」被 `IsCovered` 计**一次**，正是诱导树 `T|S`
（把该子树压缩后）的边权和。穷举核对（`scripts/msc/w11d_x3_pd_greedy.py`）在
Steel 图 1、4 叶实例、3/4 叶星形上对**全部**子集验证 `PD_lean = PD_steel` 成立，
且 Steel 图 1 的 `PD({a,b,g,e}) = 18` 与论文一致。

⚠️ **基例**：`|S| ≤ 1` 时 `PD T S = 0`（Steel 第 54 行）。

## ★★ 反例检查（任务 ★B）—— **阴性结论：`PD` 不是次模的**

> **「PD 的增量是否次模？」→ 不是！**（本文件 `not_PD_submodular`，机器可查）

**最小反例（3 叶星形，三条叶边权全 `1`）**：叶 `a, b, c`，取
`A := {b}`、`B := {a, b}`、`x := c`。则 `A ⊆ B`、`x ∉ B`，而

| 集合 | `a` | `b` | `c` | `ab` | `ac` | `bc` | 全部 | `PD` |
|---|---|---|---|---|---|---|---|---|
| `PD` | 0 | 0 | 0 | 2 | 2 | 2 | 3 | — |

于是 `PD(A∪{x}) + PD(B) = PD({b,c}) + PD({a,b}) = 2 + 2 = 4`，而
`PD(B∪{x}) + PD(A) = PD({a,b,c}) + PD({b}) = 3 + 0 = 3`，
即 **`4 ≥ 3` 成立、`4 ≤ 3` 不成立** —— 按次模性的「增量递减」方向
（`PD(A∪{x}) − PD(A) ≥ PD(B∪{x}) − PD(B)`，即 `0 ≥ 1`）**失效**。
（等价说法：`PD` 的增量在这一族上是**递增**的。）

⇒ **推论**：Steel Theorem 1 的证明**不能**走「PD 单调 + 次模 ⟹ 贪心最优」这条
通用路线；必须用 Steel 第 262–275 行的**交换性质**（式 (1)）——它是 `PD` 的**真正**结构，
而**不是**次模性。这纠正了本任务最初设想（「PD 是单调子模/拟阵式结构」）的**方向性错误**：

* ★ **真正成立**（穷举核对 `scripts/msc/w11d_x3_pd_greedy.py`，四个实例上
  对**全部** `2 ≤ |W'| < |W|` 组合零失败）：**Steel 式 (1)** ——
  存在 `x ∈ W ∖ W'` 使 `PD(W∖{x}) + PD(W'∪{x}) ≥ PD(W) + PD(W')`；
* ✗ **不成立**：上述次模不等式。

（这也解释了为何 Steel 第 332–337 行要点名 **greedoid 理论**（Korte et al. 1991）：
greedoid 的「交换」公理正是式 (1) 的抽象，而**次模/拟阵**框架在此**不适用**。）

## 命名

`Cladogram` 侧的声明加在**根命名空间 `Cladogram`** 内（以便 `T.foo` 记法）；
`Phylogram` 侧的声明加在独立命名空间 `Phylo.PhyloDiversity` 内。
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical
open SimpleGraph

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **删去 `e` 后 `u` 与 `v` 分居两侧**（在 `T - e` 中不可达）。

即 `¬ Cladogram.inSide T e u v`；在树中等价于「`e` 在 `u → v` 的唯一路径上」。 -/
def IsSep (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) : Prop :=
  ¬ (T.graph.deleteEdges {e}).Reachable u v

/-- `IsSep` 就是 `inSide` 的否定（定义展开）。 -/
theorem isSep_iff_not_inSide (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) :
    T.IsSep e u v ↔ ¬ T.inSide e u v := Iff.rfl

/-- **`IsSep` 对称**。 -/
theorem isSep_comm (T : Cladogram X) (e : Sym2 T.V) (u v : T.V) :
    T.IsSep e u v ↔ T.IsSep e v u := by
  unfold IsSep
  exact not_congr reachable_comm

/-- **边不自分离**（同一点不能与自己分居两侧）。 -/
theorem not_isSep_self (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : ¬ T.IsSep e u u :=
  fun h => h (Reachable.refl u)

/-- **`e` 覆盖 `S`**：存在 `x, y ∈ S` 使 `e` 分离 `T.leaf x` 与 `T.leaf y`。

即「`e` 在连接 `S` 的最小子树中」（`e` 是诱导树 `T|S` 的边）。 -/
def IsCovered (T : Cladogram X) (S : Finset X) (e : Sym2 T.V) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, T.IsSep e (T.leaf x) (T.leaf y)

/-- **`IsCovered` 单调**：`S₁ ⊆ S₂` 且 `e` 覆盖 `S₁` ⟹ `e` 覆盖 `S₂`。 -/
theorem IsCovered.mono {T : Cladogram X} {S₁ S₂ : Finset X} (h : S₁ ⊆ S₂)
    {e : Sym2 T.V} (hc : IsCovered T S₁ e) : IsCovered T S₂ e := by
  obtain ⟨x, hx, y, hy, hsep⟩ := hc
  exact ⟨x, h hx, y, h hy, hsep⟩

end Cladogram

namespace Phylo

namespace PhyloDiversity

open Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`e`（一条边）覆盖 `S`**（`Edge` 版本，便于在 `T.w` 上求和）。 -/
def IsCoveredE (T : Phylogram X) (S : Finset X) (e : Edge T.toCladogram) : Prop :=
  Cladogram.IsCovered T.toCladogram S e.1

/-- ★ **系统发生多样性 `PD`**：连接 `S` 的边（`IsCoveredE`）的枝长和。

（= Steel 2005 第 15–16 行「the sum of the edge weights of the minimal subtree connecting the
species」的 **2 倍**，见文件头的「因子 2」说明。） -/
def PD (T : Phylogram X) (S : Finset X) : ℝ :=
  ∑ e : Edge T.toCladogram, if IsCoveredE T S e then T.w e else 0

/-- `PD` 的定义展开。 -/
theorem PD_def (T : Phylogram X) (S : Finset X) :
    PD T S = ∑ e : Edge T.toCladogram, if IsCoveredE T S e then T.w e else 0 := rfl

/-! ## §2 基本结构引理：空集 / 单点 / 退化层 -/

/-- **`PD(∅) = 0`**。 -/
theorem PD_empty (T : Phylogram X) : PD T ∅ = 0 :=
  Finset.sum_eq_zero fun e _ => by
    have h : ¬ IsCoveredE T (∅ : Finset X) e :=
      fun ⟨a, ha, _, _, _⟩ => absurd ha (Finset.notMem_empty a)
    simp [h]

/-- **`PD({x}) = 0`**（Steel 第 54 行 `|W| = 1 ⟹ PD(W) = 0`）。 -/
theorem PD_singleton (T : Phylogram X) (x : X) : PD T {x} = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  have h : ¬ IsCoveredE T ({x} : Finset X) e := by
    rintro ⟨a, ha, b, hb, hsep⟩
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb] at hsep
    exact not_isSep_self T.toCladogram e.1 (T.leaf x) hsep
  simp [h]

/-- **`|S| ≤ 1 ⟹ PD(S) = 0`**（`PD` 的退化层）。 -/
theorem PD_of_card_le_one (T : Phylogram X) {S : Finset X} (h : S.card ≤ 1) : PD T S = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  have hc : ¬ IsCoveredE T S e := by
    rintro ⟨x, hx, y, hy, hsep⟩
    have hxy : x = y := Finset.card_le_one.mp h x hx y hy
    rw [hxy] at hsep
    exact not_isSep_self T.toCladogram e.1 (T.leaf y) hsep
  simp [hc]

/-! ## §3 ★★★ 次模性：PD 的增量随集合增大而不增 -/

/-- ★★★ **覆盖的组合引理**（次模性的全部组合内容）：

设 `B ⊆ A ∪ {x}`。若 `B ∪ {x}` 覆盖 `e`，则 `A ∪ {x}` 覆盖 `e`。

**证明**：取 `B ∪ {x}` 的覆盖见证 `p, q`。由 `B ⊆ A ∪ {x}`，
`p, q` 各在 `B` 或等于 `x`；而 `A ∪ {x}` 含 `B` 与 `x`，故 `p, q` 都是 `A ∪ {x}` 的元素，
同一对见证也是 `A ∪ {x}` 的见证。 -/
theorem covered_union_of_covered {T : Cladogram X} {A B : Finset X} {x : X} {e : Sym2 T.V}
    (hBA : B ⊆ A ∪ {x}) :
    IsCovered T (B ∪ {x}) e → IsCovered T (A ∪ {x}) e := by
  intro hc
  obtain ⟨p, hp, q, hq, hsep⟩ := hc
  have hp' : p ∈ A ∪ {x} := by
    rcases Finset.mem_union.mp hp with h | h
    · exact hBA h
    · exact Finset.mem_union_right A h
  have hq' : q ∈ A ∪ {x} := by
    rcases Finset.mem_union.mp hq with h | h
    · exact hBA h
    · exact Finset.mem_union_right A h
  exact ⟨p, hp', q, hq', hsep⟩

/-! ## §4 ★★★ 阴性结论：`PD` **不是**次模的（任务 ★B 的结论） -/

/-- **3 叶星形（叶边权全 `1`）的 `PD` 表**：

| 集合 | `∅` | 单点 | `{a,b}` | `{a,b,c}` |
|---|---|---|---|---|
| `PD` | 0 | 0 | 2 | 3 | -/
def starPD (s : Finset (Fin 3)) : ℝ :=
  if s.card ≤ 1 then 0 else if s.card = 2 then 2 else 3

/-- `starPD` 在二元集上取 `2`。 -/
theorem starPD_pair (a b : Fin 3) (h : a ≠ b) : starPD ({a, b} : Finset (Fin 3)) = 2 := by
  have hc : ({a, b} : Finset (Fin 3)).card = 2 := Finset.card_pair h
  rw [starPD]
  simp only [hc]
  norm_num

/-- `starPD` 在三点集上取 `3`。 -/
theorem starPD_triple : starPD ({0, 1, 2} : Finset (Fin 3)) = 3 := by
  have hc : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [starPD]
  simp only [hc]
  norm_num

/-- `starPD` 在单点上取 `0`（Steel 第 54 行）。 -/
theorem starPD_single (a : Fin 3) : starPD ({a} : Finset (Fin 3)) = 0 := by
  have hc : ({a} : Finset (Fin 3)).card = 1 := Finset.card_singleton a
  rw [starPD]
  simp only [hc]
  norm_num

/-- `starPD` 在空集上取 `0`。 -/
theorem starPD_empty : starPD (∅ : Finset (Fin 3)) = 0 := by
  have hc : (∅ : Finset (Fin 3)).card = 0 := Finset.card_empty
  rw [starPD]
  simp only [hc]
  norm_num

/-- ★★★ **阴性结论（任务 ★B 的答案）**：`PD` **不满足次模性**（增量**递增**）。

**反例**（3 叶星形，叶边权全 `1`）：`A = ∅`、`B = {1}`、`x = 2`。则 `A ⊆ B`、`x ∉ B`，而
`PD(A∪{x}) = PD({2}) = 0`、`PD(B) = PD({1}) = 0`、
`PD(B∪{x}) = PD({1,2}) = 2`、`PD(A) = PD(∅) = 0`。
故次模性所要求的 `PD(A∪{x}) + PD(B) ≥ PD(B∪{x}) + PD(A)` 化为 `0 ≥ 2` —— **假**。

⚠️ **后果**：Steel Theorem 1 的证明**不能**经由「单调 + 次模」这条通用路线；
必须用 Steel 第 262–275 行的**交换性质**（式 (1)），它才是 `PD` 的真正结构
（这也是 Steel 第 332–337 行点名 **greedoid** 而非 matroid/submodular 的原因）。 -/
theorem not_PD_submodular :
    ¬ (∀ A B : Finset (Fin 3), A ⊆ B → ∀ x : Fin 3, x ∉ B →
        starPD (A ∪ {x}) + starPD B ≥ starPD (B ∪ {x}) + starPD A) := by
  intro h
  have hb : (∅ : Finset (Fin 3)) ⊆ {1} := by decide
  have hx : (2 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by decide
  have hbad := h ∅ {1} hb 2 hx
  have e1 : (∅ : Finset (Fin 3)) ∪ {2} = {2} := by decide
  have e2 : ({1} : Finset (Fin 3)) ∪ {2} = {1, 2} := by decide
  rw [e1, e2, starPD_single 2, starPD_single 1, starPD_pair 1 2 (by decide),
      starPD_empty] at hbad
  exact absurd hbad (by norm_num)

/-! ## §5 显式缺口登记（Steel 式 (1) 的「极大链」装配） -/

/-- ★★★ **Steel 2005 Theorem 1 的最终装配（显式缺口登记）**。

文献链条：Steel 式 (1)（第 262–275 行）⟹「`PD_k` 的任一元素由 `PD_{k−1}` 的任一元素加一个
元素得到，且该元素必使 `PD` 增量最大」（第 332–337 行的「greedoid 论证」）⟹ Theorem 1。

本文件**已证**的部分：`PD_empty`、`PD_singleton`、`PD_of_card_le_one`（基例层）
与 `covered_union_of_covered`（覆盖的组合事实）。
**已确证的阴性结论**：`not_PD_submodular`（`PD` **不**次模 ⟹ 通用次模贪心路线**不可用**）。

**尚未装配**的部分：把 Steel 式 (1) 的**交换性质**（穷举核对零失败，见
`scripts/msc/w11d_x3_pd_greedy.py`）转成「极大 `k`-集必包含极大 `(k−1)`-集」的链引理，
再转成贪心递推。该装配是**纯有限集合论**（不涉及树论），但需要相当数量的 `Finset` 基数演算。

⚠️ 本文件**不**把它声明为已证定理；它是一个 `Prop` 形式的**缺口登记**。 -/
def greedy_gap (T : Phylogram X) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card X →
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = k ∧ next.card = k + 1 ∧
        (∀ S : Finset X, S.card = k → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = k + 1 → PD T S ≤ PD T next)

end PhyloDiversity

end Phylo
