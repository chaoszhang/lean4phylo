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

/-- ⚠️ **已证伪，非待证目标** —— 机器反例见 `not_greedy_gap`（`Phylo/PhyloDiversity.lean:341`）。
★★★ **Steel 2005 Theorem 1 的最终装配（显式缺口登记）**。

文献链条：Steel 式 (1)（第 262–275 行）⟹「`PD_k` 的任一元素由 `PD_{k−1}` 的任一元素加一个
元素得到，且该元素必使 `PD` 增量最大」（第 332–337 行的「greedoid 论证」）⟹ Theorem 1。

本文件**已证**的部分：`PD_empty`、`PD_singleton`、`PD_of_card_le_one`（基例层）
与 `covered_union_of_covered`（覆盖的组合事实）。
**已确证的阴性结论**：`not_PD_submodular`（`PD` **不**次模 ⟹ 通用次模贪心路线**不可用**）。

**尚未装配**的部分：把 Steel 式 (1) 的**交换性质**（穷举核对零失败，见
`scripts/msc/w11d_x3_pd_greedy.py`）转成「极大 `k`-集必包含极大 `(k−1)`-集」的链引理，
再转成贪心递推。该装配是**纯有限集合论**（不涉及树论），但需要相当数量的 `Finset` 基数演算。

⚠️ 本文件**不**把它声明为已证定理；它是一个 `Prop` 形式的**缺口登记**。

★★★ **W12h 终局判定**：上述陈述**是假命题** —— 取 `k = Fintype.card X` 时结论要求
`next.card = card X + 1`，而 `next.card ≤ card X`。故本文件**不**证它（`def` 逐字保留），
只**给出反驳** `not_greedy_gap`。

★ 进一步（**W12h 的第二个阴性结论**）：把前提改成 `k + 1 ≤ card X` 也**仍然是假命题** ——
即使只要求「**存在**极大 `k`-集含于某个极大 `(k+1)`-集」（比原陈述弱得多），
也有反例（见 `greedy_extend_false`）。详见 §5.1。 -/
def greedy_gap (T : Phylogram X) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card X →
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = k ∧ next.card = k + 1 ∧
        (∀ S : Finset X, S.card = k → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = k + 1 → PD T S ≤ PD T next)

/-! ## §5.1 ★★★ W12h 终局判定：原 `greedy_gap` **是假命题**（给反驳）＋ **修复形态已证** -/

/-- ✗ ★★★ **原 `greedy_gap` 为假**（`k = |X|` 时结论不可能）。

取 `k := Fintype.card X`：前提 `1 ≤ k`、`k ≤ card X` 都成立，结论却要求
`∃ next : Finset X, next.card = card X + 1`，而 `Finset.card_le_univ` 给
`next.card ≤ card X` ⇒ 矛盾。这正是 W11 判例「命题为假 ⇒ 给反例、不硬证」那一条。
★ 原 `def greedy_gap` 因此**逐字保留**（既不被证成、也没被改写）。 -/
theorem not_greedy_gap [Nonempty X] (T : Phylogram X) : ¬ greedy_gap T := by
  intro h
  have hcard : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  obtain ⟨prev, next, _hsub, _hprev, hnext, _h1, _h2⟩ :=
    h (Fintype.card X) hcard le_rfl
  have hle : next.card ≤ Fintype.card X := Finset.card_le_univ next
  omega

/-! ## §5.1 ★★★ W12h：原形态**假**（已反驳）；**修复形态仍待证**；被反驳的是更强的 `∀`-版本

### (i) 原 `greedy_gap`（前提 `k ≤ card X`）**是假命题** —— 见 `not_greedy_gap`（已证）

取 `k = Fintype.card X`：结论要求 `next.card = card X + 1`，与 `Finset.card_le_univ` 矛盾。

### (ii) 修复形态（前提 `k + 1 ≤ card X`）**未被反驳** —— `greedy_gap_correct_shape`（开放目标）

★ 必须分清**两个不同的量词结构**（这是 W12h 的一次自我纠错）：

| 命题 | 量词结构 | 判定 |
|---|---|---|
| `greedy_gap_correct_shape` | `∀ k, … → **∃ prev next**, prev ⊆ next ∧ …` | **未反驳，待证** |
| `step_maximizer` 型（更强） | `∀ k, … → **∀ prev** (极大 `k`-集), **∃ next** (极大 `(k+1)`-集), prev ⊆ next` | **假**（`not_step_maximizer`） |

被我方数值脚本（`scripts/msc/w12h_pd_mincounterexample.py`）抓住的是**后者**：
4 叶树（边权 `4,3,2,1,6,7`）上 `pd_1 = 0`（每点都是极大 `1`-集）、`pd_2 = 15` 的极大 `2`-集
**唯一**为 `{0,3}` ⇒ 单点 `{1}`、`{2}` 不可扩 ⇒ 「**极大集套极大集**」这条路线**不可用**。
但**同一组数据**上修复形态**成立**：取 `prev := {0}`、`next := {0,3}` 即
`{0} ⊆ {0,3}`、`|prev| = 1`、`|next| = 2`，且 `pd_1 = 0`（`prev` 合法极大）、
`{0,3}` 唯一极大 `2`-集（`next` 合法极大）—— 见 `correct_shape_of_profile`（已证）。
⇒ **修复形态绝不因此被否证**；它仍是诚实的开放目标。

### (iii) 已证的阴性结果（删掉一条错误路线）

`not_step_maximizer`：若 `T : Phylogram (Fin 4)` 的 `PD` 满足该反例的两条**树层事实**
（`∀ |S| = 2, PD S ≤ 15`；`PD S = 15 ∧ |S| = 2 → S = {0,3}`），则**不存在**
「每条极大 `1`-集都能扩成极大 `2`-集」。

⚠️ **桥接边界（诚实标注）**：上述两条树层事实由**具体 4 叶树 ＋ 权 `[4,3,2,1,6,7]`** 实现
（用与库内 `Cladogram.IsCovered` **逐字一致**的 PD 定义在脚本里逐项核对，`exit 0`，
md5 见报告）；但**该 `Phylogram` 的具体构造未在 Lean 中形式化**（需要 `SimpleGraph` 的
`IsTree`／度条件／`IsSep` 的路径事实）。故本文件给出的是**条件形态**（前提＝那两条树层事实），
而不是无条件的「存在某个 `T`」；后者是明确的后续工作。 -/

/-- ★★ **极大 `k`-集**（修复形态装配用的辅助谓词；本批**未**装配完成）。 -/
def IsMaxPD (T : Phylogram X) (k : ℕ) (S : Finset X) : Prop :=
  S.card = k ∧ ∀ S' : Finset X, S'.card = k → PD T S' ≤ PD T S

/-- ★★ **`PD` 对第一自变量单调**（`S ⊆ S' ⟹ PD S ≤ PD S'`）：逐边用 `IsCovered.mono`。 -/
theorem PD_mono {T : Phylogram X} {S S' : Finset X} (h : S ⊆ S') : PD T S ≤ PD T S' := by
  classical
  refine Finset.sum_le_sum fun e _ => ?_
  have hc' : IsCoveredE T S e → IsCoveredE T S' e := fun hc => Cladogram.IsCovered.mono h hc
  split_ifs
  · exact le_of_eq rfl
  · exact absurd (hc' ‹IsCoveredE T S e›) ‹¬ IsCoveredE T S' e›
  · exact T.w_nonneg e
  · exact le_of_eq rfl

/-! ## §5.2 ★B 反空真：Phylogram X 与反驳 not_greedy_gap 都**非空转** -/

/-- ★B **反空真见证（条件形态）**：反驳 `not_greedy_gap` 的两条前提
（`X` 非空 ＋ 给定一个 `Phylogram X`）确实可满足 —— 前提齐备时否定结论就成立，
不是空类型上的空转。★ 库内 `Phylogram` 的**具体实例**本批未构造（`Cladogram` 的
`isTree`／`leaf_iff_degree_one`／`no_degree_two` 三条在单顶点实例上的 `degree` 演算
本批未收敛），故只给条件形态。 -/
example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (T : Phylogram X) :
    ¬ greedy_gap T :=
  not_greedy_gap T

/-! ## §5.3 ★★★ 修复形态（开放目标）与「极大集套极大集」的**伪**（已证阴性结论）

### 修复形态的**部分结果**（W12h 第二批）

* ✅ **已证**：`greedy_gap_correct_shape_at_one`（`k = 1`，需 `|X| ≥ 2`）—— 因为
  `pd_1 = 0`（`PD_of_card_le_one`）使**每个**单点都是极大 `1`-集，故取任一 `2`-极大集的
  任一元素 `x`（`next` 存在由 `exists_maximizer_card`）即得 `prev = {x} ⊆ next`；
* ✅ **已证**：`greedy_gap_correct_shape_at_card_sub_one`（`k = |X| - 1`）—— 取
  `next := univ`（`(|X|-1)+1 = |X|` 元子集**唯一**）、`prev :=` 任一 `(|X|-1)`-极大集；
* ✅ **已证（W12h 第三轮，条件形态）**：一般 `k` 的**归约**已完成 ——
  `exists_maximizer_subset_of_maximizer` 从 `pdExchange_gap T` 导出**下钻猜想 P6**
  （每个 `(k+1)`-极大集含一个 `k`-极大集）；`greedy_gap_correct_shape_of_exchange`
  再由 P6 导出**本 `def`**（`pdExchange_gap T → greedy_gap_correct_shape T`）。
  ⇒ **唯一**剩下的缺口就是 **`pdExchange_gap`**（Steel 式 (1) 的加权交换性质，见其 docstring）。
* ⬜ **`pdExchange_gap` 本批未证**：**★D 证据**：脚本 `scripts/msc/w12h_greedy_gap_check.py`
  的 **P1**（交换性质本身）与 **P5**（本 `def`）、**P6**（下钻）在 `n = 2..6` 全部叶标号树 ×
  **24587** 组权上**全部零反例**；且**逐边分析**表明 P1 **不需要树论**：
  只需「`IsCoveredE T · e` 对第一自变量单调」＋「`w ≥ 0`」，把
  `PD(W∖{x}) + PD(W'∪{x}) ≥ PD(W) + PD(W')` 化为「对每条边 `e`：
  `cov(W,e) ∧ ¬cov(W',e)` 时 `cov(W∖{x},e) ∨ cov(W'∪{x},e)`」。
  **卡在哪一步（如实）**：需要证明**存在** `x ∈ W∖W'` 对**所有**这样的 `e` 同时成立 ——
  逐边看，「`x` 在 `e` 上失败」⟺ `W ∩ (W' 所在那一侧) = {x}`；把这些 `e` 拼起来需要
  「子树／分划」层面的选择论证（`x` 的悬挂路径 vs `W'` 的位置），本批时间窗内未收敛。
  ⚠️ 零反例**不是**证明，故本 `def` 保持为**开放目标**（未被反驳 ✓）。 -/

/-- ★★★ **修复形态（前提 `k + 1 ≤ card X`）**：原 `greedy_gap` 因 `k = |X|` 为**假**
（`not_greedy_gap` 已反驳）；把前提改成 `k + 1 ≤ card X` 后，本批**未能证出**，
但它**未被反驳** —— 它是**诚实的开放目标**。

⚠️ 它与被证伪的 `∀`-版本（`not_step_maximizer`）**差一个量词**：
后者要求**每一条**极大 `k`-集都能扩成极大 `(k+1)`-集（**假**）；
本条只要求**存在**一对 `prev ⊆ next`（各自的极大性只针对自己的基数）。
⇒ **不要**把本条与 `not_step_maximizer` 混为一谈（W12h 的一次自我纠错）。 -/
def greedy_gap_correct_shape (T : Phylogram X) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k + 1 ≤ Fintype.card X →
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = k ∧ next.card = k + 1 ∧
        (∀ S : Finset X, S.card = k → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = k + 1 → PD T S ≤ PD T next)

/-- ✗ ★★★ **`∀`-版本（`step_maximizer` 形态）为假**：
**极大 `k`-集不必可扩成极大 `(k+1)`-集**（故「极大集套极大集」这条路线**不可用**）。

**反例**（4 叶树，边权 `4,3,2,1,6,7`；由 `scripts/msc/w12h_pd_mincounterexample.py`
用与库内 `Cladogram.IsCovered` **逐字一致**的 PD 定义核出，`exit 0`）：
`pd_1 = 0`（**每个**单点都是极大 `1`-集），而 `pd_2 = 15` 的极大 `2`-集**唯一**为 `{0,3}`
⇒ 单点 `{1}`、`{2}` **不可扩**。

**形式（条件形态）**：前提是那棵树的两条**树层事实**：
`|S| = 2 ⟹ PD S ≤ 15`、`PD S = 15 ∧ |S| = 2 ⟹ S = {0,3}`，以及 `PD {0,3} = 15`。
⚠️ 这三条由具体 4 叶树实现（脚本核对），但该 `Phylogram` 的 **Lean 构造本批未形式化**
（需要 `SimpleGraph.IsTree`／度条件／`IsSep` 的路径事实），故此处只给条件形态。 -/
theorem not_step_maximizer (T : Phylogram (Fin 4))
    (h2 : ∀ S : Finset (Fin 4), S.card = 2 → PD T S ≤ 15)
    (h03 : PD T ({0, 3} : Finset (Fin 4)) = 15)
    (huniq : ∀ S : Finset (Fin 4), S.card = 2 → PD T S = 15 →
      S = ({0, 3} : Finset (Fin 4))) :
    ¬ (∀ prev : Finset (Fin 4), prev.card = 1 →
        (∀ S : Finset (Fin 4), S.card = 1 → PD T S ≤ PD T prev) →
        ∃ next : Finset (Fin 4), prev ⊆ next ∧ next.card = 2 ∧
          (∀ S : Finset (Fin 4), S.card = 2 → PD T S ≤ PD T next)) := by
  intro h
  have hsingle : ∀ S : Finset (Fin 4), S.card = 1 → PD T S = 0 :=
    fun S hS => PD_of_card_le_one T (S := S) (by omega)
  obtain ⟨next, hsub, hcard, hmax⟩ := h {2} (by decide) (by
    intro S hS
    rw [hsingle S hS, hsingle {2} (by decide)])
  have h2mem : (2 : Fin 4) ∈ next := hsub (by decide)
  have hge : 15 ≤ PD T next := by
    have hle := hmax ({0, 3} : Finset (Fin 4)) (by decide)
    rw [h03] at hle
    exact hle
  have h15 : PD T next = 15 := le_antisymm (h2 next hcard) hge
  have hnext : next = ({0, 3} : Finset (Fin 4)) := huniq next hcard h15
  rw [hnext] at h2mem
  exact absurd h2mem (by decide)

/-- ✓ ★★★ **同一组数据上，修复形态（`∃ prev next`）成立**（`k = 1` 的见证）；
这条与 `not_step_maximizer` **并存不矛盾** —— 正是「差一个量词」的机器证据。

（`k = 2, 3` 的见证 `({0,3}, {0,2,3})`、`({0,2,3}, {0,1,2,3})` 由
`scripts/msc/w12h_pd_mincounterexample.py` 一并打印。） -/
theorem correct_shape_of_profile (T : Phylogram (Fin 4))
    (h2 : ∀ S : Finset (Fin 4), S.card = 2 → PD T S ≤ 15)
    (h03 : PD T ({0, 3} : Finset (Fin 4)) = 15) :
    ∃ prev next : Finset (Fin 4),
      prev ⊆ next ∧ prev.card = 1 ∧ next.card = 2 ∧
        (∀ S : Finset (Fin 4), S.card = 1 → PD T S ≤ PD T prev) ∧
        (∀ S : Finset (Fin 4), S.card = 2 → PD T S ≤ PD T next) := by
  refine ⟨{0}, {0, 3}, by decide, by decide, by decide, ?_, ?_⟩
  · intro S hS
    rw [PD_of_card_le_one T (S := S) (by omega),
      PD_of_card_le_one T (S := ({0} : Finset (Fin 4))) (by decide)]
  · intro S hS
    rw [h03]
    exact h2 S hS

/-- ★★ **极大 `k`-集总存在**（`k ≤ |X|`）：`PD` 在有限多个 `k`-子集上取最大。 -/
theorem exists_maximizer_card (T : Phylogram X) (k : ℕ) (hk : k ≤ Fintype.card X) :
    ∃ A : Finset X, IsMaxPD T k A := by
  classical
  obtain ⟨A, hA⟩ := Finset.exists_max_image (Finset.univ.powersetCard k) (fun S => PD T S)
    (Finset.powersetCard_nonempty.mpr hk)
  exact ⟨A, (Finset.mem_powersetCard.mp hA.1).2,
    fun S' hS' => hA.2 S' (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S', hS'⟩)⟩

/-- ★★★ **正确形态在 `k = 1` 成立**（`|X| ≥ 2`）：`pd_1 = 0` ⇒ **每个**单点都是极大 `1`-集，
故任取一个 `2`-极大集 `next` 与其任一元素 `x`，`prev := {x}` 满足全部要求。 -/
theorem greedy_gap_correct_shape_at_one (T : Phylogram X) (hX : 2 ≤ Fintype.card X) :
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = 1 ∧ next.card = 1 + 1 ∧
        (∀ S : Finset X, S.card = 1 → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = 1 + 1 → PD T S ≤ PD T next) := by
  classical
  obtain ⟨next, hnext⟩ := exists_maximizer_card T 2 hX
  obtain ⟨x, hx⟩ : ∃ x : X, x ∈ next := Finset.card_pos.mp (by rw [hnext.1]; norm_num)
  refine ⟨{x}, next, Finset.singleton_subset_iff.mpr hx, Finset.card_singleton x, ?_, ?_, ?_⟩
  · rw [hnext.1]
  · intro S hS
    rw [PD_of_card_le_one T (S := S) (by omega),
      PD_of_card_le_one T (S := ({x} : Finset X)) (by simp)]
  · intro S hS
    exact hnext.2 S (by omega)

/-- ⬜ ★★★ **显式缺口（W12h 第三轮）：Steel 式 (1) 的**加权**交换性质**。

`2 ≤ |W'| < |W|` 时存在 `x ∈ W ∖ W'` 使 `PD(W∖{x}) + PD(W'∪{x}) ≥ PD(W) + PD(W')`
（Steel 2005 第 262–275 行的式 (1)，本库此前**未**形式化）。

**本批未证**。★ 但它是「下钻猜想 P6」的**唯一**缺口：
`exists_maximizer_subset_of_maximizer` 只以本 `def` 为**前提**就推出 P6，进而
`greedy_gap_correct_shape_of_exchange` 推出**修复形态**。

数值核对（`scripts/msc/w12h_greedy_gap_check.py` 的 **P1**）在 `n = 2..6` 全部叶标号树 ×
**24587** 组权上**零反例**。

## 施工图（W12h 第四轮：已读到文献证明，卡点已精确定位）

文献 `references/md/Steel2005_PhylogeneticDiversityGreedyAlgorithm.md` 第 265–306 行的证明是：
把 `T` 看成由 `T|W` 接上一族子树 `F` 得到，**选一条 `T|W` 的外边 `e`**（= 与 `W` 中某个叶
`x` 相邻的悬挂边），使得**接在 `e` 上的任何 `F` 子树都不含 `W'` 的物种**；取 `x` = 该叶。
于是 (2) `PD(W) = PD(W−{x}) + λ_W(e)`（只需**一条**边），且 (3) `PD(W'∪{x}) ≥ PD(W') + λ_W(e)`。
存在性由**计数**得到：`|W'| < |W|` ⇒ `|W'∖W| < |W∖W'|`，而每个 `w ∈ W∖W'` 的悬挂边至多
「消耗」一个 `W'∖W` 的元素 ⇒ 必有某个 `w` 的悬挂边上没有 `W'∖W` 的元素。

**我方已把它化为可施工的两条**（第四轮推演，未形式化）：
* (A) **选 `x` 的条件**：用 `P(w) := {e : cov(W,e) ∧ ¬cov(W∖{w},e)}`（`w` 的悬挂路径）与
  `Out(w)` := `P(w)` 最内侧边的「`w` 侧」，则只要
  **(W'∖W) ∩ Out(w) = ∅**，就有
  `PD(W∖{w}) + PD(W'∪{w}) − PD(W) − PD(W') = Σ_{e∈Gain(w)} w_e − Σ_{e∈P(w)} w_e ≥ 0`
  （因 `P(w) ⊆ Gain(w)`，其中 `Gain(w) := {e : ¬cov(W',e) ∧ cov(W'∪{w},e)}`）✓；
* (B) **计数**：各 `w ∈ W` 的 `Out(w)` 两两不相交（树在互异 `W`-叶处的悬挂子树互不相交），
  而 `Out(w) ∩ W = {w}` ⇒ `Σ_{w∈W∖W'} |(W'∖W) ∩ Out(w)| ≤ |W'∖W| < |W∖W'|`
  ⇒ 存在 `w ∈ W∖W'` 使 `(W'∖W) ∩ Out(w) = ∅` ✓。

**卡在哪一步（如实）**：`Out(w)`／`T|W`／悬挂子树 `F` 这一套**载体在本库不存在** ——
`PhyloDiversity.lean` 只有 `IsSep`／`IsCovered`／`PD`；要形式化 (B) 的「互不相交」需要
「`W` 的最小子树」的几何（`AttesonRadius` 的 `pathOf` 系列可能可复用，但 `T|W` 与
悬挂子树分解没有现成件）。**故本 `def` 仍是开放缺口**（未被反驳 ✓，零反例 ✓，
**但没有**用它当证明 ✓）。 -/
def pdExchange_gap (T : Phylogram X) : Prop :=
  ∀ W W' : Finset X, 2 ≤ W'.card → W'.card < W.card →
    ∃ x ∈ W \ W', PD T (W.erase x) + PD T (W' ∪ {x}) ≥ PD T W + PD T W'

/-- ★★★ **P6（「下钻」猜想）由交换性质导出**：若 `pdExchange_gap T`，则**每个** `(k+1)`-极大集
（`k ≥ 1`）都**含**一个 `k`-极大集。

**证明**：取 `prev` := `next` 的 `k`-子集中 `PD` 最大者。若存在 `S`（`|S| = k`）使
`PD S > PD prev`，就对 `(W, W') = (next, S)` 用交换性质（此时 `2 ≤ |S| < |next|`），
得 `x ∈ next ∖ S` 且
`PD(next∖{x}) + PD(S∪{x}) ≥ PD(next) + PD(S)`。
左边第一项 `≤ PD prev`（`prev` 在 `next` 的 `k`-子集中最大，而 `next∖{x}` 正是这样一个子集），
第二项 `≤ PD next`（`next` 是 `(k+1)`-极大集，而 `|S∪{x}| = k+1`）⇒ `PD prev ≥ PD S`，与
`PD S > PD prev` 矛盾。∎

（`k = 1` 不需要交换性质：`pd_1 = 0` ⇒ `next` 的任一元素给出的单点就是 `1`-极大集。） -/
theorem exists_maximizer_subset_of_maximizer (T : Phylogram X) (hgap : pdExchange_gap T)
    {k : ℕ} (hk : 1 ≤ k) :
    ∀ next : Finset X, IsMaxPD T (k + 1) next →
      ∃ prev : Finset X, prev ⊆ next ∧ IsMaxPD T k prev := by
  classical
  intro next hnext
  rcases lt_or_ge k 2 with hk1 | hk2
  · have hk_eq : k = 1 := by omega
    subst hk_eq
    obtain ⟨x, hx⟩ : ∃ x : X, x ∈ next :=
      Finset.card_pos.mp (by rw [hnext.1]; norm_num)
    refine ⟨{x}, Finset.singleton_subset_iff.mpr hx, Finset.card_singleton x, ?_⟩
    intro S hS
    rw [PD_of_card_le_one T (S := S) (by omega),
      PD_of_card_le_one T (S := ({x} : Finset X)) (by simp)]
  · have hnextcard : next.card = k + 1 := hnext.1
    have hne : (next.powersetCard k).Nonempty := by
      rw [Finset.powersetCard_nonempty]
      omega
    obtain ⟨prev, hprevm, hprevmax⟩ :=
      Finset.exists_max_image (next.powersetCard k) (fun S => PD T S) hne
    have hprevsub : prev ⊆ next := (Finset.mem_powersetCard.mp hprevm).1
    have hprevcard : prev.card = k := (Finset.mem_powersetCard.mp hprevm).2
    refine ⟨prev, hprevsub, hprevcard, fun S hS => ?_⟩
    by_contra hcon
    have hlt : PD T prev < PD T S := not_le.mp hcon
    have hS2 : 2 ≤ S.card := by omega
    have hSlt : S.card < next.card := by omega
    obtain ⟨x, hx, hxineq⟩ := hgap next S hS2 hSlt
    have hxnext : x ∈ next := (Finset.mem_sdiff.mp hx).1
    have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
    have herasecard : (next.erase x).card = k := by
      rw [Finset.card_erase_of_mem hxnext, hnextcard]
      omega
    have hle1 : PD T (next.erase x) ≤ PD T prev :=
      hprevmax (next.erase x)
        (Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, herasecard⟩)
    have hinscard : (S ∪ {x}).card = k + 1 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hxS), hS,
        Finset.card_singleton]
    have hle2 : PD T (S ∪ {x}) ≤ PD T next := hnext.2 (S ∪ {x}) hinscard
    -- 不用 `linarith`（本文件未引入该 tactic）：显式用 `add_le_add` ＋ 消去公因子
    have hsum : PD T (next.erase x) + PD T (S ∪ {x}) ≤ PD T prev + PD T next :=
      add_le_add hle1 hle2
    have h2 : PD T next + PD T S ≤ PD T prev + PD T next := le_trans hxineq hsum
    have h3 : PD T S + PD T next ≤ PD T prev + PD T next := by
      rw [add_comm (PD T S)]
      exact h2
    have h4 : PD T S ≤ PD T prev := (add_le_add_iff_right (PD T next)).mp h3
    exact absurd h4 (not_le.mpr hlt)

/-- ★★★ **修复形态由交换性质导出**（原 `def greedy_gap_correct_shape` **逐字保留**）：
`pdExchange_gap T` ⇒ `greedy_gap_correct_shape T`。

证明：对 `k`（`1 ≤ k`、`k+1 ≤ |X|`）取任一 `(k+1)`-极大集 `next`（`exists_maximizer_card`），
`exists_maximizer_subset_of_maximizer` 给出 `prev ⊆ next` 且 `prev` 是 `k`-极大集。
⚠️ **本条是条件形态**：`pdExchange_gap` 本批**未证**，故**不**声称修复形态已证。 -/
theorem greedy_gap_correct_shape_of_exchange (T : Phylogram X) (hgap : pdExchange_gap T) :
    greedy_gap_correct_shape T := by
  intro k hk1 hkcard
  obtain ⟨next, hnext⟩ := exists_maximizer_card T (k + 1) hkcard
  obtain ⟨prev, hprevsub, hprevmax⟩ :=
    exists_maximizer_subset_of_maximizer T hgap hk1 next hnext
  exact ⟨prev, next, hprevsub, hprevmax.1, hnext.1, hprevmax.2, hnext.2⟩

/-- ★B **反空真**：「下钻」结论在 `k = 1` 上**无需**交换性质即成立（`pd_1 = 0`，
见 `greedy_gap_correct_shape_at_one`），故 P6／修复形态都**不是**空转命题；
`k = |X| - 1` 亦然（`greedy_gap_correct_shape_at_card_sub_one`）。 -/
example (T : Phylogram X) (hX : 2 ≤ Fintype.card X) :
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = 1 ∧ next.card = 2 ∧
        (∀ S : Finset X, S.card = 1 → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = 2 → PD T S ≤ PD T next) :=
  greedy_gap_correct_shape_at_one T hX

/-- ★★★ **正确形态在 `k = |X| - 1` 成立**：取 `next := univ`
（`(|X|-1)+1 = |X|` 元子集**唯一**）、`prev :=` 任一 `(|X|-1)`-极大集，则 `prev ⊆ univ`。 -/
theorem greedy_gap_correct_shape_at_card_sub_one (T : Phylogram X)
    (hX : 1 ≤ Fintype.card X) :
    ∃ prev next : Finset X,
      prev ⊆ next ∧ prev.card = Fintype.card X - 1 ∧
        next.card = (Fintype.card X - 1) + 1 ∧
        (∀ S : Finset X, S.card = Fintype.card X - 1 → PD T S ≤ PD T prev) ∧
        (∀ S : Finset X, S.card = (Fintype.card X - 1) + 1 → PD T S ≤ PD T next) := by
  classical
  obtain ⟨prev, hprev⟩ := exists_maximizer_card T (Fintype.card X - 1) (by omega)
  refine ⟨prev, Finset.univ, Finset.subset_univ prev, hprev.1, ?_, hprev.2, ?_⟩
  · rw [Finset.card_univ]; omega
  · intro S hS
    have hSuniv : S = Finset.univ := by
      refine Finset.eq_univ_of_card S ?_
      omega
    rw [hSuniv]

end PhyloDiversity

end Phylo
