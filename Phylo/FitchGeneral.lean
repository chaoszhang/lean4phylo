/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Phylo.Core
import Phylo.Stat.Parsimony

/-!
# `Phylo.FitchGeneral` —— Fitch 算法 / Fitch 代价的一般形式（任意状态数）

本文件把库内 **4 元集 · 2 状态（`Bool`）版** `Pattern.fitchCost_eq`
（`Phylo/Stat/Parsimony.lean:75`）沿两个轴推广：

* **状态数轴**：`α` 任意有限非空类型（库内版硬编码 `Bool`）；
* **分支数轴**：任意多个孩子（库内版只有两个孩子）—— 但**规则要换**，见下。

## 文献出处（Fitch 1971，本库 OCR 副本 `references/md/Fitch1971_TowardDefiningCourseOfEvolution.md`）

* **下到上递推（preliminary phase）**：第 487–497 行 ——
  「The preliminary nodal set shall be comprised of all characters (nucleotides) common to both
  immediately descendent sets; if none are common to both, then the preliminary nodal set will be
  comprised of all characters found in either. In mathematical terms, the nodal set is the
  intersection of its immediately descendent sets if the intersection exists (i.e., is not empty)
  otherwise it is the union of those sets.」
  ⇒ 本文件 `pair` / `best_pair`（★★★，**二叉**结点 = 交集非空取交、否则取并）。
* **并集数 = 最少突变数**：第 659–665 行 ——
  「counting the number of unions gives one the minimum number of fixations (or changes of state)
  required to account for descendent nucleotides (characters) from a common ancestor, given the
  phylogeny assumed at the outset.」
  ⇒ 本文件 `extra`（并集计数）/ `minExtra`（其最小者）。
* **最终相（final phase）**：第 864–900 行的六步规则（`I.`–`VI.`，用祖先信息修正祖先结点赋值）。
  **本文件的所有定理只用前两处**（preliminary 规则 + 并集计数）——「最少突变数」由 preliminary 相
  决定；final 相的规则在本文件的任何陈述里都不出现。
* 行号来自本库 OCR 副本 `references/md/Fitch1971_TowardDefiningCourseOfEvolution.md`（2228 行），
  **已逐句回查**（⚠️ OCR 有连续双空格，用单词 grep 才命中，逐字 grep 会漏）。

## ⚠️ 本文件对上一版的两处**更正**（都是「文档/陈述说错」，见 `MEMORY.md`）

1. **上一版的 `extra_pair` 陈述是假命题**。当时写的是
   `extra ({S,U} : Finset (Finset α)) s = [s∉S] + [s∉U]`（**无** `S ≠ U` 假设）——
   `S = U` 时左边只数到一个集合：反例 `α = Bool`、`S = U = {true}`、`s = false` 时**左 = 1、右 = 2**。
   ⇒ 根治办法不是补 `S ≠ U`，而是**换表示**：把孩子集合按**下标**（每个孩子一个下标）记账，
   见下面的 `extra`。**教训**：一个证不出来的引理，先花五分钟试造反例。
2. **`Finset (Finset α)` 表示会「去重」**，从而在 **polytomy（≥ 4 个孩子）上低估代价**：
   4 个孩子状态 `a,a,b,b` 时真最优增量 = **2**，而集合去重后只剩 `{{a},{b}}`、给出 **1**。
   ⇒ 同样由下标版 `extra` 根治（见 `star_aabb_minExtra`）。

## ✅ 本批已证（零 `sorry`、零新公理）

* ★★★ `best_pair` —— **Fitch 1971 的二叉规则**（任意状态数 `α`，交集非空取交、否则取并）；
* ★★ `minExtra_pair` / `extra_pair` —— 二叉结点的代价增量（**任意状态数**，无需 `S ≠ U`）；
* ★★ `minExtra_add` —— **Fitch 递推的心脏恒等式**
  `min_t ([t∉S] + [t≠s]) = [s∉S]`（有了它，`minCost v`（不含父边）与「根态 = s 时的最优代价」
  才接得上，是树层递推的引擎）；
* ★★ 边界反例 `pairFoldCost_aabb` / `pairFoldCost_abab` / `star_aabb_minExtra` ——
  **「逐对并集」规则在 polytomy 上不是最优、且依赖折叠顺序**（`1` vs `2`；真最优 `2`）。
  ⇒ Fitch 1971 的逐对规则**只对二叉结点**成立；一般分支数必须改用 `best` / `minExtra`。
* ★★ **树层的组合机制**（`GenTree` / `children` / `desc`，已证）：
  * `desc v = {v} ∪ ⋃_{u ∈ children v} desc u`（`desc_eq_insert_biUnion`）、
    **不同孩子的子树两两不交**（`desc_pairwise_disjoint`）、`desc root = univ`（`desc_root`）、
    非 `root` 顶点必有父（`parent_eq_none_iff`）；
  * 燃料引理 `depth_lt_of_parStep`（祖先链上高度严格上升，`depth` 是**从叶往上数**的高度）；
  * 自底向上递推的**定义**（`WellFounded.fix`）：`fitchSet`（= `S_v`）、`fitchCost`（= `c_v`）、
    `insideCost`，以及它们的展开引理（叶 / 内部）。
* ★★ **树层的下界（ii）与两条桥**（已证）：
  * `minExtra_add_le`：`minExtra sets + [s ∉ best sets] ≤ extra sets t + [t ≠ s]`
    —— 结点层的下界引擎（**只能是不等式**，见下节的数值反例）；
  * `fitchCost_add_le_insideCost`：`c_v + [s ∉ S_v] ≤ insideCost v τ + [st τ v ≠ s]`
    （对 `depth` 的良基归纳；**主定理「≤ 最少突变数」方向的全部内容**）；
  * `insideCost_root_eq_numChanges`：`insideCost root τ = numChanges σ τ`；
  * `fitchCost_eq_sum_minExtra` / `fitchCostGen_eq_sum_minExtra`：
    `c_v = ∑_{w ∈ desc v} minExtra (childSets w)`，特别地
    `fitchCostGen σ = ∑_v minExtra (childSets v)`；
  * `numChanges_eq_sum_children`：`numChanges σ τ = ∑_v ∑_{u ∈ children v} [st τ u ≠ st τ v]`。
  （两条「后代求和」桥都靠 `desc` 的分解 + 两两不交 + `Finset.sum_biUnion`。）

## ⚠️ 树层的一处更正（多分叉）：`F v s = c_v + [s ∉ S_v]` **不成立**

「条件代价」`F v s`（＝子树内最少突变数，且 `v` 的状态被钉成 `s`）必须**递推定义**：
`F v s = ∑_{u ∈ children v} min_t (F u t + [t ≠ s])`（叶：`F leaf s = [s ≠ label]`），
而 `c_v = min_s F v s`、`S_v = {s | F v s = c_v}` 只是它的最小值 / 最小集。能用的桥是**不等式**
`c_v + [s ∉ S_v] ≤ F v s` —— 它由结点层**已有**的两条直接得到
（`minExtra_le`：`minExtra ≤ extra t`；`lt_extra_of_notMem_best`：`s ∉ best ⇒ minExtra < extra s`），
**不需要新引理**。

**数值反例**（与 `star_aabb_minExtra` / `pairFoldCost_abab` 同一现象：多分叉 / Hartigan）：
`v` 有 4 个叶孩子、标签全为 `a`，取 `s = b ≠ a` 时，`childSets v` = 四份 `{a}`、
`extra sets t = 4·[t ≠ a]`、`minExtra = 0`、`best = {a}`；于是
**真·条件代价 `F v b = 4`，而 `c_v + [b ∉ S_v] = 0 + 1 = 1`** ⇒ 两者**不是等式，只有 `≤`**。
（结点层那条 `minExtra_add` 是**单个集合 / 单个孩子**的版本，本身仍然为真；
假的是把它**按孩子求和**之后的形态 ✗。）

## 🟡 尚未做（**不得含糊**）

* **树层主定理尚未证**：`fitchCostGen = 最少突变数`（`fitchCostGen_eq_minChanges`），
  以及与库内 4 元集版的桥 `fitchCostGen_quartet_eq_fitchCost`。
  **已有**：树数据 `GenTree`、子树机制（分解 / 不交 / `desc root = univ`）、
  `S_v` / `c_v` / `insideCost` 的定义与展开引理、`fitchCostGen` / `numChanges` / `minChanges`、
  结点层下界引擎 `minExtra_add_le`、下界（ii）`fitchCost_add_le_insideCost`、
  两条桥 `insideCost_root_eq_numChanges` / `fitchCostGen_eq_sum_minExtra`、
  `numChanges_eq_sum_children`。
  **缺**（最后一批）：上界（iii）—— 自顶向下构造 `assign : V → α`，使每个结点
  `st (assign σ) v ∈ S_v`，于是 `∑_v extra (childSets v) (st τ v) = ∑_v minExtra (childSets v)`，
  从而 `minChanges σ ≤ fitchCostGen σ`；再由 (ii) 得主定理 `fitchCostGen_eq_minChanges`。
  —— **未证者不标 ★**（纪律 12）；`references/README.md` 的 `Fitch1971_*` 在手 ✓。
* **Sankoff（任意代价矩阵）本批不做** —— **Sankoff 1975**
  （*Minimum mutation trees of sequences*, SIAM J. Appl. Math. 28:35–42）
  **不在** `references/md/`（见 `references/README.md:248`、`:282` 缺失清单）。
  本文件全部结论只用单位代价矩阵（替换代价 `= [状态不同]`），即 Fitch 的模型。
-/

universe u v

namespace Fitch

variable {α : Type v} [Fintype α] [DecidableEq α]

/-! ## 结点层：Fitch 的集合运算与代价增量 -/

/-- **Fitch (1971) 的结点集合运算**：交集非空取交集，否则取并集。 -/
def pair (S U : Finset α) : Finset α := if (S ∩ U).Nonempty then S ∩ U else S ∪ U

/-- 把两个集合摆成 `Fin 2` 下标（**每个孩子一个下标**，不去重）。 -/
def pairSets (S U : Finset α) : Fin 2 → Finset α := fun i => if i = 0 then S else U

/-- 状态 `s` **不在**其中多少个孩子集合里 —— 结点代价增量（Fitch 的并集计数）。

⚠️ 用**下标类型 `ι`**（每个孩子一个下标）而不是 `Finset (Finset α)`：后者会把相同的
孩子集合去重，从而在 polytomy 上低估代价（见 `star_aabb_minExtra`）。 -/
def extra {ι : Type*} [Fintype ι] (sets : ι → Finset α) (s : α) : ℕ :=
  ∑ i, if s ∈ sets i then 0 else 1

/-- 最小的代价增量（`α` 为空时约定为 `0`，此时无状态可取）。 -/
def minExtra {ι : Type*} [Fintype ι] (sets : ι → Finset α) : ℕ :=
  if h : (Finset.univ : Finset α).Nonempty then
    ((Finset.univ : Finset α).image (extra sets)).min' (h.image _) else 0

/-- **Fitch 候选集**：达到最小代价增量的状态集。 -/
def best {ι : Type*} [Fintype ι] (sets : ι → Finset α) : Finset α :=
  (Finset.univ : Finset α).filter (fun s => extra sets s = minExtra sets)

variable {ι : Type*} [Fintype ι]

theorem mem_best {sets : ι → Finset α} {s : α} :
    s ∈ best sets ↔ extra sets s = minExtra sets := by
  simp only [best, Finset.mem_filter, Finset.mem_univ, true_and]

theorem minExtra_le (sets : ι → Finset α) (s : α) : minExtra sets ≤ extra sets s := by
  have h : (Finset.univ : Finset α).Nonempty := ⟨s, Finset.mem_univ s⟩
  rw [minExtra, dite_eq_left h]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)

theorem exists_extra_eq_minExtra (sets : ι → Finset α) (s : α) :
    ∃ t : α, extra sets t = minExtra sets := by
  have h : (Finset.univ : Finset α).Nonempty := ⟨s, Finset.mem_univ s⟩
  rw [minExtra, dite_eq_left h]
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((Finset.univ : Finset α).image (extra sets)) (h.image (extra sets)))
  exact ⟨t, ht⟩

theorem best_nonempty (sets : ι → Finset α) (s : α) : (best sets).Nonempty := by
  obtain ⟨t, ht⟩ := exists_extra_eq_minExtra sets s
  exact ⟨t, mem_best.mpr ht⟩

theorem lt_extra_of_notMem_best {sets : ι → Finset α} {s : α} (h : s ∉ best sets) :
    minExtra sets < extra sets s := by
  simp only [mem_best] at h
  exact lt_of_le_of_ne (minExtra_le sets s) (Ne.symm h)

/-! ## 两个孩子的专门化（**Fitch 1971 的二叉规则**） -/

omit [Fintype α] in
/-- `Fin 2` 上的求和拆成两项（自足版，避免为一条引理引入整块 big-operators 依赖）。 -/
theorem sum_fin_two {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) : ∑ i, f i = f 0 + f 1 := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

omit [Fintype α] in
/-- **两个孩子时的代价增量**（任意状态数；**无需 `S ≠ U`** —— 下标记账让 `S = U` 也对）。 -/
theorem extra_pair (S U : Finset α) (s : α) :
    extra (pairSets S U) s = (if s ∈ S then 0 else 1) + (if s ∈ U then 0 else 1) := by
  rw [extra, sum_fin_two]
  simp [pairSets]

omit [Fintype α] in
/-- `extra = 0` ⟹ 两个集合都含 `s`。 -/
theorem extra_pair_eq_zero {S U : Finset α} {s : α}
    (h : extra (pairSets S U) s = 0) : s ∈ S ∧ s ∈ U := by
  rw [extra_pair] at h
  have h0 : (if s ∈ S then (0 : ℕ) else 1) = 0 := (Nat.add_eq_zero_iff.mp h).1
  have h1 : (if s ∈ U then (0 : ℕ) else 1) = 0 := (Nat.add_eq_zero_iff.mp h).2
  exact ⟨by by_contra hc; simp only [hc, ite_false] at h0; omega,
         by by_contra hc; simp only [hc, ite_false] at h1; omega⟩

/-- **两个孩子时的最小增量**（`S = U ≠ ∅` 时也对：最小值 `0`）。 -/
theorem minExtra_pair {S U : Finset α} (hS : S.Nonempty) :
    minExtra (pairSets S U) = if (S ∩ U).Nonempty then 0 else 1 := by
  rcases hS with ⟨a, ha⟩
  by_cases h : (S ∩ U).Nonempty
  · simp only [h, ite_true]
    obtain ⟨t, ht⟩ := h
    rw [Finset.mem_inter] at ht
    have h0 : extra (pairSets S U) t = 0 := by rw [extra_pair]; simp [ht.1, ht.2]
    have := minExtra_le (pairSets S U) t
    omega
  · simp only [h, ite_false]
    have haU : a ∉ U := fun hau => h ⟨a, Finset.mem_inter.mpr ⟨ha, hau⟩⟩
    have h1 : extra (pairSets S U) a = 1 := by rw [extra_pair]; simp [ha, haU]
    have hne : minExtra (pairSets S U) ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := exists_extra_eq_minExtra (pairSets S U) a
      rw [h0] at ht
      exact h ⟨t, Finset.mem_inter.mpr (extra_pair_eq_zero ht)⟩
    have := minExtra_le (pairSets S U) a
    rw [h1] at this
    omega

/-- ★★★ **Fitch 1971 的二叉规则**：恰有两个孩子（候选集 `S`、`U`，`S` 非空）时，
最优状态集就是「交集非空取交集、否则取并集」——**对任意有限状态类型 `α`**。 -/
theorem best_pair {S U : Finset α} (hS : S.Nonempty) :
    best (pairSets S U) = pair S U := by
  have hmin := minExtra_pair (S := S) (U := U) hS
  rw [pair]
  ext s
  rw [mem_best, hmin]
  by_cases h : (S ∩ U).Nonempty
  · simp only [h, ite_true, Finset.mem_inter]
    exact ⟨fun hs => extra_pair_eq_zero (by rw [hs]), fun hs => by
      rw [extra_pair]; simp [hs.1, hs.2]⟩
  · simp only [h, ite_false, Finset.mem_union]
    constructor
    · intro hs
      rw [extra_pair] at hs
      by_cases h1 : s ∈ S
      · exact Or.inl h1
      · refine Or.inr (by_contra fun h2 => ?_)
        simp only [h1, h2, ite_false] at hs
        omega
    · intro hs
      rcases hs with h1 | h2
      · have hq : s ∉ U := fun hq => h ⟨s, Finset.mem_inter.mpr ⟨h1, hq⟩⟩
        rw [extra_pair]; simp only [h1, hq, ite_true, ite_false]
      · have hq : s ∉ S := fun hq => h ⟨s, Finset.mem_inter.mpr ⟨hq, h2⟩⟩
        rw [extra_pair]; simp only [h2, hq, ite_true, ite_false]

/-! ## 递推的心脏恒等式 -/

/-- ★★ **Fitch 递推的心脏**：给定孩子的**最优状态集** `S`，
「让孩子态取 `t`（多付 `[t∉S]`）再付父边 `[t≠s]`」的最小值就是 `[s∉S]`（再叠加常数 `c`）。

即 `min_t (c + [t∉S] + [t≠s]) = c + [s∉S]`。它是「结点代价 + 父边代价」的**分离引理**，
树层递推（`fitchCostGen = 最少突变数`）全靠它。 -/
theorem minExtra_add (S : Finset α) (c : ℕ) (s : α) (h : (Finset.univ : Finset α).Nonempty) :
    ((Finset.univ : Finset α).image
        (fun t => c + (if t ∈ S then 0 else 1) + (if t = s then 0 else 1))).min' (h.image _)
      = c + (if s ∈ S then 0 else 1) := by
  refine le_antisymm ?_ (Finset.le_min' _ _ _ ?_)
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, by simp⟩)
  · intro n hn
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hn
    have hle : (if s ∈ S then (0 : ℕ) else 1)
        ≤ (if t ∈ S then (0 : ℕ) else 1) + (if t = s then (0 : ℕ) else 1) := by
      by_cases hts : t = s
      · subst hts; split_ifs <;> omega
      · simp only [hts, ite_false]; split_ifs <;> omega
    omega

/-! ## ★★ 边界反例：polytomy 上「逐对并集」规则**不是**最优 -/

omit [Fintype α] in
/-- **Fitch 的逐对并集计数**（按给定顺序把候选集两两合并，数「交集为空」的次数）。

这是 Fitch 1971 原文规则的机械化（只对**二叉**结点有最优性保证）。 -/
def pairFoldCostAux (acc : Finset α) : List (Finset α) → ℕ
  | [] => 0
  | S :: rest => (if (acc ∩ S).Nonempty then 0 else 1) + pairFoldCostAux (pair acc S) rest

omit [Fintype α] in
/-- `pairFoldCostAux` 的入口（第一个孩子当初始累加集）。 -/
def pairFoldCost (l : List (Finset α)) : ℕ :=
  match l with
  | [] => 0
  | S :: rest => pairFoldCostAux S rest

omit [Fintype α] in
/-- 4 个孩子、状态 `a,a,b,b`：逐对折叠（顺序 `a,a,b,b`）只数到 **1** 次并集。 -/
theorem pairFoldCost_aabb :
    pairFoldCost [({true} : Finset Bool), {true}, {false}, {false}] = 1 := by decide

omit [Fintype α] in
/-- 同样 4 个孩子、只换折叠顺序（`a,b,a,b`）：数到 **2** 次 ⇒ 逐对规则**顺序相关**。 -/
theorem pairFoldCost_abab :
    pairFoldCost [({true} : Finset Bool), {false}, {true}, {false}] = 2 := by decide

/-- ★★ **真最优增量是 2**（根取 `a` 或 `b`，总有恰好两个孩子状态不同）——
逐对规则在 polytomy 上**过小**（`1 < 2`）。 -/
theorem star_aabb_minExtra :
    minExtra (fun i : Fin 4 => if (i : ℕ) < 2 then ({true} : Finset Bool) else {false}) = 2 := by
  decide

/-! ## 树层：任意有根树（任意状态数）上的 Fitch 递推

下面把结点层（`best` / `minExtra` / `minExtra_add`）拼成**任意有根有限树**上的递推，
并证明它就是「最少突变数」。

### 树数据（为什么树层不用 `Phylo.Core.RootedTree`）

`RootedTree`（`Phylo/Core.lean:304`）只给 `SimpleGraph`；要从它导出「父映射 + 子树分解」
得先把无向图跑成有根树（唯一路径、连通分量……），这与本文件的目标正交。所以树层的输入取
**自足的组合数据** `GenTree`：

* `parent`：父映射；`root` 是唯一没有父的顶点（`parent_root`，配合 `reachable` 得
  `parent_eq_none_iff`）；
* `depth`：**高度**（从叶往上数，`parent v = some u → depth v < depth u`）——
  这是自底向上良基递归的燃料；
* `reachable`：每个顶点都能沿父指针走到 `root`（连通性）；
* `label`：叶的标签（叶态 = `σ (label v)`）。

`desc v`（子树）用**父指针迭代的闭包**定义（不是递归定义）；于是「子树分解」
`desc v = {v} ∪ ⋃_{u ∈ children v} desc u` 与「不同孩子的子树两两不交」都由同一条
引理 `depth_lt_of_parStep`（祖先链上高度严格上升）推出。 -/

noncomputable section

open Classical

/-- 沿父指针走一步（`Option` 上的全函数；`none` 是吸收元）。 -/
def parStep {V : Type*} (parent : V → Option V) : Option V → Option V :=
  fun o => o.bind parent

theorem parStep_none {V : Type*} (parent : V → Option V) (n : ℕ) :
    (parStep parent)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : parStep parent none = none := rfl
    rw [Function.iterate_succ_apply, h, ih]

theorem parStep_some {V : Type*} (parent : V → Option V) (x : V) :
    parStep parent (some x) = parent x := rfl

/-- 从上一步的迭代里**剥掉最后一跳**（`parStep` 是先作用在 `some w` 上的）。 -/
theorem iterate_parStep_succ {V : Type*} (parent : V → Option V) (n : ℕ) (w : V) :
    (parStep parent)^[n.succ] (some w) = (parStep parent)^[n] (parent w) := by
  rw [Function.iterate_succ_apply, parStep_some]

/-- **有根有限树的组合数据**（树层的输入）。

`depth` 是**高度**（从叶往上数）：孩子的 `depth` 严格小于父亲 —— 良基递归的燃料。
`reachable` 是连通性（每个顶点都能沿父指针走到 `root`）；`label` 给叶的标签。 -/
structure GenTree (X : Type u) where
  V : Type u
  fintypeV : Fintype V
  decEqV : DecidableEq V
  root : V
  parent : V → Option V
  depth : V → ℕ
  label : V → X
  parent_root : parent root = none
  depth_parent : ∀ ⦃a b : V⦄, parent a = some b → depth a < depth b
  reachable : ∀ w : V, ∃ k : ℕ, (parStep parent)^[k] (some w) = some root

attribute [instance] GenTree.fintypeV GenTree.decEqV

/-
树层的声明都放在类型自己的命名空间里，于是 `T.children` / `T.fitchSet σ` 等点记法可用。 -/
namespace GenTree

variable (T : GenTree X)

/-- `v` 的孩子（每个孩子一个下标，**不去重**）。 -/
def children (v : T.V) : Finset T.V :=
  (Finset.univ : Finset T.V).filter (fun u => T.parent u = some v)

theorem mem_children {u v : T.V} : u ∈ T.children v ↔ T.parent u = some v := by
  simp [children]

/-- 叶：没有孩子。 -/
def IsLeaf (v : T.V) : Prop := T.children v = ∅

theorem isLeaf_iff {v : T.V} : T.IsLeaf v ↔ T.children v = ∅ := Iff.rfl

/-- 孩子的 `depth` 严格小于父亲（递归的燃料，直接由 `depth_parent` 得到）。 -/
theorem children_depth_lt {u v : T.V} (h : u ∈ T.children v) : T.depth u < T.depth v :=
  T.depth_parent (T.mem_children.mp h)

/-- `v` 是 `w` 的祖先（含 `w = v`）：沿父指针从 `w` 走 `k` 步到 `v`。 -/
def IsAnc (v w : T.V) : Prop := ∃ k : ℕ, (parStep T.parent)^[k] (some w) = some v

theorem isAnc_self (v : T.V) : T.IsAnc v v := ⟨0, rfl⟩

theorem isAnc_step {u v : T.V} (h : T.parent u = some v) : T.IsAnc v u := by
  refine ⟨1, ?_⟩
  rw [Function.iterate_one, parStep_some]
  exact h

theorem isAnc_trans {a b c : T.V} (hab : T.IsAnc a b) (hbc : T.IsAnc b c) : T.IsAnc a c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  refine ⟨k + l, ?_⟩
  rw [Function.iterate_add_apply, hl, hk]

theorem isAnc_of_mem_children {u v : T.V} (h : u ∈ T.children v) : T.IsAnc v u :=
  T.isAnc_step (T.mem_children.mp h)

/-- `v` 的子树（含 `v` 自己）。 -/
def desc (v : T.V) : Finset T.V := (Finset.univ : Finset T.V).filter (T.IsAnc v)

theorem mem_desc {w v : T.V} : w ∈ T.desc v ↔ T.IsAnc v w := by
  simp [desc]

theorem desc_self (v : T.V) : v ∈ T.desc v := T.mem_desc.mpr (T.isAnc_self v)

/-- `v` 的真后代（不含 `v`）。 -/
def strictDesc (v : T.V) : Finset T.V := (T.desc v).erase v

theorem mem_strictDesc {w v : T.V} : w ∈ T.strictDesc v ↔ w ≠ v ∧ w ∈ T.desc v := by
  simp [strictDesc]

theorem insert_strictDesc (v : T.V) : insert v (T.strictDesc v) = T.desc v :=
  Finset.insert_erase (T.desc_self v)

/-- **祖先链上高度严格上升**（每次剥掉最后一跳；`k.succ` 保证至少走一步）。 -/
theorem depth_lt_of_parStep_aux (k : ℕ) :
    ∀ {w v : T.V}, (parStep T.parent)^[k.succ] (some w) = some v → T.depth w < T.depth v := by
  induction k with
  | zero =>
    intro w v h
    rw [Function.iterate_one, parStep_some] at h
    exact T.depth_parent h
  | succ k ih =>
    intro w v h
    rw [iterate_parStep_succ] at h
    cases hp : T.parent w with
    | none => rw [hp, parStep_none] at h; exact absurd h (by simp)
    | some y =>
      rw [hp] at h
      exact lt_trans (T.depth_parent hp) (ih h)

theorem depth_lt_of_parStep {k : ℕ} (hk : 0 < k) {w v : T.V}
    (h : (parStep T.parent)^[k] (some w) = some v) : T.depth w < T.depth v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
  exact T.depth_lt_of_parStep_aux m h

theorem depth_lt_of_mem_strictDesc {w v : T.V} (h : w ∈ T.strictDesc v) : T.depth w < T.depth v := by
  obtain ⟨hne, hmem⟩ := T.mem_strictDesc.mp h
  obtain ⟨k, hk⟩ := T.mem_desc.mp hmem
  rcases Nat.eq_zero_or_pos k with hk0 | hpos
  · rw [hk0, Function.iterate_zero_apply] at hk
    exact absurd (Option.some.inj hk) hne
  · exact T.depth_lt_of_parStep hpos hk

/-- **子树分解**：`desc v = {v} ∪ ⋃_{u ∈ children v} desc u`。 -/
theorem desc_eq_insert_biUnion (v : T.V) :
    T.desc v = insert v ((T.children v).biUnion T.desc) := by
  ext w
  rw [Finset.mem_insert, Finset.mem_biUnion, T.mem_desc]
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hpos
    · left
      rw [hk0, Function.iterate_zero_apply] at hk
      exact Option.some.inj hk
    · right
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
      rw [Function.iterate_succ_apply'] at hk
      cases hy : (parStep T.parent)^[m] (some w) with
      | none =>
        rw [hy] at hk
        exact absurd hk (by simp [parStep])
      | some y =>
        rw [hy, parStep_some] at hk
        exact ⟨y, T.mem_children.mpr hk, T.mem_desc.mpr ⟨m, hy⟩⟩
  · rintro (hwv | ⟨u, hu, hwu⟩)
    · rw [hwv]
      exact T.isAnc_self v
    · exact T.isAnc_trans (T.isAnc_step (T.mem_children.mp hu)) (T.mem_desc.mp hwu)

/-- 孩子不是它父亲的祖先。 -/
theorem not_isAnc_of_mem_children {u v : T.V} (hu : u ∈ T.children v) : ¬ T.IsAnc u v := by
  rintro ⟨k, hk⟩
  have hdu : T.depth u < T.depth v := T.depth_parent (T.mem_children.mp hu)
  rcases Nat.eq_zero_or_pos k with hk0 | hpos
  · rw [hk0, Function.iterate_zero_apply] at hk
    have huv : u = v := (Option.some.inj hk).symm
    have hpv : T.parent v = some v := by
      have hpu : T.parent u = some u := by rw [T.mem_children.mp hu, huv]
      rw [huv] at hpu
      exact hpu
    exact absurd (T.depth_parent hpv) (lt_irrefl _)
  · exact absurd (T.depth_lt_of_parStep hpos hk) (not_lt.mpr hdu.le)

/-- 从同一个 `w` 出发的两条祖先链可以比较：短的那条是长的前缀。 -/
theorem anc_le_anc {w a b : T.V} {k l : ℕ}
    (hk : (parStep T.parent)^[k] (some w) = some a)
    (hl : (parStep T.parent)^[l] (some w) = some b) (hkl : k ≤ l) : T.IsAnc b a := by
  refine ⟨l - k, ?_⟩
  have h : (parStep T.parent)^[l] (some w)
      = (parStep T.parent)^[l - k] ((parStep T.parent)^[k] (some w)) := by
    conv_lhs => rw [← Nat.sub_add_cancel hkl]
    rw [Function.iterate_add_apply]
  rw [hk] at h
  exact h.symm.trans hl

/-- 同一个父亲的**两个孩子**，若一个是另一个的祖先，则两者相等。 -/
theorem eq_of_children_of_isAnc {u u' v : T.V} (hu : u ∈ T.children v)
    (hu' : u' ∈ T.children v) (h : T.IsAnc u' u) : u' = u := by
  obtain ⟨n, hn⟩ := h
  have hdu : T.depth u' < T.depth v := T.depth_parent (T.mem_children.mp hu')
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · rw [hn0, Function.iterate_zero_apply] at hn
    exact (Option.some.inj hn).symm
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
    cases m with
    | zero =>
      rw [Function.iterate_one, parStep_some] at hn
      have huv : u' = v := Option.some.inj (by rw [← hn]; exact T.mem_children.mp hu)
      have hpv : T.parent v = some v := by
        have : T.parent u' = some u' := by rw [T.mem_children.mp hu', huv]
        rw [huv] at this
        exact this
      exact absurd (T.depth_parent hpv) (lt_irrefl _)
    | succ m =>
      have h2 : (parStep T.parent)^[m.succ] (some v) = some u' := by
        rw [iterate_parStep_succ] at hn
        rwa [T.mem_children.mp hu] at hn
      exact absurd (T.depth_lt_of_parStep_aux m h2) (not_lt.mpr hdu.le)

/-- **不同孩子的子树两两不交**（`Finset.sum_biUnion` 需要的形状）。 -/
theorem desc_pairwise_disjoint (v : T.V) :
    ∀ u ∈ T.children v, ∀ u' ∈ T.children v, (T.desc u ∩ T.desc u').Nonempty → u = u' := by
  intro u hu u' hu' hne
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hwu, hwu'⟩ := Finset.mem_inter.mp hw
  obtain ⟨k, hk⟩ := T.mem_desc.mp hwu
  obtain ⟨l, hl⟩ := T.mem_desc.mp hwu'
  rcases le_total k l with hkl | hlk
  · exact (T.eq_of_children_of_isAnc hu hu'
      (T.anc_le_anc (hk := hk) (hl := hl) (hkl := hkl))).symm
  · exact T.eq_of_children_of_isAnc hu' hu (T.anc_le_anc (hk := hl) (hl := hk) (hkl := hlk))

theorem pairwiseDisjoint_desc (v : T.V) :
    (↑(T.children v) : Set T.V).PairwiseDisjoint T.desc :=
  Finset.pairwiseDisjoint_iff.mpr (T.desc_pairwise_disjoint v)

/-- **真后代正是孩子们子树的并**。 -/
theorem strictDesc_eq_biUnion (v : T.V) :
    T.strictDesc v = (T.children v).biUnion T.desc := by
  have hv : v ∉ (T.children v).biUnion T.desc := by
    rw [Finset.mem_biUnion]
    rintro ⟨u, hu, hvu⟩
    exact T.not_isAnc_of_mem_children hu (T.mem_desc.mp hvu)
  rw [strictDesc, T.desc_eq_insert_biUnion v, Finset.erase_insert hv]

/-- **`desc root = univ`**（`reachable` 的直接翻译：每个顶点都在根子树里）。 -/
theorem desc_root : T.desc T.root = Finset.univ := by
  ext w
  exact ⟨fun _ => Finset.mem_univ w, fun _ => T.mem_desc.mpr (T.reachable w)⟩

theorem strictDesc_root : T.strictDesc T.root = Finset.univ.erase T.root := by
  rw [strictDesc, T.desc_root]

/-- **非 `root` 顶点必有父**（由 `reachable` 推出，不需要额外假设）。 -/
theorem parent_eq_none_iff (w : T.V) : T.parent w = none ↔ w = T.root := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := T.reachable w
    rcases Nat.eq_zero_or_pos k with hk0 | hpos
    · rw [hk0, Function.iterate_zero_apply] at hk
      exact Option.some.inj hk
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
      have hk' : (parStep T.parent)^[m] (T.parent w) = some T.root := by
        rw [← iterate_parStep_succ]
        exact hk
      rw [h, parStep_none] at hk'
      exact absurd hk' (by simp)
  · intro h
    rw [h]
    exact T.parent_root

/-! ### 自底向上的 Fitch 递推（`S_v` / `c_v` / `insideCost`） -/

/-- 良基关系：孩子的 `depth` 严格小于父亲，故可自底向上递归。 -/
theorem wf_depth (T : GenTree X) : WellFounded (fun a b : T.V => T.depth a < T.depth b) :=
  InvImage.wf T.depth (measure (id : ℕ → ℕ)).wf

/-- **Fitch 候选集 `S_v`**（`WellFounded.fix`，燃料 = `depth`）：
叶取 `{σ (label v)}`，内部取 `best`（＝最小代价增量的状态集）。 -/
def fitchSet (σ : X → α) (v : T.V) : Finset α :=
  WellFounded.fix T.wf_depth (C := fun _ => Finset α) (fun v rec =>
    if T.children v = ∅ then {σ (T.label v)}
    else best (fun u : {u // u ∈ T.children v} => rec u.1 (T.children_depth_lt u.2))) v

/-- `v` 的**孩子候选集族**（每个孩子一个下标）：结点层 `best` / `minExtra` 的输入。 -/
def childSets (σ : X → α) (v : T.V) : {u // u ∈ T.children v} → Finset α :=
  fun u => T.fitchSet σ u.1

/-- **Fitch 代价 `c_v`**（`WellFounded.fix`）：
叶为 `0`，内部 = 孩子代价之和 + `minExtra`。 -/
def fitchCost (σ : X → α) (v : T.V) : ℕ :=
  WellFounded.fix T.wf_depth (C := fun _ => ℕ) (fun v rec =>
    if T.children v = ∅ then 0
    else (∑ u : {u // u ∈ T.children v}, rec u.1 (T.children_depth_lt u.2))
      + minExtra (T.childSets σ v)) v

/-- 顶点 `v` 的状态：叶被标签钉死，内部顶点取赋值 `τ`。 -/
def st (σ : X → α) (τ : T.V → α) (v : T.V) : α :=
  if T.children v = ∅ then σ (T.label v) else τ v

/-- **子树内部突变数**（不含 `v` 到父的那条边）。 -/
def insideCost (σ : X → α) (τ : T.V → α) (v : T.V) : ℕ :=
  WellFounded.fix T.wf_depth (C := fun _ => ℕ) (fun v rec =>
    if T.children v = ∅ then 0
    else ∑ u : {u // u ∈ T.children v},
      (rec u.1 (T.children_depth_lt u.2) + (if T.st σ τ u.1 ≠ T.st σ τ v then 1 else 0))) v

theorem fitchSet_eq_leaf {σ : X → α} {v : T.V} (h : T.children v = ∅) :
    T.fitchSet σ v = {σ (T.label v)} := by
  rw [fitchSet, WellFounded.fix_eq, ite_eq_left h]

theorem fitchSet_eq_internal {σ : X → α} {v : T.V} (h : T.children v ≠ ∅) :
    T.fitchSet σ v = best (T.childSets σ v) := by
  rw [fitchSet, WellFounded.fix_eq, ite_eq_right h]
  exact congrArg best (funext fun u => rfl)

theorem fitchCost_eq_leaf {σ : X → α} {v : T.V} (h : T.children v = ∅) :
    T.fitchCost σ v = 0 := by
  rw [fitchCost, WellFounded.fix_eq, ite_eq_left h]

theorem fitchCost_eq_internal' {σ : X → α} {v : T.V} (h : T.children v ≠ ∅) :
    T.fitchCost σ v
      = (∑ u : {u // u ∈ T.children v}, T.fitchCost σ u.1) + minExtra (T.childSets σ v) := by
  rw [fitchCost, WellFounded.fix_eq, ite_eq_right h]
  exact congrArg (· + minExtra (T.childSets σ v)) (Finset.sum_congr rfl fun u _ => rfl)

omit [Fintype α] in
theorem insideCost_eq_leaf {σ : X → α} {τ : T.V → α} {v : T.V} (h : T.children v = ∅) :
    T.insideCost σ τ v = 0 := by
  rw [insideCost, WellFounded.fix_eq, ite_eq_left h]

omit [Fintype α] in
theorem insideCost_eq_internal' {σ : X → α} {τ : T.V → α} {v : T.V} (h : T.children v ≠ ∅) :
    T.insideCost σ τ v
      = ∑ u : {u // u ∈ T.children v},
          (T.insideCost σ τ u.1 + (if T.st σ τ u.1 ≠ T.st σ τ v then 1 else 0)) := by
  rw [insideCost, WellFounded.fix_eq, ite_eq_right h]
  exact Finset.sum_congr rfl fun u _ => rfl

/-- **Fitch 代价（整棵树）**：根的代价。 -/
def fitchCostGen (σ : X → α) : ℕ := T.fitchCost σ T.root

/-! ### 「最少突变数」侧 -/

/-- `v` 到它父亲那条边上的突变数（`root` 无边，记 `0`）。 -/
def edgeCost (σ : X → α) (τ : T.V → α) (u : T.V) : ℕ :=
  match T.parent u with
  | none => 0
  | some p => if T.st σ τ u ≠ T.st σ τ p then 1 else 0

omit [Fintype α] in
theorem edgeCost_none {σ : X → α} {τ : T.V → α} {u : T.V} (h : T.parent u = none) :
    T.edgeCost σ τ u = 0 := by
  rw [edgeCost, h]

omit [Fintype α] in
theorem edgeCost_some {σ : X → α} {τ : T.V → α} {u p : T.V} (h : T.parent u = some p) :
    T.edgeCost σ τ u = if T.st σ τ u ≠ T.st σ τ p then 1 else 0 := by
  rw [edgeCost, h]

/-- **突变数**：`st τ` 在非根边上取值不同的边数。 -/
def numChanges (σ : X → α) (τ : T.V → α) : ℕ :=
  ((Finset.univ : Finset T.V).filter (fun u => u ≠ T.root ∧ T.edgeCost σ τ u = 1)).card

/-- **最少突变数**：对全体赋值 `τ` 取最小。 -/
def minChanges (σ : X → α) : ℕ :=
  ((Finset.univ : Finset (T.V → α)).image (T.numChanges σ)).min'
    (Finset.image_nonempty.mpr ⟨fun _ => σ (T.label T.root), Finset.mem_univ _⟩)

/-! ### 结点层的下界引擎（**不等式**形态；等式形态在多分叉上为假） -/

/-- ★★ **Fitch 递推的下界引擎**：`minExtra sets + [s ∉ best sets] ≤ extra sets t + [t ≠ s]`。

⚠️ **这里只能是不等式**。等式 `extra sets s = minExtra sets + [s ∉ best sets]` 在多分叉上**为假**：
`v` 有 4 个叶孩子、标签全为 `a` 时 `childSets v` = 四份 `{a}`，`s = b ≠ a` 给出
`extra (childSets v) b = 4`、`minExtra = 0`、`best = {a}`，故 `extra b = 4 ≠ 1 = minExtra + [b ∉ best]`。
（这正是 `star_aabb_minExtra` / `pairFoldCost_abab` 的同一现象。） -/
theorem minExtra_add_le {ι : Type*} [Fintype ι] (sets : ι → Finset α) (s t : α) :
    minExtra sets + (if s ∈ best sets then 0 else 1)
      ≤ extra sets t + (if t ≠ s then 1 else 0) := by
  by_cases hs : s ∈ best sets
  · rw [ite_eq_left hs]
    by_cases hts : t = s
    · rw [ite_eq_right (by simp [hts]), hts]
      have := mem_best.mp hs
      omega
    · rw [ite_eq_left hts]
      have := minExtra_le sets t
      omega
  · rw [ite_eq_right hs]
    by_cases hts : t = s
    · rw [ite_eq_right (by simp [hts]), hts]
      have := lt_extra_of_notMem_best hs
      omega
    · rw [ite_eq_left hts]
      have := minExtra_le sets t
      omega

/-! ### 求和桥（孩子下标 ↔ `children` ↔ 真后代） -/

/-- 孩子下标上的求和 ↔ `children` 上的 `Finset` 求和。 -/
theorem sum_children {M : Type*} [AddCommMonoid M] (v : T.V) (f : T.V → M) :
    (∑ u : {u // u ∈ T.children v}, f u.1) = ∑ u ∈ T.children v, f u := by
  rw [Finset.univ_eq_attach, Finset.sum_attach]

theorem extra_childSets (σ : X → α) (v : T.V) (s : α) :
    extra (T.childSets σ v) s
      = ∑ u : {u // u ∈ T.children v}, (if s ∈ T.fitchSet σ u.1 then 0 else 1) := by
  rw [extra]
  rfl

theorem extra_childSets_finset (σ : X → α) (v : T.V) (s : α) :
    extra (T.childSets σ v) s = ∑ u ∈ T.children v, (if s ∈ T.fitchSet σ u then 0 else 1) := by
  rw [T.extra_childSets]
  exact T.sum_children v (fun u => if s ∈ T.fitchSet σ u then 0 else 1)

theorem minExtra_childSets_eq_zero_of_leaf {σ : X → α} {v : T.V} (h : T.children v = ∅) :
    minExtra (T.childSets σ v) = 0 := by
  have h0 : extra (T.childSets σ v) (σ (T.label v)) = 0 := by
    rw [T.extra_childSets_finset, h, Finset.sum_empty]
  have hle := minExtra_le (T.childSets σ v) (σ (T.label v))
  rw [h0] at hle
  omega

/-- `desc` 上的求和 = `v` 自己 + 真后代。 -/
theorem sum_desc_eq (f : T.V → ℕ) (v : T.V) :
    ∑ w ∈ T.desc v, f w = f v + ∑ w ∈ T.strictDesc v, f w := by
  have h : v ∉ T.strictDesc v := Finset.notMem_erase v (T.desc v)
  rw [← T.insert_strictDesc v, Finset.sum_insert h]

/-- 真后代上的求和 = 孩子们子树上求和（用子树两两不交）。 -/
theorem sum_strictDesc_eq (f : T.V → ℕ) (v : T.V) :
    ∑ w ∈ T.strictDesc v, f w = ∑ u ∈ T.children v, ∑ w ∈ T.desc u, f w := by
  rw [T.strictDesc_eq_biUnion, Finset.sum_biUnion (T.pairwiseDisjoint_desc v)]

/-- 孩子们子树上求和 = 每个孩子本身 + 该孩子的真后代。 -/
theorem sum_children_desc (f : T.V → ℕ) (v : T.V) :
    ∑ u ∈ T.children v, ∑ w ∈ T.desc u, f w
      = (∑ u ∈ T.children v, f u) + ∑ u ∈ T.children v, ∑ w ∈ T.strictDesc u, f w := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => T.sum_desc_eq f u

/-- **每个非根顶点恰有一个父亲**：按 `children` 的双重求和可以「转置」。 -/
theorem sum_children_swap {M : Type*} [AddCommMonoid M] (g : T.V → M) :
    (∑ v ∈ (Finset.univ : Finset T.V), ∑ u ∈ T.children v, g u)
      = ∑ u ∈ (Finset.univ : Finset T.V), (if u = T.root then 0 else g u) := by
  have h1 : ∀ v : T.V, ∑ u ∈ T.children v, g u
      = ∑ u ∈ (Finset.univ : Finset T.V), (if T.parent u = some v then g u else 0) := by
    intro v
    rw [children, Finset.sum_filter]
  calc (∑ v ∈ (Finset.univ : Finset T.V), ∑ u ∈ T.children v, g u)
      = ∑ v ∈ (Finset.univ : Finset T.V),
          ∑ u ∈ (Finset.univ : Finset T.V), (if T.parent u = some v then g u else 0) :=
        Finset.sum_congr rfl fun v _ => h1 v
    _ = ∑ u ∈ (Finset.univ : Finset T.V),
          ∑ v ∈ (Finset.univ : Finset T.V), (if T.parent u = some v then g u else 0) :=
        Finset.sum_comm
    _ = ∑ u ∈ (Finset.univ : Finset T.V), (if T.parent u = none then 0 else g u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        cases hp : T.parent u with
        | none =>
          simp
        | some a =>
          simp only [Option.some.injEq]
          rw [Finset.sum_ite_eq]
          simp
    _ = ∑ u ∈ (Finset.univ : Finset T.V), (if u = T.root then 0 else g u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : T.parent u = none
        · rw [ite_eq_left hu, ite_eq_left ((T.parent_eq_none_iff u).mp hu)]
        · rw [ite_eq_right hu, ite_eq_right fun hc => hu ((T.parent_eq_none_iff u).mpr hc)]

omit [Fintype α] in
/-- 边代价的求和可以按父亲分组。 -/
theorem sum_edgeCost_eq_sum_children (σ : X → α) (τ : T.V → α) :
    (∑ u ∈ (Finset.univ : Finset T.V), T.edgeCost σ τ u)
      = ∑ v ∈ (Finset.univ : Finset T.V), ∑ u ∈ T.children v, T.edgeCost σ τ u := by
  rw [T.sum_children_swap (fun u => T.edgeCost σ τ u)]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u = T.root
  · subst hu
    rw [ite_eq_left rfl, T.edgeCost_none T.parent_root]
  · rw [ite_eq_right hu]

omit [Fintype α] in
theorem edgeCost_le_one (σ : X → α) (τ : T.V → α) (u : T.V) : T.edgeCost σ τ u ≤ 1 := by
  unfold edgeCost
  split
  · omega
  · split_ifs <;> omega

omit [Fintype α] in
/-- `numChanges` 就是「所有边的代价之和」。 -/
theorem numChanges_eq_sum_edgeCost (σ : X → α) (τ : T.V → α) :
    T.numChanges σ τ = ∑ u ∈ (Finset.univ : Finset T.V), T.edgeCost σ τ u := by
  rw [numChanges, Finset.card_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u = T.root
  · subst hu
    rw [ite_eq_right (by simp), T.edgeCost_none T.parent_root]
  · by_cases he : T.edgeCost σ τ u = 1
    · rw [ite_eq_left (by simp [hu, he]), he]
    · rw [ite_eq_right (by simp [hu, he])]
      have hle := T.edgeCost_le_one σ τ u
      omega

omit [Fintype α] in
/-- `numChanges` 的「按结点分组」形态：每个结点的贡献 = 与孩子状态不同的孩子数。 -/
theorem numChanges_eq_sum_children (σ : X → α) (τ : T.V → α) :
    T.numChanges σ τ = ∑ v ∈ (Finset.univ : Finset T.V), ∑ u ∈ T.children v,
      (if T.st σ τ u ≠ T.st σ τ v then 1 else 0) := by
  rw [T.numChanges_eq_sum_edgeCost, T.sum_edgeCost_eq_sum_children]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u hu =>
    T.edgeCost_some (T.mem_children.mp hu)

/-! ### 下界（ii）：Fitch 代价不超过任意赋值的突变数 -/

theorem fitchCost_add_le_insideCost (σ : X → α) (τ : T.V → α) (v : T.V) (s : α) :
    T.fitchCost σ v + (if s ∈ T.fitchSet σ v then 0 else 1)
      ≤ T.insideCost σ τ v + (if T.st σ τ v ≠ s then 1 else 0) := by
  revert s
  refine WellFounded.induction T.wf_depth (C := fun v => ∀ s : α,
      T.fitchCost σ v + (if s ∈ T.fitchSet σ v then 0 else 1)
        ≤ T.insideCost σ τ v + (if T.st σ τ v ≠ s then 1 else 0)) v ?_
  intro v ih s
  by_cases hleaf : T.children v = ∅
  · rw [T.fitchCost_eq_leaf hleaf, T.fitchSet_eq_leaf hleaf, T.insideCost_eq_leaf hleaf]
    have hst : T.st σ τ v = σ (T.label v) := by rw [st, ite_eq_left hleaf]
    rw [hst, zero_add, zero_add]
    by_cases h : s = σ (T.label v)
    · rw [ite_eq_left (Finset.mem_singleton.mpr h), ite_eq_right (by rw [h]; simp)]
    · rw [ite_eq_right fun hc => h (Finset.mem_singleton.mp hc), ite_eq_left (Ne.symm h)]
  · have hne : T.children v ≠ ∅ := hleaf
    have hsum : (∑ u : {u // u ∈ T.children v}, T.fitchCost σ u.1)
        + extra (T.childSets σ v) (T.st σ τ v)
        = ∑ u : {u // u ∈ T.children v},
            (T.fitchCost σ u.1 + (if T.st σ τ v ∈ T.fitchSet σ u.1 then 0 else 1)) := by
      rw [T.extra_childSets, ← Finset.sum_add_distrib]
    have h1 : (∑ u : {u // u ∈ T.children v}, T.fitchCost σ u.1)
        + extra (T.childSets σ v) (T.st σ τ v) ≤ T.insideCost σ τ v := by
      rw [T.insideCost_eq_internal' hne, hsum]
      exact Finset.sum_le_sum fun u _ => ih u.1 (T.children_depth_lt u.2) (T.st σ τ v)
    have h2 := minExtra_add_le (T.childSets σ v) s (T.st σ τ v)
    rw [T.fitchCost_eq_internal' hne, T.fitchSet_eq_internal hne]
    omega

/-! ### 桥：`insideCost` / `fitchCost` 的「后代求和」形态 -/

omit [Fintype α] in
theorem insideCost_eq_sum_edgeCost (σ : X → α) (τ : T.V → α) (v : T.V) :
    T.insideCost σ τ v = ∑ w ∈ T.strictDesc v, T.edgeCost σ τ w := by
  refine WellFounded.induction T.wf_depth (C := fun v =>
    T.insideCost σ τ v = ∑ w ∈ T.strictDesc v, T.edgeCost σ τ w) v ?_
  intro v ih
  by_cases hleaf : T.children v = ∅
  · rw [T.insideCost_eq_leaf hleaf, T.strictDesc_eq_biUnion, hleaf, Finset.biUnion_empty,
      Finset.sum_empty]
  · have hne : T.children v ≠ ∅ := hleaf
    have hsub : (∑ u ∈ T.children v, T.insideCost σ τ u)
        = ∑ u ∈ T.children v, ∑ w ∈ T.strictDesc u, T.edgeCost σ τ w :=
      Finset.sum_congr rfl fun u hu => ih u (T.children_depth_lt hu)
    rw [T.insideCost_eq_internal' hne, T.strictDesc_eq_biUnion,
      Finset.sum_biUnion (T.pairwiseDisjoint_desc v)]
    rw [T.sum_children v (fun u => T.insideCost σ τ u
      + (if T.st σ τ u ≠ T.st σ τ v then 1 else 0))]
    rw [Finset.sum_add_distrib, hsub]
    rw [T.sum_children_desc (T.edgeCost σ τ) v]
    rw [Finset.sum_congr rfl (fun u hu => (T.edgeCost_some (T.mem_children.mp hu)).symm)]
    exact Nat.add_comm _ _

omit [Fintype α] in
/-- **桥 1**：`insideCost root` 就是突变数。 -/
theorem insideCost_root_eq_numChanges (σ : X → α) (τ : T.V → α) :
    T.insideCost σ τ T.root = T.numChanges σ τ := by
  have hA : ∀ u : T.V, T.edgeCost σ τ u = (if u = T.root then 0 else T.edgeCost σ τ u) := by
    intro u
    by_cases hu : u = T.root
    · subst hu
      rw [ite_eq_left rfl, T.edgeCost_none T.parent_root]
    · rw [ite_eq_right hu]
  have hB : ∀ u : T.V, (if u = T.root then 0 else T.edgeCost σ τ u)
      = (if u ≠ T.root ∧ T.edgeCost σ τ u = 1 then (1 : ℕ) else 0) := by
    intro u
    by_cases hu : u = T.root
    · subst hu
      rw [ite_eq_left rfl, ite_eq_right (by simp)]
    · by_cases he : T.edgeCost σ τ u = 1
      · rw [ite_eq_right hu, ite_eq_left (by simp [hu, he]), he]
      · rw [ite_eq_right hu, ite_eq_right (by simp [hu, he])]
        have hle := T.edgeCost_le_one σ τ u
        omega
  calc T.insideCost σ τ T.root
      = ∑ w ∈ T.strictDesc T.root, T.edgeCost σ τ w := T.insideCost_eq_sum_edgeCost σ τ T.root
    _ = ∑ w ∈ (Finset.univ : Finset T.V).erase T.root, T.edgeCost σ τ w := by
        rw [T.strictDesc_root]
    _ = ∑ u ∈ (Finset.univ : Finset T.V), T.edgeCost σ τ u :=
        Finset.sum_erase (Finset.univ : Finset T.V) (T.edgeCost_none T.parent_root)
    _ = ∑ u ∈ (Finset.univ : Finset T.V),
          (if u = T.root then 0 else T.edgeCost σ τ u) :=
        Finset.sum_congr rfl fun u _ => hA u
    _ = ∑ u ∈ (Finset.univ : Finset T.V),
          (if u ≠ T.root ∧ T.edgeCost σ τ u = 1 then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun u _ => hB u
    _ = T.numChanges σ τ := by rw [numChanges, Finset.card_filter]

/-- **桥 2**：`c_v` 就是 `v` 子树上所有 `minExtra` 之和。 -/
theorem fitchCost_eq_sum_minExtra (σ : X → α) (v : T.V) :
    T.fitchCost σ v = ∑ w ∈ T.desc v, minExtra (T.childSets σ w) := by
  refine WellFounded.induction T.wf_depth (C := fun v =>
    T.fitchCost σ v = ∑ w ∈ T.desc v, minExtra (T.childSets σ w)) v ?_
  intro v ih
  by_cases hleaf : T.children v = ∅
  · rw [T.fitchCost_eq_leaf hleaf, T.desc_eq_insert_biUnion, hleaf, Finset.biUnion_empty,
      Finset.sum_insert (Finset.notMem_empty v), Finset.sum_empty,
      T.minExtra_childSets_eq_zero_of_leaf (σ := σ) hleaf]
    omega
  · have hne : T.children v ≠ ∅ := hleaf
    have hsub : (∑ u ∈ T.children v, T.fitchCost σ u)
        = ∑ u ∈ T.children v, ∑ w ∈ T.desc u, minExtra (T.childSets σ w) :=
      Finset.sum_congr rfl fun u hu => ih u (T.children_depth_lt hu)
    rw [T.fitchCost_eq_internal' hne, T.sum_children v (fun u => T.fitchCost σ u), hsub,
      T.sum_desc_eq (fun w => minExtra (T.childSets σ w)) v,
      T.sum_strictDesc_eq (fun w => minExtra (T.childSets σ w)) v]
    exact Nat.add_comm _ _

/-- **桥 2（根）**：`fitchCostGen σ = ∑_v minExtra (childSets v)`。 -/
theorem fitchCostGen_eq_sum_minExtra (σ : X → α) :
    T.fitchCostGen σ = ∑ w ∈ (Finset.univ : Finset T.V), minExtra (T.childSets σ w) := by
  rw [fitchCostGen, T.fitchCost_eq_sum_minExtra, T.desc_root]

end GenTree

end

end Fitch
