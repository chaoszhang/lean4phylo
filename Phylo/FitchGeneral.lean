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

## 🟡 尚未做（**不得含糊**）

* **树层**：把上面的结点层拼成「任意有根树 + 任意状态数」上的递推
  `fitchCostGen`，并证明它 **= 最少突变数**（对全体内部态赋值取最小），
  以及与库内 4 元集版的桥 `fitchCostGen_quartet_eq_fitchCost`。
  —— 本文件目前**没有**这两个声明（**未证者不标 ★**，纪律 12）；
  `references/README.md` 的 `Fitch1971_*` 在手 ✓。
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

end Fitch
