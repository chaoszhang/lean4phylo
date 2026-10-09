/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license regarding copyright in this file.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERTheorem1

/-!
# `Phylo.Stat.CASTERTheorem2` —— CASTER **定理 2（贪心放置算法一致）** 与树级收口

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
定理 2 陈述在附录 **518–520** 行，证明在 **1706–1720** 行。

## 附录的证明（逐字）

> We prove that the greedy placement algorithm is a statistically consistent estimator
> of the topology of the true species tree by induction:
> 1. When the species tree has only four leaves, greedy placement is a statistically consistent estimator.
> 2. When it has more than four leaves, let `S'` denote the species tree topology without one
>    species `a`. Then, optimally placing `a` onto `S'` is a statistically consistent estimator.
> The base case is proven in the proof of Theorem 1; the inductive case can be easily proven
> by contradiction: Let `S` be the optimal tree obtained by placing `a` onto `S'`.
> If `S` does not match the topology of the true tree, then `score(S) ≥ score(true)`,
> which contradicts Theorem 1.

## 本文件把它形式化成什么

附录这一步的**全部数学内容**是：**真树一定在候选集里**（它就是「把 `a` 放回它该在的位置」），
而估计量在**候选集上**最大化经验得分。于是：

* **★★★ `caster_greedy_consistent`** —— 只要每步候选集含真选择、估计量在候选集上最大，
  估计量最终就是真选择。**证明只用这两条**，候选集的具体形状（三划分 / 放置位置）
  **不影响结论** —— 这正是归纳步「不依赖算法细节」的原因。
  （基例就是定理 1：候选集取全集。）
* **★★ `tree_strict_separation`** —— 归纳步里「若 `S ≠ 真树` 就与定理 1 矛盾」所依赖的事实：
  两棵**不同构**的 binary 树，其期望得分**严格分离**。
  证明：不同构 ⟹ 逐 quartet 必有不同（★★★ `QuartetDecidesTree` 的**逆否**）
  ⟹ `CASTERIdeal.casterScore_lt_of_not_true`。
* **★★★ `caster_statisticallyConsistent_iso`** —— 把定理 1 从「quartet 选择层」
  升到「**树同构**」层（用既有 ★★★ `QuartetDecidesTree`）。这是 ASTRAL 侧
  `astral_iso` 的同款收口。
* **★★ `IsTrueQ.trans`** —— 「模 `swap` 一致」关系的传递性（树级收口与分离都要用）。

## 🔻 诚实边界

* 本文件**没有**建模「把物种 `a` 放到骨架树 `S'` 上」这个**算法**本身
  （三划分、DP、`O(n²k)` 那些都是实现细节）。附录的归纳证明也不需要它 ——
  它只需要「真树在候选集里」。若将来要证「算法的**输出**确实是候选集上的最大者」，
  那是对 `Algorithm` 的正确性证明，与统计一致性正交。
* 与定理 1 一样，`CASTERSampling.converges`（大数定律）是公理化的，见 `Phylo/Stat/MSC`。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 「模 swap 一致」的传递性 -/

/-- ★★ **`IsTrueQ` 的传递性**：若 `b` 与 `c` 都与 `a` 模 `swap` 一致，则 `b` 与 `c` 也模 `swap` 一致。

（四种组合：`b = a 或 a.swap` × `c = a 或 a.swap`；只有 `b = a`、`c = a.swap` 那一支
需要 `Split.swap_swap`。） -/
theorem IsTrueQ.trans {a b c : QuartetChoice X} (hab : IsTrueQ a b) (hac : IsTrueQ a c) :
    ∀ (S : Finset X) (hS : S.card = 4), b S hS = c S hS ∨ b S hS = (c S hS).swap := by
  intro S hS
  rcases hab S hS with hb | hb <;> rcases hac S hS with hc | hc
  · exact Or.inl (hb.trans hc.symm)
  · exact Or.inr (by rw [hb, hc, Split.swap_swap])
  · exact Or.inr (by rw [hb, hc])
  · exact Or.inl (hb.trans hc.symm)

/-! ## 2. ★★★ 定理 2：贪心放置在「候选集含真选择」时一致 -/

/-- ★★★ **定理 2（贪心放置一致）**：设每一步的候选集 `C n` **含真选择**
（归纳步：真树就是「把物种 `a` 放回正确位置」的那棵树），估计量 `E n` 在 `C n` 上
**最大化经验得分**，则 `E n` 最终与真选择模 `swap` 一致。

**证明**：与 ★★★ `caster_statisticallyConsistent` 逐字相同 ——
`exists_gap` 给统一 gap `δ`，大数定律给 `ε = δ/(2N+1)` 的逐点接近，
`caster_stable_argmax` 收口。区别只在于「最大化」被限制到 `C n`，
而证明需要的唯一一条 `casterScore (emp n) qtrue ≤ casterScore (emp n) (E n)`
由 **`hfeas`（真选择在候选集里）+ `hmax`** 给出。

⇒ **候选集怎么定义（三划分 / 放置位置 / DP 约束）都与结论无关**；
附录归纳步的数学内容到此为止。 -/
theorem caster_greedy_consistent (M : CASTERIdeal X) (sm : CASTERSampling X)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q)
    (C : ℕ → Set (QuartetChoice X)) (hfeas : ∀ n : ℕ, M.qtrue ∈ C n)
    {E : ℕ → QuartetChoice X}
    (hmax : ∀ (n : ℕ) (q : QuartetChoice X), q ∈ C n →
      casterScore (sm.emp M.W n) q ≤ casterScore (sm.emp M.W n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueQ M.qtrue (E n) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := M.exists_gap hNE
  set K : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges M.W (δ / K) (div_pos hδ hKpos)
  refine ⟨N, fun n hn => ?_⟩
  refine caster_stable_argmax M hδ hgap (W := sm.emp M.W n) ?_ ?_
  · simpa [hKdef] using hN n hn
  · exact hmax n M.qtrue (hfeas n)

/-! ## 3. ★★ 树级严格分离与 ★★★ 树级收口 -/

/-- ★★ **树级严格分离**：真树与任何**不同构**的 binary 树，在理想权重表下期望得分严格分离。

这是定理 2 归纳步「若贪心 ≠ 真树则与定理 1 矛盾」所依赖的事实：
**不同构 ⟹ 逐 quartet 必有不同**（★★★ `QuartetDecidesTree` 的逆否命题）
⟹ `CASTERIdeal.casterScore_lt_of_not_true`。 -/
theorem tree_strict_separation (M : CASTERIdeal X)
    {Ttrue qt : QuartetTree.{u, v} X} (hTtrue : Ttrue.tree.IsBinary)
    (hqt : qt.tree.IsBinary) (htrue : IsTrueQ M.qtrue Ttrue.q)
    (hiso : ¬ Nonempty (Iso qt.tree Ttrue.tree)) :
    casterScore M.W qt.q < casterScore M.W M.qtrue := by
  refine M.casterScore_lt_of_not_true fun hqt_true => ?_
  exact hiso (QuartetDecidesTree X qt Ttrue hqt hTtrue (IsTrueQ.trans hqt_true htrue))

/-- ★★★ **树级定理 1**：把 `caster_statisticallyConsistent` 从「quartet 选择层」
升到「**树同构**」层（同 ASTRAL 侧的 `astral_iso`）。

设真树的 quartet 选择是 `qtrue`（`htrue`：`Ttrue.q` 与 `M.qtrue` 模 `swap` 一致），
估计量 `E n` 是第 `n` 个样本上经验得分最大化者且输出 binary 树，
则最终 `(E n).tree` 与真树**同构**。 -/
theorem caster_statisticallyConsistent_iso (M : CASTERIdeal X) (sm : CASTERSampling X)
    {Ttrue : QuartetTree.{u, v} X} (hTtrue : Ttrue.tree.IsBinary)
    (htrue : IsTrueQ M.qtrue Ttrue.q)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q)
    {E : ℕ → QuartetTree.{u, v} X} (hEbin : ∀ n : ℕ, (E n).tree.IsBinary)
    (hE : ∀ (n : ℕ) (q : QuartetChoice X),
      casterScore (sm.emp M.W n) q ≤ casterScore (sm.emp M.W n) (E n).q) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E n).tree Ttrue.tree) := by
  obtain ⟨N, hN⟩ := caster_statisticallyConsistent M sm hNE hE
  exact ⟨N, fun n hn =>
    QuartetDecidesTree X (E n) Ttrue (hEbin n) hTtrue (IsTrueQ.trans (hN n hn) htrue)⟩
