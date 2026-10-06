/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.ASTRAL

/-!
# `Phylo.Stat.Stability` —— 一致性的**通用引擎**（得分 gap + 稳定性）

四个算法的一致性证明可拆成三层，其中 `② ③` **与算法无关**：

```
① 理想一致性   score 在真树上唯一最大            （各算法分头证）
② gap 引理     严格最大 ⟹ 存在正 gap δ            （有限性，本文件）
③ 稳定性       频率扰动 < δ/(2N) ⟹ argmax 不变    （本文件）
──────────────────────────────────────────────
⟹ 统计一致性   （① + ② + ③ + MSC 大数定律）
```

## 本文件证什么

* `score_lt_of_not_true` —— 「非真」选择函数的得分**严格**小于真树；
* ★ `exists_gap` —— 上述严格性在**有限**选择函数空间上一致化，给出正的 `δ`；
* ★★ `stable_argmax` —— 频率扰动 `ε < δ/(2N+1)` 时 argmax 仍为「真选择」；
* ★★★ `astral_statisticallyConsistent` —— **ASTRAL 统计一致性（quartet 层面）**。

⚠️ **诚实边界**：`MSCSampling.converges` 是公理化的（见 `Phylo.Stat.MSC`）。
把「一致性提升到树同构」还需「quartet 系统决定树」（见 `Phylo.Stat.QuartetDecides`）。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **「真选择」**：`q` 在每个 4-元集上给出的 quartet 与真树一致（模 `swap`，即无向意义相同）。 -/
def IsTrueChoice (m : MSCFreq.{u, v} X) (q : QuartetChoice X) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4), q S hS = m.q S hS ∨ q S hS = (m.q S hS).swap

open Classical in
/-- 非真选择函数的存在性等价形式（剥掉两层 `∀` 并展开 `¬(a ∨ b)`）。 -/
theorem exists_false_of_not_isTrueChoice {m : MSCFreq.{u, v} X} {q : QuartetChoice X}
    (h : ¬ IsTrueChoice m q) :
    ∃ (S : Finset X) (hS : S.card = 4), q S hS ≠ m.q S hS ∧ q S hS ≠ (m.q S hS).swap := by
  by_contra hc
  apply h
  intro S hS
  by_cases h1 : q S hS = m.q S hS
  · exact Or.inl h1
  · refine Or.inr ?_
    by_contra h2
    exact hc ⟨S, hS, h1, h2⟩

/-- ★ **非真选择函数的得分严格小于真树**（`MSCFreq.majorizes` 的求和形式）。 -/
theorem score_lt_of_not_true (m : MSCFreq.{u, v} X) {q : QuartetChoice X}
    (h : ¬ IsTrueChoice m q) : astralScore m.freq q < astralScore m.freq m.q := by
  obtain ⟨S, hS, h1, h2⟩ := exists_false_of_not_isTrueChoice h
  exact Finset.sum_lt_sum
    (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    (fun S1 _ => m.p_le S1.1 S1.2 (q S1.1 S1.2))
    ⟨⟨S, hS⟩, Finset.mem_univ _, m.majorizes S hS (q S hS) h1 h2⟩

/-! ## ② gap 引理 -/

open Classical in
/-- ★ **得分 gap**：存在统一的 `δ > 0`，使任何非真选择函数的得分至少比真树低 `δ`。

由**有限性**（`QuartetChoice X` 是有限类型）得到：取「真树得分 − 各非真得分」
这一有限实数集的最小值即可。 -/
theorem exists_gap (m : MSCFreq.{u, v} X)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : QuartetChoice X, ¬ IsTrueChoice m q →
      astralScore m.freq q + δ ≤ astralScore m.freq m.q := by
  classical
  obtain ⟨q0, hq0⟩ := hNE
  set S : Finset ℝ := ((Finset.univ : Finset (QuartetChoice X)).filter
      (fun q => ¬ IsTrueChoice m q)).image
      (fun q => astralScore m.freq m.q - astralScore m.freq q) with hSdef
  have hne : S.Nonempty := by
    refine ⟨astralScore m.freq m.q - astralScore m.freq q0, ?_⟩
    rw [hSdef]
    exact Finset.mem_image.mpr
      ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩, rfl⟩
  refine ⟨S.min' hne, ?_, ?_⟩
  · obtain ⟨q1, hq1, heq⟩ := Finset.mem_image.mp (S.min'_mem hne)
    rw [← heq]
    have := score_lt_of_not_true m (Finset.mem_filter.mp hq1).2
    linarith
  · intro q hq
    have hmem : astralScore m.freq m.q - astralScore m.freq q ∈ S := by
      rw [hSdef]
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    have h1 : S.min' hne ≤ astralScore m.freq m.q - astralScore m.freq q := S.min'_le _ hmem
    linarith

/-! ## ③ 稳定性 -/

/-- **`ε` 扰动下的得分比较上界**：`score_D(q) ≤ score_{D'}(q) + N·ε`（逐点 `ε`-接近）。

其中 `N = #(4-元集)`。 -/
theorem astralScore_le_add (D D1 : QuartetFreq X) (q : QuartetChoice X) {ε : ℝ}
    (hD : FreqClose D D1 ε) :
    astralScore D q ≤ astralScore D1 q + ε * (Fintype.card {S : Finset X // S.card = 4}) := by
  have hdiff : astralScore D q - astralScore D1 q ≤
      ε * (Fintype.card {S : Finset X // S.card = 4}) := by
    rw [astralScore, astralScore, ← Finset.sum_sub_distrib]
    calc (Finset.univ : Finset {S : Finset X // S.card = 4}).sum
          (fun S => D.p S.1 S.2 (q S.1 S.2) - D1.p S.1 S.2 (q S.1 S.2))
        ≤ (Finset.univ : Finset {S : Finset X // S.card = 4}).sum (fun _ => ε) :=
          Finset.sum_le_sum fun S _ => le_trans (le_abs_self _) (hD S.1 S.2 (q S.1 S.2)).le
      _ = ε * (Fintype.card {S : Finset X // S.card = 4}) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  linarith

open Classical in
/-- ★★ **稳定性**：若频率扰动 `ε < δ / (2N + 1)`，则任何在扰动数据上得分不低于真树的
选择函数，必是「真选择」。

`N = #(4-元集)`，`δ` 为 `exists_gap` 给出的 gap。 -/
theorem stable_argmax (m : MSCFreq.{u, v} X) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuartetChoice X, ¬ IsTrueChoice m q →
      astralScore m.freq q + δ ≤ astralScore m.freq m.q)
    {D : QuartetFreq X}
    (hD : FreqClose D m.freq (δ / (2 * (Fintype.card {S : Finset X // S.card = 4}) + 1)))
    {q : QuartetChoice X}
    (hmax : astralScore D m.q ≤ astralScore D q) : IsTrueChoice m q := by
  by_contra hnot
  set N : ℝ := (Fintype.card {S : Finset X // S.card = 4} : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * N + 1) with hεdef
  have hN1 : (2 : ℝ) * N + 1 ≠ 0 := by linarith
  have hεN : ε * (2 * N + 1) = δ := by rw [hεdef, div_mul_cancel₀ _ hN1]
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos hδ (by linarith)
  have h1 : astralScore D q ≤ astralScore m.freq q + ε * N := astralScore_le_add D m.freq q hD
  have h2 : astralScore m.freq m.q ≤ astralScore D m.q + ε * N :=
    astralScore_le_add m.freq D m.q (FreqClose_symm hD)
  have h3 : astralScore m.freq q + δ ≤ astralScore m.freq m.q := hgap q hnot
  have h4 : 2 * ε * N < δ := by rw [← hεN]; nlinarith
  linarith

/-! ## ★★★ ASTRAL 统计一致性（quartet 层面） -/

open Classical in
/-- ★★★ **ASTRAL 的统计一致性**（quartet 层面）：

设 `E` 是 ASTRAL 型估计量（在每个频率表上返回一个得分最大化者），
则在 MSC 采样下（`MSCSampling`，含公理化的大数定律），**最终** `E` 的 quartet 选择
与真树一致（模 `swap`）。

**证明**：大数定律给最终 `ε`-接近（取 `ε = δ/(2N+1)`），
`stable_argmax` 把 `IsASTRAL`（得分最大化）转成 `IsTrueChoice`。

⚠️ 两条边界：(i) `converges` 是公理化的；(ii) 结论止于 quartet 层面 ——
升级为树同构需 `Phylo.Stat.QuartetDecides`。 -/
theorem astral_statisticallyConsistent (m : MSCFreq.{u, v} X) (sm : MSCSampling.{u, v} X)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice m (E (sm.emp n)).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_gap m hNE
  set M : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges m (δ / M) (div_pos hδ hMpos)
  refine ⟨N, fun n hn => ?_⟩
  refine stable_argmax (D := sm.emp n) m hδ hgap ?_ ?_
  · simpa [hMdef] using hN n hn
  · exact hE (sm.emp n) m.toQuartetTree
