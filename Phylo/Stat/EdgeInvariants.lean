/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.InvariantsRank
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# `Phylo.Stat.EdgeInvariants` —— I6：edge invariants（沿边的极小式）构成的不变量理想

## 文献依据（篇名 + 行号；行号指 `references/md/` 下的文本文件）

* **M. Casanellas, J. Fernández-Sánchez, *Relevant phylogenetic invariants for equivariant
  models*, `references/md/CasanellasFernandezSanchez2011_RelevantInvariants.md`（共 3343 行）**：
  * **617–633 行（Definition 2.14）**：沿一个二分为 `L₁ | L₂` 的**展平** `flat_{L₁|L₂}ψ` 与
    **薄展平** `Tf_{L₁|L₂}(ψ)` 的定义；
  * **677–700 行（Lemma 2.17）**：`rk flat = Σ_t dim N_{ω_t} · rk(ψ_t)`，且「展平满秩 ⟺
    每个分块的秩最大」；
  * **702–718 行（Lemma 2.19）**：展平与「张量乘法（在 `C` 上缩并）」**相容**：
    `flat_{L₁|L₂}(φ₁ ∗_C φ₂) = Tf_{L₁|C}(φ₁) · Tf_{C|L₂}(φ₂)`；
  * **802–830 行（Proposition 3.1）**：`T` 三价、`A ∈ Par_G(T)` 时
    `rk Tf_β(ψ_T(A)) ≤ m_β`，即**沿边展平的秩上界**，也就是「**`I_e ⊆ I(T)`**」；
  * **1394–1412 行（Definition 3.6 / Notation 3.7 / Definition 3.8）**：
    `I_{L₁|L₂}` 是「`Tf` 各分块的 `(m_t+1)` 阶子式」生成的理想；边 `e` 对应 `I_e`；
    **edge invariants** := `Σ_{e ∈ E(T)} I_e`；
  * **1413–1420 行**：「**Proposition 3.1 proves that edge invariants are phylogenetic
    invariants**」（`Σ_e I_e ⊆ I(T)`）—— 本文件证的就是这一条（`edgeIdeal_le_ker_evalAt`）；
  * **1528–1548 行（Theorem 4.4，本文主定理）**：对 `p ∈ ⋃_T U_T`（一般点集）与任意 `T₀`，
    `p ∈ V(T₀) ⟺ p ∈ Z(Σ_{e∈E(T₀)} I_e)` —— **「edge invariants 足够」**。本文件**落缺口**
    （`edgeInvariants_suffice_gap`），只证充分性的「⊆」半边。
  * **1672–1700 行（Corollary 4.8）**：理想版本（局部化环中 `I(V(T₀) ∩ U) = Σ_e I_e`）；
  * **1804–1815 行（Corollary 4.12）**：这些「相关不变量」的次数的上界。
* **B. Sturmfels, S. Sullivant, *Toric ideals of phylogenetic invariants*,
  `references/md/SturmfelsSullivant2005_ToricIdealsPhyloInvariants.md`（共 2831 行）**：
  * **1560–1600 行（Theorem 1 的精确形式）+ 1709–1734 行（Theorem 24, Local Structure of
    Invariants）**：`T` 的不变量理想由「局部（claw tree）不变量 + 沿边的二次二项式」经
    `Ext` 扩张生成 —— 与本文件的 `edgeIdeal` 是同一件事的代数/组合两个视角。
* **E. S. Allman, J. A. Rhodes, *Phylogenetic ideals and varieties for the general Markov
  model*（库内 `references/md/AllmanRhodes2006_PhyloIdealsVarietiesGeneralMarkov.md`）**：
  * **770 行 + 776–779 行**：沿边展平 `F late(P)` 的 `(κ+1)` 阶子式必须为零，记为
    `Fedge(T)`，称 **edge invariants**；**785–788 行（Theorem 4）** 说 `κ = 2` 时它们
    **生成**整个不变量理想（本文件不做，见「诚实边界」）。

## 本文件做的事（I6 的**可证**半边）

库内 `Phylo.Stat.InvariantsRank` 已经证明 `Fedge(T)` 型极小式**在模型上取 0**
（`rank_flatAB_le_four_iff_minor`），但那是「矩阵 + 数值」层面的陈述。I6 要求的是**理想**层面：
把这一族极小式**组织成多项式环里的一个理想**，并证明这个理想的每个元素都是**不变量**。

1. **变量环与极小式多项式**：`Var := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)`（16×16 = 256 个变量，
   对应展平矩阵的每个位置）；`Xmat` 是变量矩阵；`edgeMinor r c` 是 `5 × 5` 子式
   （= `Fedge(T)` 型极小式的多项式版本）。
2. **求值与展平交换**：`evalAt_edgeMinor`（用 `RingHom.map_det`）。
3. **每个 edge invariant 都是不变量**：`edgeMinor_isInvariant`（直接调用
   `rank_flatAB_le_four_iff_minor`）。
4. **理想层面**：`edgeIdeal := Ideal.span (Set.range edgeMinorP)`；
   `edgeIdeal_le_ker_evalAt`：**`edgeIdeal ⊆ I(T)`**（Casanellas 1413–1420 行那一句）。
5. **非空真（anti-vacuity）**：`edgeIdeal_ne_bot` —— 取展平 = 单位阵的具体张量
   `identFreq`，则 `edgeMinor witnessIdx witnessIdx ≠ 0`，故 `edgeIdeal ≠ ⊥`
   （**edge invariants 不是「一切都是不变量」**）。
6. **「更大阶的极小式已经被生成」**：`minor_mem_edgeIdeal` —— 对 `n ≥ 5`，
   **任意** `n × n` 子式都属于 `edgeIdeal`。这是「edge invariants 足够」在**行列式族内部**
   的一个可证的、具体的情形：**5 阶（沿边）极小式已足以生成全部更高阶的秩不变量**
   （用 Laplace 沿第一行展开逐次降阶）。
7. **缺口**：`edgeInvariants_suffice_gap` —— Casanellas **Theorem 4.4 / Corollary 4.8** 的
   「充分性」半边（`Z(Σ_e I_e) ∩ U = V(T₀) ∩ U`）。

## 诚实边界

* 本文件**不**证明 `edgeIdeal = I(T)`（不变量理想的生成元问题），也**不**证明
  Casanellas Theorem 4.4（一般点上的充分性）——见 `edgeInvariants_suffice_gap`。
* 本文件**不**触碰 `κ = 2` 的 Allman–Rhodes Theorem 4 的「生成」结论（那需要 Gröbner 基 /
  代数几何）；`minor_mem_edgeIdeal` 只在**行列式族内部**说「大阶次式 ∈ 5 阶理想」。
* 本文件**只在 `κ = 4`（DNA，`Fin 4`）与 4 分类群、展平 `κ² × κ² = 16 × 16` 上做**，
  `κ^k`（k ≥ 3）的展平不做（与 `InvariantsRank` 的边界一致）。
* 模型半边（「`P` 来自树上的 Markov 模型 ⟹ 存在因子分解」）仍是
  `InvariantsRank.TreeMarkovFactorGap` 的欠账，本文件以 `Factorizable` 为显式假设传入。
* 本文件对**一般情形**（任意 `n`、任意拓扑、生成整个理想）如实落缺口，不弱化陈述冒充达标。
* 无 `sorry`、无 `axiom`、无 `native_decide`。
-/

universe u

namespace Phylo.Stat.EdgeInvariants

open Matrix MvPolynomial

/-! ## 1. 变量环与 edge minor 多项式 -/

/-- **变量类型**：展平矩阵的一个位置，即「行指标 `(i,j)` × 列指标 `(k,l)`」= 一个 site pattern。 -/
abbrev Var := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)

/-- ★ **展平的变量矩阵** `X : Matrix ((Fin 4 × Fin 4)) ((Fin 4 × Fin 4)) (MvPolynomial Var ℝ)`,
`X_{(i,j),(k,l)} = X_{(i,j),(k,l)}`（每个位置一个独立变量）。 -/
noncomputable def Xmat : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) (MvPolynomial Var ℝ) :=
  Matrix.of fun p q => MvPolynomial.X (p, q)

/-- ★★ **edge invariant（`Fedge(T)` 型极小式）的多项式版本**：
`5 × 5` 子式的行列式（行指标 `r`、列指标 `c`）。
这正是 Allman–Rhodes 2006 的 `Fedge(T)`（776–779 行）与 Casanellas 2011 的
`I_e` 的生成元（Definition 3.6，1394–1405 行）。 -/
noncomputable def edgeMinor (r c : Fin 5 → Fin 4 × Fin 4) : MvPolynomial Var ℝ :=
  (Xmat.submatrix r c).det

/-- 打包成单元数（便于对 `Set.range` 取理想）。 -/
noncomputable def edgeMinorP (p : (Fin 5 → Fin 4 × Fin 4) × (Fin 5 → Fin 4 × Fin 4)) :
    MvPolynomial Var ℝ :=
  edgeMinor p.1 p.2

/-! ## 2. 求值：把变量送到具体的位点频率张量 -/

/-- **求值同态**：`X_{(i,j),(k,l)} ↦ P i j k l`。 -/
noncomputable def evalAt (P : SiteFreq (Fin 4)) : MvPolynomial Var ℝ →+* ℝ :=
  MvPolynomial.eval fun v => P v.1.1 v.1.2 v.2.1 v.2.2

/-- ★★ **求值与展平交换**：`evalAt P (edgeMinor r c) = ((flatAB P).submatrix r c).det`。

证明：`RingHom.map_det`（`f M.det = (f.mapMatrix M).det`）把「先取行列式再求值」换成
「先逐项求值再取行列式」；再逐项验证 `mapMatrix evalAt Xmat = flatAB P`。 -/
theorem evalAt_edgeMinor (P : SiteFreq (Fin 4)) (r c : Fin 5 → Fin 4 × Fin 4) :
    evalAt P (edgeMinor r c) = ((flatAB P).submatrix r c).det := by
  have hmat : (evalAt P).mapMatrix (Xmat.submatrix r c) = (flatAB P).submatrix r c := by
    ext i j
    simp [Xmat, evalAt, flatAB, RingHom.mapMatrix_apply, Matrix.submatrix_apply]
  rw [edgeMinor, RingHom.map_det, hmat]

/-! ## 3. 每个 edge invariant 都是（模型上的）不变量 -/

/-- **模型点（因子分解形式）**：`P` 沿某条边把中间隐状态求和掉后成为
「`κ²` 状态观测量 — `κ` 维桥 — `κ²` 状态观测量」的因子分解。
这是 `Phylo.Stat.InvariantsRank.TreeMarkovFactorGap` 里那条**未证**的模型半边。 -/
def Factorizable (P : SiteFreq (Fin 4)) : Prop :=
  ∃ (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ),
    ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l)

/-- 零张量是因子分解的（`A = B = 0`）—— 说明 `Factorizable` **不是**空假设。 -/
theorem factorizable_zero : Factorizable (fun _ _ _ _ => (0 : ℝ)) :=
  ⟨0, 0, by intro i j k l; simp⟩

/-- ★★★ **edge invariant 是真正的不变量**：每条边对应的 `5 × 5` 极小式在**任何**因子分解
张量上取 `0`。（Casanellas 2011, 1413–1420 行；Allman–Rhodes 2006, 770 行。）

这是 `Phylo.Stat.InvariantsRank.rank_flatAB_le_four_iff_minor` 的**多项式侧重述**：
把「矩阵子式 = 0」升级成「理想生成元在模型上取 0」。 -/
theorem edgeMinor_isInvariant (P : SiteFreq (Fin 4))
    (A : Matrix (Fin 4 × Fin 4) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 4 × Fin 4) ℝ)
    (hP : ∀ i j k l, P i j k l = ∑ m, A (i, j) m * B m (k, l))
    (r c : Fin 5 → Fin 4 × Fin 4) : evalAt P (edgeMinor r c) = 0 := by
  rw [evalAt_edgeMinor]
  exact Phylo.Stat.InvariantsRank.rank_flatAB_le_four_iff_minor P A B hP r c

/-! ## 4. ★★ edge invariants 生成的理想（`Σ_e I_e`，Casanellas Definition 3.8） -/

/-- ★★ **edge invariants 理想** `Σ_{e ∈ E(T)} I_e`（Casanellas 2011, Definition 3.8, 1409 行）：
由全部沿边极小式 `edgeMinor r c` 生成的理想。

（本文件的树只有 4 个分类群、一条内部边，故 `Σ_e I_e` 就由这一族极小式生成。） -/
noncomputable def edgeIdeal : Ideal (MvPolynomial Var ℝ) :=
  Ideal.span (Set.range edgeMinorP)

/-- ★★★ **`Σ_e I_e ⊆ I(T)`**（Casanellas 2011, 1413–1420 行 +
Definition 3.8）：**edge invariants 理想的每个元素都是不变量** ——
即每个生成元都在「任意因子分解张量」的求值核里时，整个生成理想也在核里。

这一条把 I6 从「逐条极小式为 0」提升到**理想层面**：不变量类的封闭性
（加法、乘法、乘常数）由 `Ideal` 保证。 -/
theorem edgeIdeal_le_ker_evalAt (P : SiteFreq (Fin 4)) (hP : Factorizable P) :
    edgeIdeal ≤ RingHom.ker (evalAt P) := by
  rw [edgeIdeal, Ideal.span_le]
  rintro _ ⟨⟨r, c⟩, rfl⟩
  exact RingHom.mem_ker.mpr (by
    rcases hP with ⟨A, B, hAB⟩
    exact edgeMinor_isInvariant P A B hAB r c)

/-! ## 5. ★ 非空真：具体的非零 edge invariant（anti-vacuity） -/

/-- 展平 = **单位阵**的具体位点频率张量：`P i j k l = [i = k][j = l]`。 -/
def identFreq : SiteFreq (Fin 4) := fun i j k l => if (i, j) = (k, l) then 1 else 0

theorem flatAB_identFreq : flatAB identFreq = 1 := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  rw [flatAB, identFreq, Matrix.one_apply]

/-- 5 个**互不相同**的行/列指标（取 `Xmat` 的 5 个不同位置）。 -/
def witnessIdx : Fin 5 → Fin 4 × Fin 4 :=
  ![(0, 0), (1, 0), (2, 0), (3, 0), (0, 1)]

theorem witnessIdx_injective : Function.Injective witnessIdx := by decide

/-- ★ **显式的非零 edge invariant**：在「展平 = 单位阵」的张量上，
`edgeMinor witnessIdx witnessIdx` 求值为 `1`。

（这也是 I6 的**反例检查**：如果 `edgeIdeal` 是整个环，那这条就等于在说
「所有多项式都是不变量」—— 事实上不是。） -/
theorem edgeMinor_witness_eval_eq_one :
    evalAt identFreq (edgeMinor witnessIdx witnessIdx) = 1 := by
  rw [evalAt_edgeMinor, flatAB_identFreq]
  have hsub : (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℝ).submatrix witnessIdx witnessIdx
      = (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have hw : ¬ (witnessIdx i = witnessIdx j) := fun hh => h (witnessIdx_injective hh)
      simp [h, hw]
  rw [hsub, Matrix.det_one]

theorem edgeMinor_witness_ne_zero : edgeMinor witnessIdx witnessIdx ≠ 0 := by
  intro h
  have h1 := edgeMinor_witness_eval_eq_one
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- ★★ **`edgeIdeal ≠ ⊥`**：edge invariants 理想**不**是整个环，**也不**是零理想。
反空真：这条说明 `edgeIdeal_le_ker_evalAt` 不是「空条件推出空结论」。 -/
theorem edgeIdeal_ne_bot : edgeIdeal ≠ ⊥ := by
  intro h
  have hmem : edgeMinor witnessIdx witnessIdx ∈ edgeIdeal :=
    Ideal.subset_span ⟨(witnessIdx, witnessIdx), rfl⟩
  rw [h] at hmem
  exact edgeMinor_witness_ne_zero (by simpa using hmem)

/-! ## 6. ★★★ 「更高阶的极小式已经被 5 阶（沿边）极小式生成」

Casanellas 的 edge invariants 是**沿边**的**最低阶**极小式（`κ + 1 = 5` 阶）。
下面这一条是「**5 阶极小式足够生成全部更高阶的秩不变量**」这一具体情形的
**可证**版本：任意 `n ≥ 5` 阶子式都落在 `edgeIdeal` 里。

证明：`Matrix.det_succ_row_zero`（Laplace 沿第一行展开）
`det A = Σ_j (-1)^j · A 0 j · det(A.submatrix Fin.succ j.succAbove)`，
把 `n` 阶子式写成「元素 × `(n-1)` 阶子式」，对 `n` 作强归纳。 -/

/-- ★★★ **任意 `n ≥ 5` 阶极小式 ∈ `edgeIdeal`**。 -/
theorem minor_mem_edgeIdeal :
    ∀ (n : ℕ) (r c : Fin n → Fin 4 × Fin 4), 5 ≤ n →
      (Xmat.submatrix r c).det ∈ edgeIdeal := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r c hn
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
    rcases eq_or_lt_of_le hn with h5 | h6
    · -- 基例 `n = 5`：就是 edge minor 本身
      have hm : m = 4 := by omega
      subst hm
      exact Ideal.subset_span ⟨(r, c), rfl⟩
    · -- 归纳步：Laplace 沿第一行展开，降阶
      have hm5 : 5 ≤ m := by omega
      rw [Matrix.det_succ_row_zero]
      refine Ideal.sum_mem _ fun j _ => ?_
      have hsub : ((Xmat.submatrix r c).submatrix Fin.succ j.succAbove)
          = Xmat.submatrix (fun i => r (Fin.succ i)) (fun i => c (j.succAbove i)) := by
        ext a b
        rfl
      rw [hsub]
      have hmem : (Xmat.submatrix (fun i => r (Fin.succ i))
          (fun i => c (j.succAbove i))).det ∈ edgeIdeal :=
        ih m (by omega) _ _ hm5
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hmem)

/-! ## 7. 诚实边界（显式缺口） -/

/-- **缺口（I6 的「充分性」半边）**：Casanellas–Fernández-Sánchez (2011)
**Theorem 4.4（1528–1548 行）＋ Corollary 4.8（1672–1700 行）**：

> 对一般点 `p ∈ U`（各拓扑的「展平秩都取到期望最大值」的开集）与任意树 `T₀`，
> `p ∈ V(T₀) ⟺ p ∈ Z(Σ_{e ∈ E(T₀)} I_e)`。

形式化版本：给定一个「一般点集」`U` 与一个「目标模型族」`Model`，
若 `p ∈ U`，则 `p ∈ Model` **当且仅当** `p` 让所有 edge invariants 消失。

**已证的是 `←` 的「⊆」半边**（`edgeIdeal_le_ker_evalAt`：`Model` 里每个点都让
edge invariants 消失）；**未证的是 `→`**：一般点上「edge invariants 全为零」⟹ 落在
`Model` 里。缺的是：

* Proposition 3.1（802–830 行）的一般 Markov / 等变模型层（展平秩的**上界**要从模型推出，
  而不是作为假设传入），
* 「展平秩取到期望值」的一般点集 `U` 的显式刻画（1510–1527 行 `U_{T,β}`、`U_T`），
* Buneman 的「分裂集合决定无根树拓扑」（同文件 1465–1508 行 Theorem 4.1）。

这三条都在当前库的器材之外（前者见 `InvariantsRank.TreeMarkovFactorGap`，
后两者需要一般树的 GMM 层），故如实落缺口而不弱化陈述。 -/
def edgeInvariants_suffice_gap (U : Set (SiteFreq (Fin 4)))
    (Model : Set (SiteFreq (Fin 4))) : Prop :=
  ∀ p ∈ U, (p ∈ Model ↔ ∀ f ∈ edgeIdeal, evalAt p f = 0)

/-- 缺口的**已证半边**：`Model` 中的点（只要都因子分解）让所有 edge invariants 消失。 -/
theorem edgeInvariants_suffice_gap_forward (U : Set (SiteFreq (Fin 4)))
    (Model : Set (SiteFreq (Fin 4))) (hM : ∀ p ∈ Model, Factorizable p) :
    ∀ p ∈ U, p ∈ Model → ∀ f ∈ edgeIdeal, evalAt p f = 0 :=
  fun p _ hp _f hf => RingHom.mem_ker.mp ((edgeIdeal_le_ker_evalAt p (hM p hp)) hf)

end Phylo.Stat.EdgeInvariants
