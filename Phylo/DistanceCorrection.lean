/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Phylo.Distance

/-!
# `Phylo.DistanceCorrection` —— KF branch score（F3）与 Jukes–Cantor 距离校正（F4）

`NEXT.md` P0-D 的 F3 / F4 两条「低垂果实」。

## 文献依据（本项目纪律：先读文献再动手）

### F3 —— Kuhner–Felsenstein branch score

文献**在手**：`references/md/KuhnerFelsenstein1994_SimulationComparison.md`
（Kuhner & Felsenstein 1994, *A simulation comparison of phylogeny algorithms under equal and
unequal evolutionary rates*, Mol. Biol. Evol. **11**(3):459–468；本库文件 4049 行全文）。

其 "Comparison of Trees" 一节定义 branch score `Bs` 为：把树看成「**全部可能二分割**
（partition）之集 `(P₁,…,P_N)` 上的**枝长数组**」`B = (b₁,…,b_N)`——`bᵢ` 是树中对应
分割 `Pᵢ` 的那条边的长度，**树中没有该边则取 `bᵢ = 0`**——然后

> `Bs(B,B') = Σ_{i=1}^{N} (bᵢ − b'ᵢ)²`   （原文式 (1)）

文献紧接着指出「A more precise definition of the branch score shows that **its square root
is a metric** and thus should be called a distance」，故 `KF = √Bs`；同处还指出
Robinson–Foulds 的 `dT` 恰是「所有非零枝长都取 `1`」时的 branch score。

⇒ 本文件实现**文献的数组/分割索引层**：`branchScore` = 式 (1)，`kfDistance` = `√branchScore`，
并证明 `kfDistance` 的度量三性质（对称 / 非负 / 零 ⟺ 逐分量相等，外加三角不等式）。

**诚实边界（F3）**：把它接到具体 `Phylogram` 的边上（即给出「树 → 分割索引枝长数组」的
映射）需要 `Split.lean` 的 `splitOfEdge` 对每条边先**选定一侧**、并证明同一条内部边给出
同一个分割——那是另一项工作，本文件**未**做，故这里只给抽象索引层。术语提醒：文献里
的 `Bs` 是**树比较度量**（branch score / KF distance），**不是** K2P 型的序列距离校正。

### F4 —— Jukes–Cantor 距离校正

公式：`d = −(3/4)·ln(1 − (4/3)p)`，`p` 为两位点序列的差异比例（`p < 3/4` 时良定义）。

**诚实边界（F4）**：JC69 原始书章（Jukes & Cantor 1969, *Mammalian Protein Metabolism*）
**不在本库文献中**（付费墙）。`NEXT.md` 称公式可在 `Sturmfels2004` 找到，但**实测**
`references/md/Sturmfels2004_PhylogeneticAlgebraicGeometry.md` §4（第 686–710 行）**只给出
JC 转移矩阵的 Hankel 形式**（对角 `a₀`、非对角 `a₁`），**并未显式写出上述对数校正公式**。
本文件采用的常数由**模型自洽性**确定，并与**库内已证**的闭式逐字核对：
`Phylo/JukesCantor.lean` 已证 `pDiff t i j = 3/4 * (1 − exp (−(4/3)·pathLen))`，
本文件 `pModel` 即其一般形式 `p(d) = (3/4)(1 − e^{−4d/3})`（`d ≥ 0` 为枝长）。
⇒ **常数不是「文献原文引用」，而是「模型自洽 + 库内已证闭式核对」**，报告中如实标注。

## 手算最小例子（先手算再写引理）

* `p = 0`：`1 − (4/3)·0 = 1`，`ln 1 = 0` ⇒ `jcDistance 0 = 0`；
* `p = 3/8`：`1 − (4/3)(3/8) = 1/2`，`ln(1/2) = −ln 2` ⇒ `jcDistance (3/8) = (3/4)·ln 2`
  （模型侧：`(3/4)(1 − e^{−4d/3}) = 3/8 ⇒ e^{−4d/3} = 1/2 ⇒ d = (3/4)ln 2` ✓ 常数一致）；
* `d = 0`：`p = (3/4)(1 − 1) = 0` ⇒ 回到 `jcDistance 0 = 0`；
* `d = 1`：`p = (3/4)(1 − e^{−4/3})`，代入校正：
  `−(3/4)·ln(1 − (4/3)·(3/4)(1 − e^{−4/3})) = −(3/4)·ln(e^{−4/3}) = 1` ✓ 常数与符号均无误；
* `p = 3/4`：`1 − (4/3)(3/4) = 0` ⇒ `log` 参数为 `0`，**退化（文献所谓「饱和」）**。

## 命名与文件纪律

* 两个独立命名空间 `Phylo.KF`（F3）与 `Phylo.JCDist`（F4），避免与并行开发的
  `Phylo.JC`（`Phylo/JukesCantor.lean`，**未 import**）撞名；
* 本文件**不修改**任何既有文件；**无** `sorry` / `axiom` / `def … : Prop` 缺口。
-/

noncomputable section

namespace Phylo

/-! ## F3 —— Kuhner–Felsenstein branch score -/

namespace KF

variable {ι : Type*} [Fintype ι]

/-- **KF branch score**（Kuhner–Felsenstein 1994, 式 (1)）：
`Bs(B,B') = Σᵢ (bᵢ − b'ᵢ)²`。

索引 `ι` 取遍**全部可能二分割**；树中没有对应边时该分量为 `0`
（见 `branchScore_eq_sum_subset`：支撑之外的分量全为 `0` ⟹ 求和可限制在支撑上）。 -/
def branchScore (b b' : ι → ℝ) : ℝ := ∑ i, (b i - b' i) ^ 2

theorem branchScore_def (b b' : ι → ℝ) :
    branchScore b b' = ∑ i, (b i - b' i) ^ 2 := rfl

/-- **KF 距离**：branch score 的平方根（文献：「its square root is a metric」）。 -/
def kfDistance (b b' : ι → ℝ) : ℝ := Real.sqrt (branchScore b b')

theorem kfDistance_def (b b' : ι → ℝ) :
    kfDistance b b' = Real.sqrt (branchScore b b') := rfl

/-- branch score **对称**。 -/
theorem branchScore_comm (b b' : ι → ℝ) : branchScore b b' = branchScore b' b := by
  rw [branchScore_def, branchScore_def]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **分离性**：branch score 为 `0` ⟺ 两个枝长数组逐分量相等。 -/
theorem branchScore_eq_zero_iff {b b' : ι → ℝ} : branchScore b b' = 0 ↔ b = b' := by
  rw [branchScore_def]
  constructor
  · intro h
    funext i
    have hle : (b i - b' i) ^ 2 ≤ ∑ j, (b j - b' j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (b j - b' j)) (Finset.mem_univ i)
    rw [h] at hle
    have hzero : (b i - b' i) ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    nlinarith [sq_nonneg (b i - b' i)]
  · rintro rfl
    simp

@[simp] theorem branchScore_self (b : ι → ℝ) : branchScore b b = 0 := by
  simp [branchScore_def]

/-- branch score **非负**。 -/
theorem branchScore_nonneg (b b' : ι → ℝ) : 0 ≤ branchScore b b' := by
  rw [branchScore_def]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- ★ **「缺边算 0」的形式化**：若 `b` 与 `b'` 在 `s` 之外的分量都为 `0`
（`s` = 两棵树的分割支撑之并），则式 (1) 的求和只须跑 `s`。 -/
theorem branchScore_eq_sum_subset {s : Finset ι} {b b' : ι → ℝ}
    (hb : ∀ i ∉ s, b i = 0) (hb' : ∀ i ∉ s, b' i = 0) :
    branchScore b b' = ∑ i ∈ s, (b i - b' i) ^ 2 := by
  rw [branchScore_def]
  exact (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by simp [hb i hi, hb' i hi]).symm

/-- ★★ **主引理**：`kfDistance` 就是**欧氏距离**
（`EuclideanSpace ℝ ι` 上的 `dist`，即 ℓ² 范数度量）。

⇒ 对称 / 非负 / 三角不等式 / 零的刻画全部由 `dist` 的度量性质**免费继承**。 -/
theorem kfDistance_eq_dist (b b' : ι → ℝ) :
    kfDistance b b' = dist (WithLp.toLp 2 b) (WithLp.toLp 2 b') := by
  rw [kfDistance_def, branchScore_def, EuclideanSpace.dist_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [Real.dist_eq]

/-- `kfDistance` **对称**。 -/
theorem kfDistance_comm (b b' : ι → ℝ) : kfDistance b b' = kfDistance b' b := by
  rw [kfDistance_eq_dist, kfDistance_eq_dist, dist_comm]

/-- `kfDistance` **非负**。 -/
theorem kfDistance_nonneg (b b' : ι → ℝ) : 0 ≤ kfDistance b b' := by
  rw [kfDistance_eq_dist]
  exact dist_nonneg

/-- **分离性**：`kfDistance = 0` ⟺ 两个枝长数组相等（即「同树同权」的数组版本）。 -/
theorem kfDistance_eq_zero_iff {b b' : ι → ℝ} : kfDistance b b' = 0 ↔ b = b' := by
  constructor
  · intro h
    have hbs : branchScore b b' = 0 := by
      have hnn : 0 ≤ branchScore b b' := branchScore_nonneg b b'
      rw [kfDistance_def] at h
      nlinarith [Real.sq_sqrt hnn]
    exact branchScore_eq_zero_iff.mp hbs
  · rintro rfl
    rw [kfDistance_eq_dist, dist_self]

@[simp] theorem kfDistance_self (b : ι → ℝ) : kfDistance b b = 0 := by
  rw [kfDistance_eq_dist, dist_self]

/-- **三角不等式**（文献「√ 是度量」的核心一条）。 -/
theorem kfDistance_triangle (b b' b'' : ι → ℝ) :
    kfDistance b b'' ≤ kfDistance b b' + kfDistance b' b'' := by
  rw [kfDistance_eq_dist b b'', kfDistance_eq_dist b b', kfDistance_eq_dist b' b'']
  exact dist_triangle _ _ _

end KF

/-! ## F4 —— Jukes–Cantor 距离校正 -/

namespace JCDist

/-- **JC 距离校正**：`d = −(3/4)·ln(1 − (4/3)p)`，`p` 为差异比例。

在 `0 ≤ p < 3/4` 上良定义（`jcArg_pos`）；`p = 3/4` 时参数为 `0`，是文献所谓「饱和」，
本定义在 `p ≥ 3/4` 上**不是**距离校正（`jcArg_nonpos_of_three_quarters_le`）。 -/
def jcDistance (p : ℝ) : ℝ := -(3 / 4 : ℝ) * Real.log (1 - (4 / 3 : ℝ) * p)

theorem jcDistance_def (p : ℝ) :
    jcDistance p = -(3 / 4 : ℝ) * Real.log (1 - (4 / 3 : ℝ) * p) := rfl

/-- **JC 模型侧**：枝长 `d` 下的差异比例 `p(d) = (3/4)·(1 − e^{−4d/3})`
（= `Phylo/JukesCantor.lean` 已证的 `pDiff` 闭式的一般形式）。 -/
def pModel (d : ℝ) : ℝ := (3 / 4 : ℝ) * (1 - Real.exp (-(4 / 3 : ℝ) * d))

theorem pModel_def (d : ℝ) :
    pModel d = (3 / 4 : ℝ) * (1 - Real.exp (-(4 / 3 : ℝ) * d)) := rfl

/-! ### 良定义域 -/

/-- ★ **良定义**：`0 ≤ p → p < 3/4 → 0 < 1 − (4/3)p`，故 `Real.log` 的参数为正。 -/
theorem jcArg_pos {p : ℝ} (_h0 : 0 ≤ p) (h3 : p < 3 / 4) : 0 < 1 - (4 / 3 : ℝ) * p := by
  linarith

/-- **饱和点**：`p = 3/4` 时 `log` 的参数恰为 `0`（`1 − (4/3)(3/4) = 0`）。 -/
theorem jcArg_three_quarters : 1 - (4 / 3 : ℝ) * (3 / 4) = 0 := by
  norm_num

/-- `p ≥ 3/4` 时 `log` 的参数 `≤ 0`：校正公式在此**无定义**（文献的「饱和」）。 -/
theorem jcArg_nonpos_of_three_quarters_le {p : ℝ} (h : 3 / 4 ≤ p) :
    1 - (4 / 3 : ℝ) * p ≤ 0 := by
  linarith

/-! ### 端点与数值手算 -/

@[simp] theorem jcDistance_zero : jcDistance 0 = 0 := by
  simp [jcDistance]

/-- 手算最小例子：`p = 3/8` 时 `d = (3/4)·ln 2`（见文件头推导）。 -/
theorem jcDistance_three_eighths : jcDistance (3 / 8) = 3 / 4 * Real.log 2 := by
  rw [jcDistance]
  have h : 1 - (4 / 3 : ℝ) * (3 / 8) = (2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.log_inv]
  ring

/-- `p = 3/4`（饱和）处的取值。

⚠️ **诚实说明**：等式右边来自 Mathlib 的约定 `Real.log 0 = 0`，**不是**「距离为 `0`」的
生物学断言——在 `p = 3/4` 处 `log` 发散，校正公式无意义（文献称之为饱和）。
本定理只记录「参数恰为 `0`」这一算术事实。 -/
theorem jcDistance_three_quarters : jcDistance (3 / 4) = 0 := by
  rw [jcDistance, jcArg_three_quarters, Real.log_zero, mul_zero]

/-! ### 单调性与零点 -/

/-- ★ **非负**：`0 ≤ p < 3/4` 时 `0 ≤ jcDistance p`。 -/
theorem jcDistance_nonneg {p : ℝ} (h0 : 0 ≤ p) (h3 : p < 3 / 4) : 0 ≤ jcDistance p := by
  rw [jcDistance]
  have hx : 0 < 1 - (4 / 3 : ℝ) * p := jcArg_pos h0 h3
  have hx1 : 1 - (4 / 3 : ℝ) * p ≤ 1 := by linarith
  have hlog : Real.log (1 - (4 / 3 : ℝ) * p) ≤ 0 := by
    have h1 : Real.log (1 - (4 / 3 : ℝ) * p) ≤ Real.log 1 := Real.log_le_log hx hx1
    rwa [Real.log_one] at h1
  nlinarith

/-- **零点刻画**：`0 ≤ p < 3/4` 时 `jcDistance p = 0` ⟺ `p = 0`（无差异 ⟺ 距离为 `0`）。 -/
theorem jcDistance_eq_zero_iff {p : ℝ} (h0 : 0 ≤ p) (h3 : p < 3 / 4) :
    jcDistance p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hx : 0 < 1 - (4 / 3 : ℝ) * p := jcArg_pos h0 h3
    have hlog : Real.log (1 - (4 / 3 : ℝ) * p) = 0 := by
      rw [jcDistance] at h
      linarith
    have hx1 : 1 - (4 / 3 : ℝ) * p = 1 := by
      have hcongr := congrArg Real.exp hlog
      rwa [Real.exp_log hx, Real.exp_zero] at hcongr
    linarith
  · rintro rfl
    exact jcDistance_zero

/-- **单调（不降）**：`p ↦ jcDistance p` 在 `[0, 3/4)` 上单调不减。 -/
theorem jcDistance_mono {p p' : ℝ} (_h0 : 0 ≤ p) (_h3 : p < 3 / 4) (h0' : 0 ≤ p')
    (h3' : p' < 3 / 4) (hpp : p ≤ p') : jcDistance p ≤ jcDistance p' := by
  rw [jcDistance, jcDistance]
  have hx' : 0 < 1 - (4 / 3 : ℝ) * p' := jcArg_pos h0' h3'
  have hxy : 1 - (4 / 3 : ℝ) * p' ≤ 1 - (4 / 3 : ℝ) * p := by linarith
  have hlog := Real.log_le_log hx' hxy
  nlinarith

/-- **严格单调**：`p < p'` 时 `jcDistance p < jcDistance p'`。 -/
theorem jcDistance_strictMono {p p' : ℝ} (_h0 : 0 ≤ p) (_h3 : p < 3 / 4) (h0' : 0 ≤ p')
    (h3' : p' < 3 / 4) (hpp : p < p') : jcDistance p < jcDistance p' := by
  rw [jcDistance, jcDistance]
  have hx' : 0 < 1 - (4 / 3 : ℝ) * p' := jcArg_pos h0' h3'
  have hxy : 1 - (4 / 3 : ℝ) * p' < 1 - (4 / 3 : ℝ) * p := by linarith
  have hlog := Real.log_lt_log hx' hxy
  nlinarith

/-! ### 模型侧的取值范围 -/

/-- 模型给出的差异比例非负（`d ≥ 0`）。 -/
theorem pModel_nonneg {d : ℝ} (h : 0 ≤ d) : 0 ≤ pModel d := by
  rw [pModel]
  have hexp : Real.exp (-(4 / 3 : ℝ) * d) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- ★ **模型永远不进饱和区**：`d > 0` 时 `p(d) < 3/4`（这正是校正公式良定义的根据）。 -/
theorem pModel_lt_three_quarters {d : ℝ} (_h : 0 < d) : pModel d < 3 / 4 := by
  rw [pModel]
  have hpos : 0 < Real.exp (-(4 / 3 : ℝ) * d) := Real.exp_pos _
  nlinarith

@[simp] theorem pModel_zero : pModel 0 = 0 := by
  simp [pModel]

/-! ### ★★ 与模型一致（逆关系）：本项最有意义的定理 -/

/-- ★★★ **与模型一致（逆关系）**：把模型给出的差异比例
`p(d) = (3/4)(1 − e^{−4d/3})` 代回校正公式，恰好还原距离 `d`。

（右边的 `d` 即上文 `pModel` 的枝长参数；本式**无**对 `d` 的假设。） -/
theorem jcDistance_pModel (d : ℝ) : jcDistance (pModel d) = d := by
  rw [jcDistance, pModel]
  have h : 1 - (4 / 3 : ℝ) * ((3 / 4 : ℝ) * (1 - Real.exp (-(4 / 3 : ℝ) * d)))
      = Real.exp (-(4 / 3 : ℝ) * d) := by ring
  rw [h, Real.log_exp]
  ring

/-- 上一式的 `0 ≤ d` 形式（对应任务书里带假设的陈述）。 -/
theorem jcDistance_pModel_of_nonneg {d : ℝ} (_h : 0 ≤ d) : jcDistance (pModel d) = d :=
  jcDistance_pModel d

/-- ★★ **反向**：`0 ≤ p < 3/4` 时把校正距离代回模型，恰好还原差异比例 `p`。 -/
theorem pModel_jcDistance {p : ℝ} (h0 : 0 ≤ p) (h3 : p < 3 / 4) :
    pModel (jcDistance p) = p := by
  rw [pModel, jcDistance]
  have h : -(4 / 3 : ℝ) * (-(3 / 4 : ℝ) * Real.log (1 - (4 / 3 : ℝ) * p))
      = Real.log (1 - (4 / 3 : ℝ) * p) := by ring
  rw [h, Real.exp_log (jcArg_pos h0 h3)]
  ring

end JCDist

end Phylo
