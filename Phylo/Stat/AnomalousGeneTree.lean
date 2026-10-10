/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent
import Phylo.Stat.MSCProof

/-!
# `Phylo.Stat.AnomalousGeneTree` —— AGT（异常基因树）与异常区（W11e 后半）

## 0. 文献（**全部在手**，`references/md/`）

* **Degnan & Rosenberg 2006**, *Discordance of species trees with their most likely gene trees*,
  PLoS Genet. **2**(5):e68 —— Definition 1–3（AGT / anomaly zone）、四叶**不对称**物种树
  `(((A,B),C),D)` 的三条显式概率公式（式 (1)(2)(3)）、"`h > g` 对一切正 `x,y`"（正文
  247–248 行）、AGT **计数 0/1/3**（247–262 行）、异常区边界 `a`/`b`（式 (4)(5)，263–305 行）、
  Proposition 2（`n ≥ 5` 任意拓扑都产 AGT，320–470 行）。
  文件：`references/md/DegnanRosenberg2006_DiscordanceSpeciesTreesMostLikelyGeneTrees.md`
  （本文件逐条核读过该 md 的 170–470 行 ✓）。
* **Rosenberg 2013**, MBE **30**(12):2709–2713（统一原理：产生 AGT ⟺ 有两个相邻内部枝）·
  **Rosenberg & Tao 2008**, Syst. Biol. **57**(1):131–140（五叶三分区）·
  **Degnan & Salter 2005**（四叶分布）· **Liu & Edwards 2009**（anomaly zone 内的分析）·
  **Mendes & Hahn 2018** · **Rickert, Fan & Hahn 2025** —— 均在 `references/md/` ✓。
* 库内溯祖器材：`Phylo.Stat.Coalescent`（`survival`/`firstMergeCDF`/`kingmanRate`，
  **149 / 344 / 349 行**）与 `Phylo.Stat.MSCProof`（`rootTopoProb_eq_third`，**104 行**）。

## 1. 术语（严格照 DR2006 Definition 1–3）

给定物种树 `σ`（标号拓扑 `ψ`、枝长向量），基因树拓扑 `G` 称为**异常的（anomalous）**
当且仅当 `P(G | σ) > P(ψ | σ)`；**异常区**是使 AGT 存在的枝长向量集合。

## 2. 本文件做什么（**已证**清单，逐条对应 DR2006 原文）

| # | 内容 | 判据 |
|---|---|---|
| ① | `f`/`g`/`h` ＝ DR2006 **式 (1)(2)(3)** 的逐字形式化（`x`＝**更深**内部枝、`y`＝更浅） | `def` |
| ② | `h − g = (1/3)·e^{−x}·(1 − e^{−y})` ⇒ `h > g`（DR2006 247–248 行"对一切正 `x,y`"） | ★★ `g_lt_h` |
| ③ | `h − f = e^{−y}·(2/3 − e^{−x}/2 − e^{−3x}/9) − (1 − e^{−x})` | ★★★ `h_sub_f` |
| ④ | **AGT 判据**：`h > f ⟺ 1 − e^{−x} < e^{−y}·(2/3 − e^{−x}/2 − e^{−3x}/9)` | ★★★ `h_gt_f_iff` |
| ⑤ | 系数正性：`0 < 2/3 − e^{−x}/2 − e^{−3x}/9`（`x ≥ 0`），且 `≥ 1/18 > 0` | ★★ `coeff_pos` |
| ⑥ | 判据与 `a(x)` 的**代数**一致：`h > f ⟺ e^{−y} > 18(1−e^{−x})/(12 − 9e^{−x} − 2e^{−3x})` | ★★ `h_gt_f_iff_div` |
| ⑦ | **"存在 AGT" 只需一条判据**：`(h > f ∨ g > f) ⟺ h > f`（因 `g < h`） | ★★★ `existsAGT_iff` |
| ⑧ | ★B **AGT 不一定存在**：同一拓扑 `x = 1/100` 下 `y = 1/100` 产 AGT、`y = 100` 不产 | ★★★ `four_taxon_agt_witness` · `four_taxon_no_agt_witness` |
| ⑨ | ★C **非空见证**：`∃ x y, h x y > f x y`（反空真）＋ `∃ x y, ¬ InAnomalyZone x y` | ★★★ `*_nonempty` |
| ⑩ | **超范围**：一般 `n` 的完整刻画（DR2006 Prop 2 / Rosenberg 2013 Thm 1） | 显式 `def … : Prop` 缺口，见 §4 |

**⑧ 的几何直观**（同时解释了为什么四叶就有 AGT）：当 `x, y → 0`（两条内部枝都极短）时，
物种树在基因树分布上趋近**星形树**，此时 DR2006 的 `f → 1/18`（caterpillar）而
`h → 1/9`（balanced）：**对称（balanced）拓扑是星形极限下的众数**，故 `h > f`。
本文件的见证点 `x = y = 1/100` 正是这个极限的**有理数**落地点（无需任何极限论证 ✓）。

## 3. 诚实边界（**没有**变的东西）

* 本文件在**实数层**工作（与 `Phylo.Stat.MSCProof` 同口径）：`1 − e^{−t}` 的**测度层**陈述
  属 W10b；本文件**不**声称给出测度层定理 ✗；
* 本文件**不**给出"`n` 叶物种树 ⇒ 基因树分布"的通用模型 ⇒ 一般 `n`（`n ≥ 5`）的存在性与
  完整刻画**未证**，只登记为缺口（§4，**不**硬编、**不**写成空真的 `Prop` ✗）；
* 四叶**对称**物种树 `((A,B),(C,D))` 不产生 AGT（DR2006 **170–176** 行，依据 Rosenberg 2002
  表 4/5）——该引文与其概率表**不在手** ⇒ 只登记为缺口（§4），**不**当作已证 ✗。

## 4. 缺口（显式 `def … : Prop`，**不弱化、不硬编**）

1. `anomalyZoneBoundaryLog`：DR2006 **式 (4)** 的 `Real.log` 形式（`0 AGT ⟺ y ≥ a(x)`）。
   本文件已证其**代数等价形式**（⑥的除法形式），与 `log` 形式的逐点等价**未证**；
2. `threeAgtCriterion`：DR2006 **式 (5)**（`3 AGT ⟺ y < b(x)`，`b` 的化简式为
   `log(6(3 − 2e^{−x})/(12 − 3e^{−x} − 2e^{−3x}))`）**未证**；
3. `GeneralAnomalyExistence`：一般 `n ≥ 5`（DR2006 Prop 2）的**抽象骨架**——模型 `P` 作为
   **参数**传入（因此该 `Prop` 不是空真：`generalAnomalyExistence_witness` 给出四叶实例 ✓），
   但 `n ≥ 5` 的具体 `P` 构造与归纳（原文 320–470 行）**未做**。
-/

noncomputable section

namespace Phylo.Stat.AnomalousGeneTree

open Real

/-! ## 1. 记号：`Z x = e^{−x}` -/

/-- `Z x = e^{−x}`：长度 `x`（溯祖单位）的枝内**两条**谱系未合并的概率；
与库内 `Coalescent.survival 2 x` 一致（`Z_eq_survival`）。 -/
def Z (x : ℝ) : ℝ := Real.exp (-x)

theorem Z_eq_survival (x : ℝ) : Z x = Coalescent.survival 2 x := by
  rw [Z, Coalescent.survival_two]

theorem Z_pos (x : ℝ) : 0 < Z x := Real.exp_pos _

theorem Z_nonneg (x : ℝ) : 0 ≤ Z x := le_of_lt (Z_pos x)

/-- 初等下界 `1 − t ≤ e^{−t}`（`Real.add_one_le_exp` 取 `−t`）。 -/
theorem one_sub_le_Z (t : ℝ) : 1 - t ≤ Z t := by
  have h := Real.add_one_le_exp (-t)
  have h' : 1 - t ≤ Real.exp (-t) := by linarith
  simpa [Z] using h'

/-- 初等上界 `e^{−t}·(1+t) ≤ 1`（`Real.add_one_le_exp` 取 `t`）。 -/
theorem Z_mul_one_add_le_one (t : ℝ) : Z t * (1 + t) ≤ 1 := by
  have h1 : 1 + t ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have hmul : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
  rw [hmul] at h2
  calc Z t * (1 + t) = (1 + t) * Real.exp (-t) := by rw [Z]; ring
    _ ≤ 1 := h2

/-- 初等上界 `e^{−t} ≤ 1/(1+t)`（`t ≥ 0`）。 -/
theorem Z_le_inv_one_add {t : ℝ} (ht : 0 ≤ t) : Z t ≤ 1 / (1 + t) := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  rw [le_div_iff₀ hpos]
  linarith [Z_mul_one_add_le_one t]

theorem Z_lt_one {x : ℝ} (hx : 0 < x) : Z x < 1 := by
  have h : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  simpa [Z] using h

theorem Z_le_one {x : ℝ} (hx : 0 ≤ x) : Z x ≤ 1 := by
  have h : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simpa [Z] using h

theorem one_sub_Z_eq_firstMergeCDF (x : ℝ) : 1 - Z x = Coalescent.firstMergeCDF 2 x := by
  rw [Coalescent.firstMergeCDF_two, Z]

/-! ## 2. DR2006 式 (1)(2)(3)：四叶 caterpillar `(((A,B),C),D)` 的三个概率

`x` 是**更深**的内部枝长（`A,B,C` 的共同祖先到根），`y` 是**更浅**的内部枝长
（`A,B` 的共同祖先到 `A,B,C` 的共同祖先）—— 与 DR2006 式 (1)–(3) 的 `x`/`y` 逐字一致。 -/

/-- 一致（concordant）拓扑 `(((A,B),C),D)` 的概率 `f(x,y)`（DR2006 **式 (1)**）。 -/
def f (x y : ℝ) : ℝ :=
  1 - (2 / 3) * Z x - (2 / 3) * Z y + (1 / 3) * (Z x * Z y)
    + (1 / 18) * (Z x ^ 3 * Z y)

/-- 不一致拓扑 `((A,C),(B,D))` 的概率 `g(x,y)`（DR2006 **式 (2)**）；`((A,D),(B,C))` 同概率。 -/
def g (x y : ℝ) : ℝ :=
  (1 / 6) * (Z x * Z y) - (1 / 18) * (Z x ^ 3 * Z y)

/-- 不一致拓扑 `((A,B),(C,D))` 的概率 `h(x,y)`（DR2006 **式 (3)**）——`h` 是四叶的 AGT 候选。 -/
def h (x y : ℝ) : ℝ :=
  (1 / 3) * Z x - (1 / 6) * (Z x * Z y) - (1 / 18) * (Z x ^ 3 * Z y)

/-! ### 2.1 次序与关键恒等式 -/

/-- `h − g = (1/3)·e^{−x}·(1 − e^{−y})`。 -/
theorem h_sub_g (x y : ℝ) : h x y - g x y = (1 / 3) * Z x * (1 - Z y) := by
  rw [h, g]; ring

/-- ★★ **DR2006（247–248 行）的 `h(x,y) > g(x,y)`**：对一切 `y > 0`（`x` 任意）成立。 -/
theorem g_lt_h {x y : ℝ} (hy : 0 < y) : g x y < h x y := by
  have hZy : Z y < 1 := Z_lt_one hy
  have hpos : 0 < (1 / 3) * Z x * (1 - Z y) := by
    have hx := Z_pos x
    nlinarith
  rw [← sub_pos, h_sub_g]
  exact hpos

/-- ★★★ **关键恒等式**：`h − f = e^{−y}·(2/3 − e^{−x}/2 − e^{−3x}/9) − (1 − e^{−x})`。 -/
theorem h_sub_f (x y : ℝ) :
    h x y - f x y = Z y * (2 / 3 - Z x / 2 - Z x ^ 3 / 9) - (1 - Z x) := by
  rw [h, f]; ring

/-! ## 3. 四叶 AGT 判据与异常区 -/

/-- ★★ **判据系数正性**：`x ≥ 0` 时 `2/3 − e^{−x}/2 − e^{−3x}/9 > 0`（事实上 `≥ 1/18`）。 -/
theorem coeff_pos {x : ℝ} (hx : 0 ≤ x) : 0 < 2 / 3 - Z x / 2 - Z x ^ 3 / 9 := by
  have h0 : (0 : ℝ) ≤ Z x := Z_nonneg x
  have h1 : Z x ≤ 1 := Z_le_one hx
  have h3 : Z x ^ 3 ≤ 1 := by nlinarith [h0, h1, sq_nonneg (Z x), sq_nonneg (Z x - 1)]
  linarith

/-- ★★★ **四叶 AGT 判据**（本文件的规范形式）：
`h(x,y) > f(x,y) ⟺ 1 − e^{−x} < e^{−y}·(2/3 − e^{−x}/2 − e^{−3x}/9)`。 -/
theorem h_gt_f_iff (x y : ℝ) :
    h x y > f x y ↔ 1 - Z x < Z y * (2 / 3 - Z x / 2 - Z x ^ 3 / 9) := by
  have hk := h_sub_f x y
  rw [gt_iff_lt, ← sub_pos, hk]
  constructor <;> intro hh <;> linarith

/-- 四叶异常区判据（**本文件的规范形式**）：`1 − e^{−x} < e^{−y}·(2/3 − e^{−x}/2 − e^{−3x}/9)`。 -/
def InAnomalyZone (x y : ℝ) : Prop :=
  1 - Z x < Z y * (2 / 3 - Z x / 2 - Z x ^ 3 / 9)

/-- ★★★ **异常区 ⟺ 存在 AGT**（与 `h_gt_f_iff` 定义等价）。 -/
theorem inAnomalyZone_iff (x y : ℝ) : InAnomalyZone x y ↔ h x y > f x y :=
  (h_gt_f_iff x y).symm

/-- ★★ **与 DR2006 式 (4) 的代数一致形式**（除法定理，`x ≥ 0`；这是 §4 缺口 1 的代数内核）：
`h > f ⟺ 18(1 − e^{−x})/(12 − 9e^{−x} − 2e^{−3x}) < e^{−y}`。 -/
theorem h_gt_f_iff_div {x y : ℝ} (hx : 0 ≤ x) :
    h x y > f x y ↔
      18 * (1 - Z x) / (12 - 9 * Z x - 2 * Z x ^ 3) < Z y := by
  rw [h_gt_f_iff]
  have hc : 0 < 2 / 3 - Z x / 2 - Z x ^ 3 / 9 := coeff_pos hx
  have hnum : 0 ≤ 1 - Z x := by
    have h1 : Z x ≤ 1 := Z_le_one hx
    linarith
  have hden : 0 < 12 - 9 * Z x - 2 * Z x ^ 3 := by
    have h0 : (0 : ℝ) ≤ Z x := Z_nonneg x
    have h1 : Z x ≤ 1 := Z_le_one hx
    have h3 : Z x ^ 3 ≤ 1 := by nlinarith [h0, h1, sq_nonneg (Z x), sq_nonneg (Z x - 1)]
    linarith
  have hkey : 18 * (2 / 3 - Z x / 2 - Z x ^ 3 / 9) = 12 - 9 * Z x - 2 * Z x ^ 3 := by ring
  constructor
  · intro hh
    rw [div_lt_iff₀ hden]
    nlinarith [hh, hkey, hc, Z_pos y]
  · intro hh
    have hh' := (div_lt_iff₀ hden).mp hh
    nlinarith [hh', hkey, hc]

/-! ## 4. "存在 AGT" 的判据与两类显式见证（★B · ★C） -/

/-- 在 DR2006 的三类概率下，"物种树 `(((A,B),C),D)` 产生 AGT" ⟺
存在**不一致**拓扑其概率超过一致拓扑（`h`＝深度错配、`g`＝互换型，各两个）。 -/
def ExistsAGT (x y : ℝ) : Prop := f x y < h x y ∨ f x y < g x y

/-- ★★★ **"存在 AGT" 只需一条判据**：由 `h > g`（`y > 0`）知 `g > f ⟹ h > f`，
故 `∃G, P(G) > P(ST) ⟺ h > f` ——**不同拓扑下的判据一致**（都归约到 `h > f`）。 -/
theorem existsAGT_iff {x y : ℝ} (hy : 0 < y) : ExistsAGT x y ↔ h x y > f x y := by
  constructor
  · intro hh
    rcases hh with hh | hh
    · exact hh
    · exact lt_trans hh (g_lt_h hy)
  · intro hh
    exact Or.inl hh

/-- `e^{−1/100}` 的**有理数**上下界：`99/100 ≤ e^{−1/100} ≤ 100/101`
（只用 `Real.add_one_le_exp`，**不用** `exp_bound`）。 -/
theorem exp_neg_hundredth_bounds :
    (99 / 100 : ℝ) ≤ Z (1 / 100) ∧ Z (1 / 100) ≤ 100 / 101 := by
  constructor
  · have h := one_sub_le_Z (1 / 100)
    norm_num at h ⊢
    linarith
  · have h := Z_le_inv_one_add (t := (1 / 100 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith

/-- ★★★ **★B · ★C 的端到端显式见证**：`x = y = 1/100` 时 `h > f`
（即 `P((A,B),(C,D)) > P(((A,B),C),D)`：**异常基因树确实存在**）。
数值余量很大：`h − f ≈ 0.0532 > 1/20`（见 `scripts/msc/w11e_agt_check.py` 的独立复核）。 -/
theorem four_taxon_agt_witness : h (1 / 100) (1 / 100) > f (1 / 100) (1 / 100) := by
  rw [h_gt_f_iff]
  obtain ⟨hlo, hhi⟩ := exp_neg_hundredth_bounds
  have h0 : (0 : ℝ) ≤ Z (1 / 100) := Z_nonneg _
  have hcube : Z (1 / 100) ^ 3 ≤ (100 / 101) ^ 3 := pow_le_pow_left₀ h0 hhi 3
  have hA : (591356 / 9272709 : ℝ) ≤ 2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9 := by
    nlinarith [hhi, hcube]
  have hA0 : (0 : ℝ) < 591356 / 9272709 := by norm_num
  have hprod : (591356 / 9272709 : ℝ) * (99 / 100)
      ≤ Z (1 / 100) * (2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9) := by
    nlinarith [hlo, hA, hA0]
  have hgoal : (1 / 100 : ℝ) < Z (1 / 100) * (2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9) := by
    nlinarith [hprod]
  linarith

/-- ★★★ **★B 的另一半：AGT 不一定存在** —— 同一物种树拓扑（`x = 1/100`）下
`y = 100` 时一致拓扑反而占优（`f > h`，即**没有** AGT）。 -/
theorem four_taxon_no_agt_witness : f (1 / 100) 100 > h (1 / 100) 100 := by
  have hk := h_sub_f (1 / 100) 100
  obtain ⟨hlo, hhi⟩ := exp_neg_hundredth_bounds
  have hA : 2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9 ≤ 2 / 3 := by
    have hp := Z_pos (1 / 100)
    nlinarith [sq_nonneg (Z (1 / 100)), hp]
  have hv : Z 100 ≤ 1 / 101 := by
    have h := Z_le_inv_one_add (t := (100 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hvA : Z 100 * (2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9) ≤ 2 / 303 := by
    have hp := Z_pos 100
    have hA0 : (0 : ℝ) ≤ 2 / 3 - Z (1 / 100) / 2 - Z (1 / 100) ^ 3 / 9 := by
      have := coeff_pos (x := (1 / 100 : ℝ)) (by norm_num)
      linarith
    nlinarith [hv, hA, hp, hA0]
  have hone : (1 : ℝ) / 101 ≤ 1 - Z (1 / 100) := by linarith
  linarith

/-- ★★★ **★C 反空真**：`∃ x y, h x y > f x y`（"存在 AGT"不是空话）。 -/
theorem anomalousGeneTreeExists : ∃ x y : ℝ, h x y > f x y :=
  ⟨1 / 100, 1 / 100, four_taxon_agt_witness⟩

/-- ★★★ **反空真**：异常区**非空**。 -/
theorem inAnomalyZone_nonempty : ∃ x y : ℝ, InAnomalyZone x y :=
  ⟨1 / 100, 1 / 100, (h_gt_f_iff _ _).mp four_taxon_agt_witness⟩

/-- ★★★ **反空真**：异常区**不是全空间**（补集非空）。 -/
theorem not_inAnomalyZone_nonempty : ∃ x y : ℝ, ¬ InAnomalyZone x y :=
  ⟨1 / 100, 100, fun hc =>
    absurd ((h_gt_f_iff _ _).mpr hc) (not_lt.mpr (le_of_lt four_taxon_no_agt_witness))⟩

example : InAnomalyZone (1 / 100) (1 / 100) := (h_gt_f_iff _ _).mp four_taxon_agt_witness

example : ¬ InAnomalyZone (1 / 100) 100 := fun hc =>
  absurd ((h_gt_f_iff _ _).mpr hc) (not_lt.mpr (le_of_lt four_taxon_no_agt_witness))

example : ExistsAGT (1 / 100) (1 / 100) := Or.inl four_taxon_agt_witness

/-! ## 5. 缺口（显式 `def … : Prop`，见 §4 的清单） -/

/-- 异常区边界函数 `a`（DR2006 式 (4) 的化简形式）：`a(x) = log(18(1 − e^{−x})/(12 − 9e^{−x} − 2e^{−3x}))`。 -/
def anomalyZoneBoundary (x : ℝ) : ℝ :=
  Real.log (18 * (1 - Z x) / (12 - 9 * Z x - 2 * Z x ^ 3))

/-- **缺口 1**（DR2006 式 (4) 的 `Real.log` 形式）：`h > f ⟺ y < a(x)`。
本文件已证 ⑥ 的**代数内核**（`h_gt_f_iff_div`），`log` 层的逐点等价**未证**。 -/
def anomalyZoneBoundaryLog : Prop :=
  ∀ x y : ℝ, 0 < x → (h x y > f x y ↔ y < anomalyZoneBoundary x)

/-- 3-AGT 边界函数 `b`（DR2006 式 (5) 的化简形式）：`b(x) = log(6(3 − 2e^{−x})/(12 − 3e^{−x} − 2e^{−3x}))`。 -/
def threeAgtBoundary (x : ℝ) : ℝ :=
  Real.log (6 * (3 - 2 * Z x) / (12 - 3 * Z x - 2 * Z x ^ 3))

/-- **缺口 2**（DR2006 式 (5)）：`g > f ⟺ y < b(x)`（即 3-AGT 区与 1-AGT 区的分界）。 -/
def threeAgtCriterion : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → (g x y > f x y ↔ y < threeAgtBoundary x)

/-- **缺口 3（一般 `n`）**：DR2006 Proposition 2（`n ≥ 5` 任意物种树拓扑都产 AGT）与
Rosenberg 2013 Theorem 1（产生 AGT ⟺ 有两个相邻内部枝）的**抽象骨架**：
模型 `P : 枝长 → 基因树 → ℝ` 与物种树拓扑 `st` 作为**参数**传入（**不假设**任何模型性质 ✓），
断言"存在枝长使某基因树比物种树更可能"。
本库没有 `n` 叶标号拓扑＋枝长向量 ⇒ 基因树分布的**通用**模型，故 `n ≥ 5` 的实例化**未做**；
但该 `Prop` **不是**空真：`generalAnomalyExistence_witness` 给出四叶实例 ✓。 -/
def GeneralAnomalyExistence (GeneTree BranchLengths : Type) (P : BranchLengths → GeneTree → ℝ)
    (st : GeneTree) : Prop :=
  ∃ b : BranchLengths, ∃ g : GeneTree, P b g > P b st

/-- ★★ **反空真**：`GeneralAnomalyExistence`（缺口 3 的骨架）在四叶层**真的成立**
——`Bool` 编码两条不一致候选（`true ↦ h`、`false`＝物种树拓扑 `↦ f`），`x = y = 1/100` 见证。 -/
theorem generalAnomalyExistence_witness :
    GeneralAnomalyExistence Bool (ℝ × ℝ)
      (fun b i => if i then h b.1 b.2 else f b.1 b.2) false :=
  ⟨(1 / 100, 1 / 100), true, by simpa using four_taxon_agt_witness⟩

end Phylo.Stat.AnomalousGeneTree
