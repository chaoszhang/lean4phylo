/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERGeneTree
import Phylo.Stat.MSCKingman

/-!
# `Phylo.Stat.SiteRateMixture` —— 有限支撑的**速率/参数层**与 `Ã`（W13b ＋ 识别等式 W13c）

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
**Supplementary** `sm.tex` 的 `Proof of Theorem 1` 前置 remark（**1269–1285** 行）：
「equilibrium frequencies, transition rates, and mutation rates for each gene are
**independently sampled from a uniformly bounded distribution**」、「all … are **positive**」。

## 这一批在整条链里的位置

```
W13 模型（老师 2026-10-11 口述）：
  θ ~ ν（溯祖时间数据）→ T' ~ τd θ（基因树拓扑）→ k ~ w（速率/参数指标）
  → 位点由 (scale θ k, T') 生成
        │
        ├── §1 有限支撑的速率/参数层 `SiteRateModel`（Fintype 上的有限和，不引入测度论）
        ├── §2 `scale` / `ampScaled` / `Ã` / `f̃`
        ├── §3 器材：显式权 `wRef`、逐点正性、非负性
        ├── §4 ★★ 真定理：`f̃` 的**逐点正性** ＋ **a.e. 正性**（`propB_of_bridge` 要的形状）
        ├── §5 ★★ 真定理：`f̃` 的**带参数一致下界**（量化域被 `lmax` / `lx⁻` 限制，见下）
        ├── §6 ★★ 真定理：命题 A 三条恒等式在 `Ã` 下**保持** ⇒ `Ã` 版 `PropAData`
        ├── §7 ★ 识别等式（**定义性**，如实陈述）
        └── §8 ★ 反空洞 ＋ 退化一致性（`r ≡ 1, ρ ≡ 1` ⇒ 退回库内 `A` / `f`）
```

## ★ 哪一部分是「定义」、哪一部分是「真定理」（★D 诚实交代）

* **识别等式（§7）基本上是把定义展开**：`expWeight ν τd Ã r` 按库内定义
  （`CASTERBridge.lean:134`）就是 `∫ θ, ∑ T', τd θ T' · Ã θ T' r ∂ν`，而 `Ã` 是
  `∑ k, w k · A (scale θ k) T' r`；两者相等**不需要任何测度论**（速率层取**有限支撑**，
  见规格 §2.1 第 167 行「有限支撑即可」）—— 数学内容是 **`Ã` 的定义 ＋ 生成过程的联合律因子化**，
  **不是**一个新的概率恒等式。本文件把它当作「定义展开」如实陈述。
* **真定理部分是 §4 / §5 / §6**：`f̃` 的逐点与 a.e. 正性（§4）、`f̃` 的带参数一致下界（§5）、
  命题 A 三条恒等式在 `Ã` 下的保持与 `Ã` 版 `PropAData`（§6）。

## ⚠️ 诚实边界（不藏）

1. **一条为假的命题（协调侧 2026-10-12 校正，本文件据此改写）**：
   ✗ `∃ δ > 0, ∀ θ, δ ≤ f̃ θ`（**无限制量化域**）**是假的**。反例：
   取 `θ` 的内枝长 `Prod.snd (Prod.fst θ) = 0`（且 `Prod.snd θ = (false, false)` 使
   `¬ KingmanDeep θ`），则 `scale` 保持内枝长为 `0` ⇒ `1 − e 0 = 0` ⇒ `f (scale θ k) = 0`
   ⇒ `f̃ θ = 0`。这正是 `784775a` 那次事故的形态（`hf_pos` 只能写成 **ν-a.e.**）。
   ⇒ 本文件因此**只证**：(i) 逐点正性「内枝长 `> 0` ⇒ `f̃ θ > 0`」（§4）、
   (ii) a.e. 正性 `∀ᵐ θ ∂ν, 0 < f̃ θ`（§4）、
   (iii) **量化域被限制**的一致下界「`lx⁻ ≤ 内枝长`、叶长 `∈ [0, lmax]` ⇒ `deltaBox ≤ f̃ θ`」（§5）。
2. **枝长的坐标口径**：库内时间数据是 `(Fin 4 → ℝ) × ℝ` —— **基因树**的（按物种编号的）
   叶枝长 ＋ 内部枝长（见 `CASTERGeneTree.canonLen`：位置 `0,1,3,4` 是叶边、位置 `2` 是内边），
   在 `KingmanΘ = ((Fin 4 → ℝ) × ℝ) × (Bool × Bool)` 里就是那个 `(Fin 4 → ℝ) × ℝ` 分量。
   ⇒ `scale θ k` 就是**把逐枝速率乘到基因树自己的枝长上**，与规格 §5.1 第 281 行的口径
   `l·r·ρ`、`lx·r·ρ` 逐字一致。⚠️ **真正的粗一档之处**：`r k : Fin 4 → ℝ`、`rk k`、`ρ k`
   都是**常数乘子**，不是「物种树各枝独立抽速率」；深溯祖时物种树枝与基因树枝的对应会变，
   故这是**逐基因树逐枝常数速率**的简化口径（规格 §5.1 正是这么写的）。
3. **有限支撑**：速率层是 `Fintype Rate` 上的**有限和**，不引入测度论（规格 §2.1 第 167 行
   「有限支撑即可」）。一般分布的情形要把 `∑ k` 换成对 `w` 的积分，本文件**不做**
   （那一步带来可积性/可测性的额外工作，属 W13a 的 B2 / B3）。
4. **`π` / `κ` 只登记不使用**：JC69 实例不使用 `π`/`κ`（JC69 里 `π ≡ (1/4,1/4,1/4,1/4)`、
   无 `κ`，见规格 §1.3 表）。`pi` / `kappa` 字段按规格 §2.1 登记（含界与归一），
   以备 F84 / LM1 的 `Ã`（子批 W13h）直接吃；本文件对它们只证明登记性质。
5. **内枝速率 `rk`**：它只出现在 `ampScaled` 的**展示形态**里；`ampScaled` 与
   `jc69Amp (scale θ k)` **逐字相等**（`ampScaled_eq_jc69Amp`），故 `rk` 不影响本文件的
   JC69 结论。它按规格 §2.1 登记，供 W13h 的 F84 / LM1 用。
6. **`wRef`（显式权常数）**：§3 用 `Classical.choice` 从 `∑ w = 1` **证出**存在正权类别
   （`exists_pos_w`），再固定一个作为常数载体。这是**定理 ＋ 选择**，不是新假设；
   公理探针里出现的 `Classical.choice` 即来自此处（在容许的三公理之内）。
-/

set_option autoImplicit false

noncomputable section

namespace Phylo.Stat.SiteRateMixture

open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.MSCKingman
open MeasureTheory

/-! ## 1. 有限支撑的速率/参数层 -/

/-- **有限支撑的速率/参数层**（规格 §1.2 / §2.1 的逐字形式化）。

对每个 `k : Rate`（「第 k 类速率配置」）：

* `w k` —— 该类别的权重（`0 ≤ w`、`∑ w = 1`）；
* `r k : Fin 4 → ℝ` —— **逐叶**枝速率（乘到基因树的 4 条叶边上）；
* `rk k : ℝ` —— **内枝**速率（见文件头 §诚实边界 5）；
* `ρ k : ℝ` —— 位点速率倍率；
* 参数域：`∀ i, rL ≤ r k i ≤ rU`、`ρL ≤ ρ k ≤ ρU`、`rkL ≤ rk k ≤ rkU`，
  下界全部 `> 0`（规格 §4④「速率/倍率 a.e. 严格正且**一致有下界**」）；
* `pi k` 与 `kappa k` —— 老师第三次补充的 `π_j` / `κ_j`（F84 / LM1 用；界与归一登记在结构里）。

★ **反空洞**：结构不是空壳 —— 见 §8 `twoRate1`（`Rate = Fin 2`、`w = (1/2,1/2)`、
`r ≡ 1`、`ρ ≡ 1`、`rk ≡ 1`、`π ≡ 1/4`、`κ ≡ 0` 的**退化实例**）。 -/
structure SiteRateModel where
  /-- 速率/参数类别的指标集（**有限** ⇒ 一切都是有限和）。 -/
  Rate : Type
  /-- 有限性（有限支撑）。 -/
  instF : Fintype Rate
  /-- 类别权重 `w`。 -/
  w : Rate → ℝ
  /-- `w ≥ 0`。 -/
  w_nonneg : ∀ k, 0 ≤ w k
  /-- `∑ w = 1`。 -/
  w_sum : ∑ k, w k = 1
  /-- **逐叶**枝速率（乘到基因树 4 条叶边上）。 -/
  r : Rate → Fin 4 → ℝ
  /-- **内枝**速率（登记用，见文件头 §诚实边界 5）。 -/
  rk : Rate → ℝ
  /-- 位点速率倍率。 -/
  ρ : Rate → ℝ
  /-- 叶速率下界（严格 `> 0`）。 -/
  rL : ℝ
  /-- 叶速率上界。 -/
  rU : ℝ
  /-- 内枝速率下界（严格 `> 0`）。 -/
  rkL : ℝ
  /-- 内枝速率上界。 -/
  rkU : ℝ
  /-- 倍率下界（严格 `> 0`）。 -/
  ρL : ℝ
  /-- 倍率上界。 -/
  ρU : ℝ
  rL_pos : 0 < rL
  rL_le : ∀ k i, rL ≤ r k i
  r_le_rU : ∀ k i, r k i ≤ rU
  rkL_pos : 0 < rkL
  rkL_le : ∀ k, rkL ≤ rk k
  rk_le_rkU : ∀ k, rk k ≤ rkU
  ρL_pos : 0 < ρL
  ρL_le : ∀ k, ρL ≤ ρ k
  ρ_le_ρU : ∀ k, ρ k ≤ ρU
  /-- 碱基频率向量 `π_k`。 -/
  pi : Rate → Fin 4 → ℝ
  /-- `π` 正下界（规格 §4⑤）。 -/
  piL : ℝ
  /-- `π` 上界。 -/
  piU : ℝ
  piL_pos : 0 < piL
  piL_le : ∀ k i, piL ≤ pi k i
  pi_le_piU : ∀ k i, pi k i ≤ piU
  /-- `∑ i, π_k i = 1`。 -/
  pi_sum : ∀ k, ∑ i : Fin 4, pi k i = 1
  /-- 转换/颠换比 `κ_k`。 -/
  kappa : Rate → ℝ
  /-- `κ` 上界（规格 §4⑤）。 -/
  kU : ℝ
  kappa_nonneg : ∀ k, 0 ≤ kappa k
  kappa_le : ∀ k, kappa k ≤ kU

attribute [instance] SiteRateModel.instF

namespace SiteRateModel

/-! ### 1.1 `scale`：把枝长按 `(r k, ρ k)` 缩放 -/

/-- **缩放 `scale θ k`**：把 `θ` 的枝长按 `(r k, ρ k)` 缩放 ——
叶枝长 `l i ↦ r k i · ρ k · l i`、内枝长 `lx ↦ ρ k · lx`。

（`ρ k` 同时乘到叶边与内边上，因为位点倍率是**整体**的替换速率倍率；`r k i` 只乘对应叶边。
`θ` 的第二分量（`Bool × Bool`）**不变** ⇒ `KingmanDeep` 不变，见 `kingmanDeep_scale`。） -/
def scale (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) : KingmanΘ :=
  (((fun i : Fin 4 => M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i),
      M.ρ k * Prod.snd (Prod.fst θ)), Prod.snd θ)

/-- `scale` 的**叶长坐标展开**。 -/
theorem scale_fst_fst (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    Prod.fst (Prod.fst (M.scale θ k))
      = fun i : Fin 4 => M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i := rfl

/-- `scale` 的**内枝长坐标展开**。 -/
theorem scale_fst_snd (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    Prod.snd (Prod.fst (M.scale θ k)) = M.ρ k * Prod.snd (Prod.fst θ) := rfl

/-- ★ **`scale` 不改 `θ` 的第二分量**（`Prod.snd θ`，即两个 `Bool`）。 -/
theorem scale_snd (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    Prod.snd (M.scale θ k) = Prod.snd θ := rfl

/-- ★ **`scale` 逐叶展开**（叶 `i` 处的枝长）。 -/
theorem scale_leaf (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) (i : Fin 4) :
    Prod.fst (Prod.fst (M.scale θ k)) i = M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i := rfl

/-- ★ **`scale` 内枝展开**。 -/
theorem scale_int (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    Prod.snd (Prod.fst (M.scale θ k)) = M.ρ k * Prod.snd (Prod.fst θ) := rfl

/-- ★★ **`scale` 保持 `KingmanDeep`**（因为 `scale` 只动枝长、不动两个 `Bool`）。

⇒ 对 `kingmanMSCTopoSym`，「无深合并」这一条件在缩放后不变。 -/
theorem kingmanDeep_scale (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    KingmanDeep (M.scale θ k) ↔ KingmanDeep θ := by
  simp [KingmanDeep, scale]

/-- ★★ **`kingmanMSCTopoSym.deep` 在 `scale` 下不变**。 -/
theorem kingmanMSCTopoSym_deep_scale (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    kingmanMSCTopoSym.deep (M.scale θ k) ↔ kingmanMSCTopoSym.deep θ :=
  M.kingmanDeep_scale θ k

/-! ### 1.2 `ampScaled`：位点层速率下的幅度（JC69 形态） -/

/-- **位点层速率下的幅度（JC69 形态）**：
`(3/4)·∏_i e(r k i · ρ k · θ 的叶长 i)·(1 − e(ρ k · θ 的内枝长))`。

这与 `jc69Amp (M.scale θ k)` **逐字相等**（`ampScaled_eq_jc69Amp`），
只是写成不需要展开 `jc69Amp` 的形态。`π` / `κ` 不进入（JC69 的退化特例）。 -/
def ampScaled (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) : ℝ :=
  (3 / 4) * (∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i))
    * (1 - Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)))

/-- ★ **`ampScaled` 就是 `jc69Amp` 在缩放后的枝长上的取值**。 -/
theorem ampScaled_eq_jc69Amp (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    M.ampScaled θ k = jc69Amp (Prod.fst (Prod.fst (M.scale θ k)))
      (Prod.snd (Prod.fst (M.scale θ k))) := by
  simp [ampScaled, jc69Amp, scale]

/-- ★ **`A` 在 `scale θ k` 上的取值 = 该速率类别下的 `geneScore`**（`jc69PropAData` 的定义展开）。 -/
theorem A_scaled_eq_geneScore (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) (T' r : Topo) :
    jc69PropAData.A (Prod.fst (M.scale θ k)) T' r
      = geneScore T' (Prod.fst (Prod.fst (M.scale θ k)))
          (Prod.snd (Prod.fst (M.scale θ k))) r := rfl

/-- ★ **`f` 在 `scale θ k` 上的取值 = `ampScaled`**（`jc69PropAData` 的定义展开）。 -/
theorem f_scaled_eq_amp (M : SiteRateModel) (θ : KingmanΘ) (k : M.Rate) :
    jc69PropAData.f (Prod.fst (M.scale θ k)) = M.ampScaled θ k := by
  simp [jc69PropAData, ampScaled, jc69Amp, scale]

/-! ## 2. `Ã` 与 `f̃`（对速率类别的加权和） -/

/-- ★★★ **`Ã θ T' r := ∑ k, w k · A (scale θ k) T' r`** ——
速率异构下的条件期望幅度（有限支撑的 Laplace / 混合形态）。 -/
def Abar (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) : ℝ :=
  ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r

/-- ★★★ **`f̃ θ := ∑ k, w k · f (scale θ k)`**。 -/
def fbar (M : SiteRateModel) (θ : KingmanΘ) : ℝ :=
  ∑ k : M.Rate, M.w k * jc69PropAData.f (Prod.fst (M.scale θ k))

theorem Abar_apply (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) :
    M.Abar θ T' r = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r := rfl

theorem fbar_apply (M : SiteRateModel) (θ : KingmanΘ) :
    M.fbar θ = ∑ k : M.Rate, M.w k * jc69PropAData.f (Prod.fst (M.scale θ k)) := rfl

/-! ## 3. 器材：显式权常数、逐点正性与非负性 -/

/-- ★ **存在正权类别**：由 `∑ w = 1` 与 `w ≥ 0` 推出（若全 `≤ 0` 则 `∑ w ≤ 0 < 1`）。
★ 这是**定理**，不是结构的假设 —— `Rate` 的非空性也是它的推论。 -/
theorem exists_pos_w (M : SiteRateModel) : ∃ k : M.Rate, 0 < M.w k := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum : (∑ k : M.Rate, M.w k) ≤ 0 := Finset.sum_nonpos fun k _ => h k
  rw [M.w_sum] at hsum
  norm_num at hsum

/-- **固定的正权类别**（`Classical.choice`，其存在性由 `exists_pos_w` 保证）。 -/
noncomputable def kRef (M : SiteRateModel) : M.Rate := M.exists_pos_w.choose

/-- ★ **`kRef` 的权严格正**。 -/
theorem kRef_pos (M : SiteRateModel) : 0 < M.w M.kRef := by
  simpa only [kRef] using M.exists_pos_w.choose_spec

/-- ★ **显式权常数 `wRef := w kRef > 0`**（一致下界的常数载体）。 -/
noncomputable def wRef (M : SiteRateModel) : ℝ := M.w M.kRef

/-- ★ **`wRef > 0`**。 -/
theorem wRef_pos (M : SiteRateModel) : 0 < M.wRef := by
  simpa only [wRef] using M.kRef_pos

/-- ★ **`e` 单调递减**（`Phylo.JC.e x = exp(−(4/3)x)`）。 -/
theorem e_le_e_of_le {x y : ℝ} (h : x ≤ y) : Phylo.JC.e y ≤ Phylo.JC.e x := by
  simp only [Phylo.JC.e]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- ★ **`e` 严格递减**。 -/
theorem e_lt_e_of_lt {x y : ℝ} (h : x < y) : Phylo.JC.e y < Phylo.JC.e x := by
  simp only [Phylo.JC.e]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- ★ **`x > 0 ⇒ e x < 1`**。 -/
theorem e_lt_one_of_pos {x : ℝ} (h : 0 < x) : Phylo.JC.e x < 1 := by
  rw [Phylo.JC.e, Real.exp_lt_one_iff]
  nlinarith

/-- ★ **`x ≥ 0 ⇒ e x ≤ 1`**。 -/
theorem e_le_one_of_nonneg {x : ℝ} (h : 0 ≤ x) : Phylo.JC.e x ≤ 1 := by
  rw [Phylo.JC.e, Real.exp_le_one_iff]
  nlinarith

/-- ★ **四因子乘积的单调性**（`Fin 4` 上的乘积，展开成四个因子后逐对相乘）。

（不用 `Finset.prod_le_prod`：本文件把它换成显式四因子版本，减少对库 API 形状的依赖。） -/
theorem prod_four_le {a b : Fin 4 → ℝ} (ha : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ b i) :
    (∏ i : Fin 4, a i) ≤ ∏ i : Fin 4, b i := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have ha2 := ha 2
  have ha3 := ha 3
  have hb0 : 0 ≤ b 0 := le_trans (ha 0) h0
  have hb1 : 0 ≤ b 1 := le_trans (ha 1) h1
  have hb2 : 0 ≤ b 2 := le_trans ha2 h2
  have h01 : a 0 * a 1 ≤ b 0 * b 1 := mul_le_mul h0 h1 (ha 1) hb0
  have h012 : a 0 * a 1 * a 2 ≤ b 0 * b 1 * b 2 :=
    mul_le_mul h01 h2 ha2 (mul_nonneg hb0 hb1)
  have h0123 : a 0 * a 1 * a 2 * a 3 ≤ b 0 * b 1 * b 2 * b 3 :=
    mul_le_mul h012 h3 ha3 (mul_nonneg (mul_nonneg hb0 hb1) hb2)
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  exact h0123

/-- ★ **`ρ k · θ 的内枝长 > 0`**（由内枝长 `> 0` 与 `ρL > 0`）。 -/
theorem rho_mul_int_pos (M : SiteRateModel) (θ : KingmanΘ)
    (h : 0 < Prod.snd (Prod.fst θ)) (k : M.Rate) :
    0 < M.ρ k * Prod.snd (Prod.fst θ) :=
  mul_pos (lt_of_lt_of_le M.ρL_pos (M.ρL_le k)) h

/-- ★★ **`ampScaled` 逐点严格正**（只需内枝长 `> 0` —— 这是本文件对「一致正」的
**诚实起点**：内枝长 `= 0` 时 `ampScaled = 0`，见文件头 §诚实边界 1）。 -/
theorem ampScaled_pos (M : SiteRateModel) (θ : KingmanΘ)
    (h : 0 < Prod.snd (Prod.fst θ)) (k : M.Rate) : 0 < M.ampScaled θ k := by
  have hpos : 0 < M.ρ k * Prod.snd (Prod.fst θ) := M.rho_mul_int_pos θ h k
  have hprod1 : (0 : ℝ) < ∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i) :=
    Finset.prod_pos fun i _ => Real.exp_pos _
  have h2 : Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) < 1 := e_lt_one_of_pos hpos
  have h3 : (0 : ℝ) < 1 - Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) := by linarith
  have h4 : (0 : ℝ) < 3 / 4 := by norm_num
  exact mul_pos (mul_pos h4 hprod1) h3

/-- ★★ **`ampScaled` 非负**（需内枝长 `≥ 0`）。 -/
theorem ampScaled_nonneg (M : SiteRateModel) (θ : KingmanΘ)
    (h : 0 ≤ Prod.snd (Prod.fst θ)) (k : M.Rate) : 0 ≤ M.ampScaled θ k := by
  have hx : 0 ≤ M.ρ k * Prod.snd (Prod.fst θ) :=
    mul_nonneg (le_trans M.ρL_pos.le (M.ρL_le k)) h
  have h2 : Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) ≤ 1 := e_le_one_of_nonneg hx
  have h3 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have h4 : (0 : ℝ) ≤ ∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have h5 : (0 : ℝ) ≤ 1 - Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) := by linarith
  exact mul_nonneg (mul_nonneg h3 h4) h5

/-- ★★★ **`wRef · ampScaled θ kRef ≤ f̃ θ`**（本文件对「显式常数下界」的**逐点**形态：
取固定的正权类别 `kRef`，单项就不超过整个加权和）。 -/
theorem wRef_mul_ampScaled_le_fbar (M : SiteRateModel) (θ : KingmanΘ)
    (h : 0 ≤ Prod.snd (Prod.fst θ)) : M.wRef * M.ampScaled θ M.kRef ≤ M.fbar θ := by
  have hfbar : M.fbar θ = ∑ k : M.Rate, M.w k * M.ampScaled θ k := by
    simp only [fbar, f_scaled_eq_amp]
  rw [hfbar, wRef]
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (M.w_nonneg j) (M.ampScaled_nonneg θ h j)) (Finset.mem_univ M.kRef)

/-! ## 4. ★★ 真定理：`f̃` 的逐点正性与 a.e. 正性 -/

/-- ★★★ **`f̃ θ > 0`（逐点，内枝长 `> 0`）**。 -/
theorem fbar_pos (M : SiteRateModel) (θ : KingmanΘ) (h : 0 < Prod.snd (Prod.fst θ)) :
    0 < M.fbar θ := by
  have h1 := M.wRef_mul_ampScaled_le_fbar θ h.le
  have h2 : 0 < M.wRef * M.ampScaled θ M.kRef := mul_pos M.wRef_pos (M.ampScaled_pos θ h M.kRef)
  linarith

/-- ★★★ **`f̃ > 0`，ν-**几乎处处**（★ 这才是 `propB_of_bridge` 要的形状：
`CASTERTopo.lean:252` 的 `hf_pos : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < P.f θ`）。

假设 `∀ᵐ θ ∂ν, 0 < θ 的内枝长`（等价于「内枝长 `= 0` 是零测事件」）。 -/
theorem fbar_pos_ae (M : SiteRateModel) (ν : Measure KingmanΘ)
    (hν : ∀ᵐ θ ∂ν, 0 < Prod.snd (Prod.fst θ)) : ∀ᵐ θ ∂ν, 0 < M.fbar θ :=
  hν.mono fun θ hθ => M.fbar_pos θ hθ

/-- ★★★ **`propB_of_bridge` 直接要的 a.e. 形状**：`∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < f̃ θ`
（`S` 的 `deep` 在假言前件里，故由 `fbar_pos_ae` 直接给出）。 -/
theorem fbar_pos_ae_not_deep (M : SiteRateModel) (S : MSCTopoSym KingmanΘ)
    (ν : Measure KingmanΘ) (hν : ∀ᵐ θ ∂ν, 0 < Prod.snd (Prod.fst θ)) :
    ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < M.fbar θ :=
  (M.fbar_pos_ae ν hν).mono fun _ h => fun _ => h

/-! ## 5. ★★ 真定理：`f̃` 的**带参数一致下界**（量化域被 `lmax` / `lx⁻` 限制）

⚠️ **无限制量化域的一致下界是假的**（文件头 §诚实边界 1）。本节给出**诚实形态**：
把量化域限制到**箱体** `叶长 i ∈ [0, lmax]`、`内枝长 ≥ lx⁻ > 0` 上，
`f̃` 有**只依赖 `(lmax, lx⁻)` 与模型常数**的正下界。 -/

/-- ★ **箱体幅度下界**：

`ampBox M lmax lx⁻ := (3/4) · ∏_i e(rU · ρU · lmax) · (1 − e(ρL · lx⁻))`。

（`∏_i e(rU ρU lmax)` 是叶长部分在箱体上的**最小**因子；`1 − e(ρL lx⁻)` 是内枝部分的最小因子。） -/
def ampBox (M : SiteRateModel) (lmax lx0 : ℝ) : ℝ :=
  (3 / 4) * (∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax))
    * (1 - Phylo.JC.e (M.ρL * lx0))

/-- ★★ **箱体一致下界常数** `deltaBox M lmax lx⁻ := wRef · ampBox M lmax lx⁻`。
（`wRef = w kRef > 0` 是固定的正权，见 §3。） -/
noncomputable def deltaBox (M : SiteRateModel) (lmax lx0 : ℝ) : ℝ := M.wRef * M.ampBox lmax lx0

/-- ★ **`ampBox ≥ 0`**（需 `lx⁻ ≥ 0`）。 -/
theorem ampBox_nonneg (M : SiteRateModel) {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) :
    0 ≤ M.ampBox lmax lx0 := by
  have hx : 0 ≤ M.ρL * lx0 := mul_nonneg M.ρL_pos.le hlx0
  have h1 : Phylo.JC.e (M.ρL * lx0) ≤ 1 := e_le_one_of_nonneg hx
  have h2 : (0 : ℝ) ≤ ∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have h3 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have h4 : (0 : ℝ) ≤ 1 - Phylo.JC.e (M.ρL * lx0) := by linarith
  simp only [ampBox]
  exact mul_nonneg (mul_nonneg h3 h2) h4

/-- ★★★ **箱体常数严格正**（`lx⁻ > 0`）。 -/
theorem deltaBox_pos (M : SiteRateModel) {lmax lx0 : ℝ} (hlx : 0 < lx0) :
    0 < M.deltaBox lmax lx0 := by
  have hx : 0 < M.ρL * lx0 := mul_pos M.ρL_pos hlx
  have h1 : (0 : ℝ) < 1 - Phylo.JC.e (M.ρL * lx0) := by
    have := e_lt_one_of_pos hx
    linarith
  have h2 : (0 : ℝ) < ∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax) :=
    Finset.prod_pos fun _ _ => Real.exp_pos _
  have h3 : (0 : ℝ) < 3 / 4 := by norm_num
  simp only [deltaBox, ampBox]
  exact mul_pos M.wRef_pos (mul_pos (mul_pos h3 h2) h1)

/-- ★★★ **单个速率类别的箱体下界**：在箱体上 `ampBox ≤ ampScaled θ k`。 -/
theorem ampBox_le_ampScaled (M : SiteRateModel) (θ : KingmanΘ) {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) (hleaf : ∀ i, 0 ≤ Prod.fst (Prod.fst θ) i)
    (hleafmax : ∀ i, Prod.fst (Prod.fst θ) i ≤ lmax)
    (hint : lx0 ≤ Prod.snd (Prod.fst θ)) (k : M.Rate) :
    M.ampBox lmax lx0 ≤ M.ampScaled θ k := by
  have hrU : 0 ≤ M.rU := le_trans (le_trans M.rL_pos.le (M.rL_le k 0)) (M.r_le_rU k 0)
  have hρU : 0 ≤ M.ρU := le_trans (le_trans M.ρL_pos.le (M.ρL_le k)) (M.ρ_le_ρU k)
  -- 叶长部分：逐叶 `e(上限) ≤ e(当前)`
  have hfac : ∀ i : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax)
      ≤ Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i) := by
    intro i
    refine e_le_e_of_le ?_
    have hri : M.r k i ≤ M.rU := M.r_le_rU k i
    have hρi : M.ρ k ≤ M.ρU := M.ρ_le_ρU k
    have hr0 : 0 ≤ M.r k i := le_trans M.rL_pos.le (M.rL_le k i)
    have hρ0 : 0 ≤ M.ρ k := le_trans M.ρL_pos.le (M.ρL_le k)
    have hl0 : 0 ≤ Prod.fst (Prod.fst θ) i := hleaf i
    have h1 : M.r k i * M.ρ k ≤ M.rU * M.ρU := mul_le_mul hri hρi hρ0 (le_trans hr0 hri)
    exact mul_le_mul h1 (hleafmax i) hl0 (mul_nonneg hrU hρU)
  have hprod : (∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax))
      ≤ ∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i) :=
    prod_four_le (fun i => (Real.exp_pos _).le) hfac
  -- 内枝部分
  have hintle : M.ρL * lx0 ≤ M.ρ k * Prod.snd (Prod.fst θ) :=
    mul_le_mul (M.ρL_le k) hint hlx0 (le_trans M.ρL_pos.le (M.ρL_le k))
  have hintfac : Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) ≤ Phylo.JC.e (M.ρL * lx0) :=
    e_le_e_of_le hintle
  have hinner : 1 - Phylo.JC.e (M.ρL * lx0)
      ≤ 1 - Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ)) := by linarith
  have h3 : (0 : ℝ) < 3 / 4 := by norm_num
  have hA : 0 ≤ (3 / 4 : ℝ) * (∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax)) :=
    mul_nonneg h3.le (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have hC : 0 ≤ 1 - Phylo.JC.e (M.ρL * lx0) := by
    have h1 : Phylo.JC.e (M.ρL * lx0) ≤ 1 :=
      e_le_one_of_nonneg (mul_nonneg M.ρL_pos.le hlx0)
    linarith
  have hB : 0 ≤ (3 / 4 : ℝ)
      * (∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i)) :=
    mul_nonneg h3.le (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have key : (3 / 4) * (∏ _ : Fin 4, Phylo.JC.e (M.rU * M.ρU * lmax))
        * (1 - Phylo.JC.e (M.ρL * lx0))
      ≤ (3 / 4) * (∏ i : Fin 4, Phylo.JC.e (M.r k i * M.ρ k * Prod.fst (Prod.fst θ) i))
        * (1 - Phylo.JC.e (M.ρ k * Prod.snd (Prod.fst θ))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hprod h3.le) hinner hC hB
  simpa only [ampBox, ampScaled] using key

/-- ★★★ **`f̃` 的带参数一致下界（本批的诚实形态）**：

在**箱体** `∀ i, 0 ≤ 叶长 i ≤ lmax`、`lx⁻ ≤ 内枝长`（且 `lmax ≥ 0`、`lx⁻ ≥ 0`）上，

```
deltaBox M lmax lx⁻  ≤  f̃ θ        （deltaBox > 0 需 lx⁻ > 0，见 `deltaBox_pos`）
```

⚠️ **量化域被 `lmax` / `lx⁻` 限制** —— 这正是「无限制一致下界为假」的诚实修法
（文件头 §诚实边界 1：内枝长 `→ 0` 时 `f̃ → 0`；叶长 `→ ∞` 时 `∏ e(叶长) → 0`）。 -/
theorem deltaBox_le_fbar (M : SiteRateModel) (θ : KingmanΘ) {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) (hleaf : ∀ i, 0 ≤ Prod.fst (Prod.fst θ) i)
    (hleafmax : ∀ i, Prod.fst (Prod.fst θ) i ≤ lmax)
    (hint : lx0 ≤ Prod.snd (Prod.fst θ)) : M.deltaBox lmax lx0 ≤ M.fbar θ := by
  have h1 : M.ampBox lmax lx0 ≤ M.ampScaled θ M.kRef :=
    M.ampBox_le_ampScaled θ hlx0 hleaf hleafmax hint M.kRef
  have h2 : M.deltaBox lmax lx0 ≤ M.wRef * M.ampScaled θ M.kRef := by
    simp only [deltaBox]
    exact mul_le_mul_of_nonneg_left h1 M.wRef_pos.le
  have h3 : M.wRef * M.ampScaled θ M.kRef ≤ M.fbar θ :=
    M.wRef_mul_ampScaled_le_fbar θ (le_trans hlx0 hint)
  exact le_trans h2 h3

/-! ## 6. ★★ 真定理：命题 A 的三条恒等式在 `Ã` 下保持 ＋ `Ã` 版 `PropAData` -/

/-- ★★ **`Ã − f̃ = ∑ w · (A − f)`**（三条保持恒等式的公共引擎；纯有限和线性性）。 -/
theorem Abar_sub_fbar (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) :
    M.Abar θ T' r - M.fbar θ
      = ∑ k : M.Rate, M.w k * (jc69PropAData.A (Prod.fst (M.scale θ k)) T' r
          - jc69PropAData.f (Prod.fst (M.scale θ k))) := by
  simp only [Abar, fbar, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- ★★ **子句 `ab|cd` 的保持**（规格 §5.3）。 -/
theorem Abar_clause_ab (M : SiteRateModel) (θ : KingmanΘ) (T' : Topo) (h : T' = .ab_cd) :
    M.Abar θ T' .ab_cd - M.fbar θ = M.Abar θ T' .ac_bd ∧
      M.Abar θ T' .ab_cd - M.fbar θ = M.Abar θ T' .ad_bc := by
  have h1 : M.Abar θ T' .ab_cd - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ac_bd := by
    rw [M.Abar_sub_fbar θ T' .ab_cd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ab (Prod.fst (M.scale θ k)) T' h).1]
  have h2 : M.Abar θ T' .ab_cd - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ad_bc := by
    rw [M.Abar_sub_fbar θ T' .ab_cd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ab (Prod.fst (M.scale θ k)) T' h).2]
  exact ⟨by rw [h1, Abar], by rw [h2, Abar]⟩

/-- ★★ **子句 `ac|bd` 的保持**（规格 §5.3）。 -/
theorem Abar_clause_ac (M : SiteRateModel) (θ : KingmanΘ) (T' : Topo) (h : T' = .ac_bd) :
    M.Abar θ T' .ac_bd - M.fbar θ = M.Abar θ T' .ab_cd ∧
      M.Abar θ T' .ac_bd - M.fbar θ = M.Abar θ T' .ad_bc := by
  have h1 : M.Abar θ T' .ac_bd - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ab_cd := by
    rw [M.Abar_sub_fbar θ T' .ac_bd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ac (Prod.fst (M.scale θ k)) T' h).1]
  have h2 : M.Abar θ T' .ac_bd - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ad_bc := by
    rw [M.Abar_sub_fbar θ T' .ac_bd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ac (Prod.fst (M.scale θ k)) T' h).2]
  exact ⟨by rw [h1, Abar], by rw [h2, Abar]⟩

/-- ★★ **子句 `ad|bc` 的保持**（规格 §5.3）。 -/
theorem Abar_clause_ad (M : SiteRateModel) (θ : KingmanΘ) (T' : Topo) (h : T' = .ad_bc) :
    M.Abar θ T' .ad_bc - M.fbar θ = M.Abar θ T' .ab_cd ∧
      M.Abar θ T' .ad_bc - M.fbar θ = M.Abar θ T' .ac_bd := by
  have h1 : M.Abar θ T' .ad_bc - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ab_cd := by
    rw [M.Abar_sub_fbar θ T' .ad_bc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ad (Prod.fst (M.scale θ k)) T' h).1]
  have h2 : M.Abar θ T' .ad_bc - M.fbar θ
      = ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' .ac_bd := by
    rw [M.Abar_sub_fbar θ T' .ad_bc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(jc69PropAData.clause_ad (Prod.fst (M.scale θ k)) T' h).2]
  exact ⟨by rw [h1, Abar], by rw [h2, Abar]⟩

/-- ★★★ **`Ã` 版 `PropAData`**（规格 §5.2：**不新增 `TopoIdeal` 定义**，
只把 `P.A` 换成 `Ã`、`P.f` 换成 `f̃`，供 `CASTERTopo.ofModel` / `ofFamily` /
`propB_of_bridge` 直接吃）。 -/
noncomputable def abarPropAData (M : SiteRateModel) : PropAData KingmanΘ where
  A := M.Abar
  f := M.fbar
  clause_ab := fun θ T' h => M.Abar_clause_ab θ T' h
  clause_ac := fun θ T' h => M.Abar_clause_ac θ T' h
  clause_ad := fun θ T' h => M.Abar_clause_ad θ T' h

@[simp] theorem abarPropAData_A (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) :
    M.abarPropAData.A θ T' r = M.Abar θ T' r := rfl

@[simp] theorem abarPropAData_f (M : SiteRateModel) (θ : KingmanΘ) :
    M.abarPropAData.f θ = M.fbar θ := rfl

/-- ★★ **`Ã` 版命题 A 的符号形式**：`Ã θ T' .ab_cd − Ã θ T' .ac_bd = sign T' · f̃ θ`
（`CASTERTopo` 的 `propB_of_bridge` 直接吃这一条）。 -/
theorem abarPropAData_delta (M : SiteRateModel) (θ : KingmanΘ) (T' : Topo) :
    M.Abar θ T' .ab_cd - M.Abar θ T' .ac_bd = sign T' * M.fbar θ := by
  simpa only [abarPropAData_A, abarPropAData_f] using PropAData.delta M.abarPropAData θ T'

/-! ## 7. ★ 识别等式（**这一步是定义性的**，如实陈述） -/

/-- **速率类别的单位点条件期望**：`∑ k, w k · A (scale θ k) T' r`
（与 `Abar` **定义相同** —— 单独命名只为把「生成过程的那一步」显式写出来）。 -/
def rateExpect (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) : ℝ :=
  ∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r

theorem rateExpect_eq_Abar (M : SiteRateModel) (θ : KingmanΘ) (T' r : Topo) :
    M.rateExpect θ T' r = M.Abar θ T' r := rfl

/-- **完整生成过程的单位点权重期望**（★ 显式对象）：

```
siteWeightExpect ν τd M r
  = ∫ θ, ∑_{T'} τd θ T' · ( ∑_k w k · A (scale θ k) T' r ) ∂ν
```

即「`θ ~ ν` → `T' ~ τd θ` → `k ~ w` → 位点由 `(scale θ k, T')` 生成」四步中
**前三步**的期望（速率类别那一步是有限和，不需要测度）。 -/
noncomputable def siteWeightExpect (M : SiteRateModel) (ν : Measure KingmanΘ)
    (τd : KingmanΘ → Topo → ℝ) (r : Topo) : ℝ :=
  ∫ θ, (∑ T' : Topo,
    τd θ T' * (∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r)) ∂ν

/-- ★ **识别等式的「内层」形态**：对每个 `θ`，内层和就是 `∑ T', τd θ T' · Ã θ T' r`。 -/
theorem siteWeightExpect_integrand (M : SiteRateModel) (τd : KingmanΘ → Topo → ℝ)
    (θ : KingmanΘ) (r : Topo) :
    (∑ T' : Topo, τd θ T' * (∑ k : M.Rate,
        M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r))
      = ∑ T' : Topo, τd θ T' * M.Abar θ T' r :=
  Finset.sum_congr rfl fun T' _ => by rw [Abar]

/-- ★★★ **识别等式**：完整生成过程的位点层期望权重 = 库内 `expWeight ν τd Ã r`。

```
∫ θ, ∑_{T'} τd θ T' · (∑_k w k · A (scale θ k) T' r) ∂ν  =  expWeight ν τd Ã r
```

⚠️ **诚实交代（★D）**：**这一步是定义性的，不是非平凡定理**。
右端的 `expWeight ν τd Ã r` 按库内定义（`CASTERBridge.lean:134`）**就是**
`∫ θ, ∑ T', τd θ T' · Ã θ T' r ∂ν`；而 `Ã θ T' r` 按本文件定义就是
`∑ k, w k · A (scale θ k) T' r`。⇒ 数学内容是

* **`Ã` 的定义**（对速率类别取加权和 —— 速率层取**有限支撑**，这里是**有限和**）；
* **生成过程的联合律因子化**：位点权重关于 `(θ, T', k)` 的条件期望分别是 `w k`
  （速率类别独立于 `θ, T'`，规格 §1.2 的三步独立性）与 `A (scale θ k) T' r`
  （给定 `(θ, T', k)` 的模型命题 A）；
* **有限和与积分相容**（这里连交换都不需要：`expWeight` 的被积函数**逐点相等**于左端
  被积函数，故由 `integral_congr_ae` 直接得到）。

⇒ 本定理**不需要任何可积性假设**（`integral_congr_ae` 只用逐点相等），这本身也说明它
没有测度论的实质内容。真正非平凡的部分是 §4 的 **a.e. 正性**、§5 的**带参数一致下界**、
§6 的**保持 ＋ `Ã` 版 `PropAData`**、以及 §8 的**退化一致性**。 -/
theorem siteWeightExpect_eq_expWeight (M : SiteRateModel) (ν : Measure KingmanΘ)
    (τd : KingmanΘ → Topo → ℝ) (r : Topo) :
    M.siteWeightExpect ν τd r = expWeight ν τd M.Abar r := by
  unfold siteWeightExpect expWeight geneExpect
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact M.siteWeightExpect_integrand τd θ r

/-! ## 8. ★ 反空洞 ＋ 退化一致性（规格 §8④） -/

/-- **退化实例 `twoRate1`**：`Rate = Fin 2`、`w = (1/2, 1/2)`、`r ≡ 1`、`rk ≡ 1`、
`ρ ≡ 1`、`π ≡ 1/4`、`κ ≡ 0`，界全部取 `1`（`π` 的界取 `1/4`）。

★ 这既是反空洞**见证**（`SiteRateModel` 非空），也是规格 §8④ 的
**退化一致性检查**的载体：此时 `scale θ k = θ`（逐字），故 `Ã = A`、`f̃ = f`。 -/
def twoRate1 : SiteRateModel where
  Rate := Fin 2
  instF := inferInstance
  w := fun _ => 1 / 2
  w_nonneg := fun _ => by norm_num
  w_sum := by
    rw [Fin.sum_univ_two]
    norm_num
  r := fun _ _ => 1
  rk := fun _ => 1
  ρ := fun _ => 1
  rL := 1
  rU := 1
  rkL := 1
  rkU := 1
  ρL := 1
  ρU := 1
  rL_pos := one_pos
  rL_le := fun _ _ => le_refl 1
  r_le_rU := fun _ _ => le_refl 1
  rkL_pos := one_pos
  rkL_le := fun _ => le_refl 1
  rk_le_rkU := fun _ => le_refl 1
  ρL_pos := one_pos
  ρL_le := fun _ => le_refl 1
  ρ_le_ρU := fun _ => le_refl 1
  pi := fun _ _ => 1 / 4
  piL := 1 / 4
  piU := 1 / 4
  piL_pos := by norm_num
  piL_le := fun _ _ => le_refl _
  pi_le_piU := fun _ _ => le_refl _
  pi_sum := by
    intro _
    rw [Fin.sum_univ_four]
    norm_num
  kappa := fun _ => 0
  kU := 0
  kappa_nonneg := fun _ => le_refl 0
  kappa_le := fun _ => le_refl 0

/-- ★★ **反空洞见证**：`SiteRateModel` 非空（具体实例，不是空壳）。 -/
theorem siteRateModel_nonempty : Nonempty SiteRateModel := ⟨twoRate1⟩

/-- ★★ **退化一致性（`scale` 部分）**：`twoRate1` 下 `scale θ k = θ` **逐字**。 -/
theorem twoRate1_scale (θ : KingmanΘ) (k : Fin 2) : twoRate1.scale θ k = θ := by
  refine Prod.ext ?_ ?_
  · refine Prod.ext ?_ ?_
    · funext i
      simp [SiteRateModel.scale, twoRate1]
    · simp [SiteRateModel.scale, twoRate1]
  · simp [SiteRateModel.scale, twoRate1]

/-- **JC69 的 `A` 沿 `Prod.fst` 搬到 `KingmanΘ`**（退化一致性陈述用；与
`Phylo.Stat.MSCInstance.jc69PropADataK` 的 `A` 字段同物，此处就地定义以免多一个 import）。 -/
noncomputable def jc69A : KingmanΘ → Topo → Topo → ℝ :=
  fun θ T' r => jc69PropAData.A (Prod.fst θ) T' r

/-- ★★ **退化一致性（`Ã` 部分）**：`r ≡ 1, ρ ≡ 1` 时 `Ã` **逐字退回**库内原 `A`，
即 `twoRate1.Abar θ T' r = jc69PropAData.A (Prod.fst θ) T' r`（对任意 `θ, T', r`）。 -/
theorem twoRate1_Abar (θ : KingmanΘ) (T' r : Topo) :
    twoRate1.Abar θ T' r = jc69PropAData.A (Prod.fst θ) T' r := by
  have hsum : twoRate1.Abar θ T' r
      = ∑ _k : Fin 2, (1 / 2 : ℝ) * jc69PropAData.A (Prod.fst θ) T' r := by
    simp only [SiteRateModel.Abar]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [twoRate1_scale θ k]
    rfl
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- ★★ **退化一致性（`f̃` 部分）**：`r ≡ 1, ρ ≡ 1` 时 `f̃` **逐字退回**库内原 `f`。 -/
theorem twoRate1_fbar (θ : KingmanΘ) : twoRate1.fbar θ = jc69PropAData.f (Prod.fst θ) := by
  have hsum : twoRate1.fbar θ
      = ∑ _k : Fin 2, (1 / 2 : ℝ) * jc69PropAData.f (Prod.fst θ) := by
    simp only [SiteRateModel.fbar]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [twoRate1_scale θ k]
    rfl
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- ★★ **退化一致性（`PropAData` 部分）**：`Ã` 版 `PropAData` 的两个数据字段与原版一致。 -/
theorem twoRate1_abarPropAData_A (θ : KingmanΘ) (T' r : Topo) :
    twoRate1.abarPropAData.A θ T' r = jc69PropAData.A (Prod.fst θ) T' r :=
  twoRate1_Abar θ T' r

theorem twoRate1_abarPropAData_f (θ : KingmanΘ) :
    twoRate1.abarPropAData.f θ = jc69PropAData.f (Prod.fst θ) :=
  twoRate1_fbar θ

/-- ★★ **退化一致性（识别等式部分）**：`r ≡ 1, ρ ≡ 1` 时识别等式退回**库内无速率层的
`expWeight`**（右端的 `A` 是 `jc69PropAData.A` 沿 `Prod.fst` 搬到 `KingmanΘ`，即 `jc69A`）。 -/
theorem twoRate1_siteWeightExpect (ν : Measure KingmanΘ) (τd : KingmanΘ → Topo → ℝ)
    (r : Topo) :
    twoRate1.siteWeightExpect ν τd r = expWeight ν τd jc69A r := by
  rw [twoRate1.siteWeightExpect_eq_expWeight]
  unfold expWeight geneExpect jc69A
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact Finset.sum_congr rfl fun T' _ => by simp only [twoRate1_Abar]

/-- ★★ **退化一致性（逐点正性部分）**：`twoRate1` 下内枝长 `> 0` ⇒ `f̃ θ > 0`，
与库内 `jc69Amp_pos`（需内枝长 `> 0`）一致。 -/
theorem twoRate1_fbar_pos (θ : KingmanΘ) (h : 0 < Prod.snd (Prod.fst θ)) : 0 < twoRate1.fbar θ :=
  twoRate1.fbar_pos θ h

/-- ★★ **退化一致性（带参数一致下界部分）**：`twoRate1` 下箱体常数
`deltaBox 1 1` 满足 `deltaBox 1 1 ≤ f̃ θ`（在叶长 `∈ [0,1]`、内枝长 `≥ 1` 的箱体上）。 -/
theorem twoRate1_deltaBox_le_fbar (θ : KingmanΘ)
    (hleaf : ∀ i, 0 ≤ Prod.fst (Prod.fst θ) i)
    (hleafmax : ∀ i, Prod.fst (Prod.fst θ) i ≤ 1)
    (hint : 1 ≤ Prod.snd (Prod.fst θ)) : twoRate1.deltaBox 1 1 ≤ twoRate1.fbar θ :=
  twoRate1.deltaBox_le_fbar θ (by norm_num) hleaf hleafmax hint

end SiteRateModel

end Phylo.Stat.SiteRateMixture
