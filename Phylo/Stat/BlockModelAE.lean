/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERRateAE
import Phylo.Stat.BlockSLLNTopoClose
import Phylo.Stat.SiteWeightMeasurable

/-!
# `Phylo.Stat.BlockModelAE` —— **块概率空间**：把桥的假设实例化（W13k）

## 1. 本文件在整条链里的位置

W13 的验收目标是「**不假设 `hconv`** 的端到端定理」。到本文件之前链上已有三件：

* `Phylo/Stat/BlockSLLN.lean`（`BlockSLLN` / `BlockSLLNIdx`）：**块级强大数定律**（纯概率层）；
* `Phylo/Stat/BlockSLLNTopoClose.lean`（`empWeight_tendsto_ae`）：块级 SLLN ⇒ **`TopoClose` 形态**的
  a.e. 收敛 —— 但它把 **5 条块层假设**（`hjoint`/`hident`/`hL1`/`hintM`/`hintL`）
  ＋ **识别等式 `hlim`** ＋ **`hrep`** 当参数挂着；
* `Phylo/Stat/CASTERRateAE.lean`（`abar_caster_statisticallyConsistent_kingman_ae`）：
  CASTER 侧端到端，假设面**只剩 `hconv` 与 `hE`**。

⇒ **本文件把 5 条块层假设 ＋ `hlim` 全部实例化**（在一个**真正构造出来的**概率空间上），
于是 `hconv` **不再是假设**；`hrep` 由**经验表的定义**直接给出（§3 与 §8 交代）。

## 2. 模型与空间（规格 §1.2 的最小可用版本）

一个**块**＝「一棵基因树 ＋ 它的全部位点」：

| 分量 | 含义 | 说明 |
|---|---|---|
| `v : ℝ × ℝ` | 溯祖等待时间数据 | 与 `kingmanMSCMeasure` 的**源空间**同口径（`kingmanMSCMeasure_dirac_eq_map`） |
| `L : ℕ` | 位点数，**`1 ≤ L ≤ C`** | 规格 §4③ 的双向界；`C` 为显式常数 |
| `κ : Fin C → M.Rate` | 逐位点速率类别 | 边缘 `rateMeasure M`（模型给的有限混合 `∑ w_k δ_k`） |

块概率空间取**无穷乘积测度** `blockSample = Measure.infinitePi (fun _ : ℕ => blockMeasure)`：

* `blockMeasure = ((ν_v × ν_L) × ν_κ)` 经 `Block.ofRaw` **推前**，其中 `ν_v = sojournLaw 2 ⊗ sojournLaw 2`、
  `ν_κ = Measure.pi (fun _ : Fin C => rateMeasure M)`（坐标 iid）；
* 坐标 iid 与边缘律**都是定理**（`iIndepFun_infinitePi` / `Measure.infinitePi_map_eval`）。

★ **块坐标为什么用 `v` 而不是任意 `KingmanΘ`**：`toKingmanΘ ((leaf,a,b), v)` 的枝长恒为
「叶长 `= leaf`、内枝长 `= a + b`」。于是只要 `hleaf : ∀ i, 0 ≤ leaf i` 与 `hab : 0 < a + b`，
**块空间上枝长处处非负** ⇒ W13a 的 `abs_geneScore_le_one`（**必须有非负前提**，见该文件 §3）
**处处可用** ⇒ 块总权重**处处有界** ⇒ `hintM`/`hintL` 与 Fubini 所需的 `Integrable`
**全部是定理**，不需要任何 `a.e.` 搬运。

## 3. 识别等式 `hlim` —— 用有限和绕开 Wald 恒等式（规格 §3.2）

因为 `L ∈ [1, C]`（**有限支撑**）且 `κ` 坐标同分布，对任意 `ω`：

```
blockW b = ∑_{i ∈ Fin C} [i < L] · siteW b i ,   siteW b i = ∑_{T'} τd θ T' · A(scale θ (κ i)) T' T
```

先对 `κ` 逐坐标积分（`MeasureTheory.integral_comp_eval` ＋ `integral_rateMeasure`，**纯有限和**），
再对 `(v, L)` 用 `MeasureTheory.integral_prod_mul`（**无额外假设**）⇒

```
∫ blockW  =  (∫ l, (l:ℝ) ∂ν_L) · expWeight ν_θ kingmanMSCTopoSym.τd M.Abar T
∫ blockL  =  (∫ l, (l:ℝ) ∂ν_L)
```

分母 `> 0`（`L ≥ 1`）⇒ **`(∫ blockW)/(∫ blockL) = expWeight ν_θ τd Ã T`** ——
**不需要任何 Wald 恒等式 / 条件期望机器**。

## 4. 诚实边界（逐条，不藏）

1. **`hconv` 消掉了** ✓：端到端定理 `abar_caster_statisticallyConsistent_kingman_ae_blocks`
   的假设面**不含 `hconv`**（逐字见其签名）。
2. **`hrep` 是【定义】**（★D 交代）：`BlockSLLNTopoClose.empWeight_tendsto_ae` 的 `hrep` 形如
   `emp n ω S hS T = (∑_{j<n} M_j)/(∑_{j<n} L_j)`，其中 **`n` 是基因树棵数** ⇒ 本文件把经验表
   **定义为**「前 `n` 棵树的块级平均」（`empOfBlocks`），于是 `hrep` 是 `rfl`。
   另有 `empOfBlocks_eq_sum_fin`：该定义**逐字**等于「块内逐位点求和」的变长形态 —
   即「经验表 = 块级平均」在**语义上**是定理，不只是命名。
3. **`hleaf : ∀ i, 0 ≤ leaf i` 是新增的模型条件**（物种树叶长非负）。它**不是**装饰：
   W13a 的 `abs_geneScore_le_one` **必须有非负枝长**（负枝长时 `|patternProb|` 可达 `3.5e4`）。
   库内旗舰端点 `abarTopoIdeal_kingman` 不带它，是因为那条路走 `a.e.` 正性而非**一致**有界。
4. **规格 §3.3 的换指标（W13j）本文件【不需要】**：`empWeight_tendsto_ae` 的 `hrep` 以
   **基因树棵数** `n` 编号（不是位点序号），故「经验表 = 块级平均」在块口径下是**定义**。
   W13j（`Phylo/Stat/BlockSLLNIndex.lean`，`prefixAvg_tendsto_of_blockAvg_tendsto`）解决的是
   **位点序号口径**下的换指标；把它接上需要「逐位点权重**对一切 `ω`** 的一致界 `hw`」，
   而本文件的一般块空间上 `θ` 的枝长只在 a.e. 意义下非负（`v`-像上恒非负，但 `Block` 类型
   的元素可任意），故 `hw` 的**全局**形态不成立 —— 这条**如实登记为未接**（见 §11）。
5. **块的空间口径**：树侧数据是溯祖等待时间 `v`（配合**固定物种树** `(leaf, a, b)`），
   与 `abarTopoIdeal_kingman`（`ν = kingmanMSCMeasure (dirac (leaf,a,b))`）逐字对应 ——
   故识别等式右端**就是**库内 `W̃`，无需改写。
6. **`π` / `κ`（老师第三次补充）**：本文件走 **JC69 端**（`π ≡ 1/4`、无 `κ`）；
   `SiteRateModel` 的 `pi`/`kappa` 登记但**不使用**（与 `SiteRateMixture`/`CASTERRateAE` 口径一致）。
7. **`hE` 仍是假设** —— 它是**算法性质**（经验得分被 `E n ω` 最大化），属 CASTER 引擎侧。
8. **反空洞**：`Block` 有具体居民（`block_nonempty`）；`rateMeasure` 是概率测度（实例已证）；
   `SiteRateModel` 由库内 `twoRate1` 居留；`LIdx`/`QuartetKey` 非空。
9. **`L ≤ C` 用了三处**：① 块空间的定义域（`LIdx`）；② 变长求和的**可测性**（固定长度 ＋ 指示函数）；
   ③ 计数引理 `sum_ite_lt_card`（`∑_{i<C} [i<L]·c = L·c`）。W13j 实测它有**反例**（无界时结论为假）
   ⇒ 本文件把它当**模型条件**而非装饰。
10. **无未完成证明 / 无公理**：全部声明正面构造；`#print axioms` 只应出现
    `[propext, Classical.choice, Quot.sound]`。
11. ★★ **「物种树写进【类型】」的代价**（W16a 于 2026-10-12 实测定位；**值得后人知道** ✓）：
    本文件的 `Block M C leaf a b` 把物种树 `(leaf, a, b)` 编进**类型** —— 这在**固定环境**下很省事
    （上面的 `hleaf` / `hab` 因此**处处**满足 ✓），但它**排除了「环境本身随机」的推广** ✗：
    要让物种树随机，就需要 `Measurable (bb ↦ Block M C bb.sp.1 bb.sp.2.1 bb.sp.2.2)` 这类**依赖族** ✗，
    而 Lean 4 的 `Measurable f` **要求余定义域是固定类型** ⇒ **连陈述的 elaboration 都过不去** ✗
    （报错原文：`Application type mismatch: … has type (p : …) → Block M C p.1.1 p.1.2.1 p.1.2.2
    but is expected to have type ?m.1 → ?m.2 in the application Measurable …` ✓）；
    `rw` / `convert` / `Measurable.of_comap_le` / `Sigma` 打包**四条路全部撞同一面墙** ✗
    （`Sigma` 只是把依赖**换个地方**陈述 ✓）。
    ★★ **出路**：**在块数据上【原生重定义】权重** ✓（把 `siteW` 写成乘积空间上的**非依赖**函数 ✓，
    再照本文件的老路逐条重证 ✓），**不要**对固定环境的 `blockW` 做依赖复合 ✗。
    ⇒ 完整记录见 `_scripts_tmp/W16a_BLOCKER.md`（项目外留痕）（142 行：确切 error 原文 · 四条路各自失败点 ·
    已验证的出路公式 ✓）。
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Phylo.Stat.BlockModelAE

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.MSCKingman (KingmanΘ kingmanMSCTopoSym)
open Phylo.Stat.MSCKingmanMeasure
open Phylo.Stat.MSCInstance (jc69PropADataK)
open Phylo.Stat.SiteRateMixture
open Phylo.Stat.CASTERRateAE
open Phylo.Stat.SiteWeightMeasurable
open Phylo.Stat.KingmanCoalescent
open Phylo.Stat.CASTERBridge
open Phylo.Stat.BlockSLLNTopoClose

/-! ## 0. 速率类别上的有限混合测度（模型给的 `w` 的载体） -/

/-- `M.Rate` 上的**离散可测结构**（有限类型 ⇒ 所有集合可测）。 -/
instance instMeasurableSpaceRate (M : SiteRateModel) : MeasurableSpace M.Rate := ⊤

instance instDiscreteMeasurableSpaceRate (M : SiteRateModel) : DiscreteMeasurableSpace M.Rate where
  forall_measurableSet := fun _ => by
    change MeasurableSet (id (α := Set M.Rate) _)
    simp [MeasurableSpace.measurableSet_top]

/-- ★ **有限类型上的函数都可测**（`M.Rate` 取离散可测结构）。 -/
theorem measurable_of_rate (M : SiteRateModel) {β : Type*} [MeasurableSpace β]
    (f : M.Rate → β) : Measurable f :=
  fun _ _ => MeasurableSet.of_discrete

/-- ★ **位点速率类别上的有限混合测度** `∑_k w_k · δ_k`。 -/
noncomputable def rateMeasure (M : SiteRateModel) : Measure M.Rate :=
  ∑ k : M.Rate, ENNReal.ofReal (M.w k) • Measure.dirac k

instance instIsProbabilityMeasureRateMeasure (M : SiteRateModel) :
    IsProbabilityMeasure (rateMeasure M) where
  measure_univ := by
    rw [rateMeasure, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ _),
      Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => M.w_nonneg k), M.w_sum, ENNReal.ofReal_one]

/-- ★★ **有限和积分公式**：`∫ h ∂(rateMeasure M) = ∑_k w_k · h k`（**纯有限和**）。 -/
theorem integral_rateMeasure (M : SiteRateModel) (h : M.Rate → ℝ) :
    ∫ j, h j ∂(rateMeasure M) = ∑ k : M.Rate, M.w k * h k := by
  rw [rateMeasure, MeasureTheory.integral_finsetSum_measure (s := Finset.univ)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (M.w_nonneg k), smul_eq_mul]
  · intro k _
    exact (integrable_dirac (a := k) (by simp)).smul_measure (by simp)

/-- 逐位点速率类别的**乘积测度**（坐标 iid，边缘 `rateMeasure M`）。 -/
noncomputable abbrev ratePi (M : SiteRateModel) (C : ℕ) : Measure (Fin C → M.Rate) :=
  Measure.pi fun _ : Fin C => rateMeasure M

instance instIsProbabilityMeasureRatePi (M : SiteRateModel) (C : ℕ) :
    IsProbabilityMeasure (ratePi M C) := by
  rw [ratePi]
  infer_instance

/-! ## 1. 块：一棵基因树 ＋ 它的全部位点 -/

/-- 位点数的取值域 `[1, C]`。 -/
abbrev LIdx (C : ℕ) : Type := {L : ℕ // 1 ≤ L ∧ L ≤ C}

/-- ★★ **块**＝「一棵基因树 ＋ 它的全部位点」（规格 §1.2 的最小可用版本）。

★ 反空洞：`block_nonempty` 给出具体居民。 -/
structure Block (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) where
  /-- 溯祖等待时间数据。 -/
  v : ℝ × ℝ
  /-- 位点数。 -/
  L : ℕ
  /-- `1 ≤ L`（每棵树至少一个位点）。 -/
  hL1 : 1 ≤ L
  /-- `L ≤ C`（规格 §4③ 的块长上界）。 -/
  hLC : L ≤ C
  /-- 逐位点速率类别。 -/
  κ : Fin C → M.Rate

variable {M : SiteRateModel} {C : ℕ} {leaf : Fin 4 → ℝ} {a b : ℝ≥0}
variable {νL : Measure (LIdx C)} [IsProbabilityMeasure νL]

namespace Block

/-- 块的**树侧数据**：`θ = toKingmanΘ ((leaf, a, b), v)`（枝长恒为 `leaf` 与 `a + b`）。 -/
def θOf (bb : Block M C leaf a b) : KingmanΘ := toKingmanΘ ((leaf, a, b), bb.v)

/-- 块到「生空间」（三块乘积空间）的投影。 -/
def toRaw (bb : Block M C leaf a b) : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate) :=
  ((bb.v, ⟨bb.L, bb.hL1, bb.hLC⟩), bb.κ)

/-- 生空间到块的构造。 -/
def ofRaw (p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) : Block M C leaf a b :=
  ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2⟩

end Block

theorem Block.toRaw_ofRaw (p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) :
    Block.toRaw (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b) p) = p := by
  obtain ⟨⟨v, ⟨L, h1, h2⟩⟩, k⟩ := p
  rfl

instance instMeasurableSpaceBlock (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    MeasurableSpace (Block M C leaf a b) :=
  MeasurableSpace.comap (Block.toRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b))
    inferInstance

theorem measurable_toRaw :
    Measurable (Block.toRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) :=
  Measurable.of_comap_le le_rfl

theorem measurable_ofRaw :
    Measurable (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) := by
  refine Measurable.of_comap_le ?_
  rw [instMeasurableSpaceBlock]
  rw [MeasurableSpace.comap_comp,
    show (Block.toRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) ∘
        (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) = id from
      funext fun p => Block.toRaw_ofRaw p,
    MeasurableSpace.comap_id]

/-- ★★ **反空洞**：块非空（`v = (0,0)`、`L = 1`、速率类别取库内的正权类别 `kRef`）。 -/
theorem block_nonempty (hC : 1 ≤ C) : Nonempty (Block M C leaf a b) :=
  ⟨{ v := (0, 0), L := 1, hL1 := le_rfl, hLC := hC, κ := fun _ => M.kRef }⟩

/-! ## 2. 块测度与块样本空间 -/

instance instIsProbabilityMeasureSojournLawTwo : IsProbabilityMeasure (sojournLaw 2) :=
  isProbabilityMeasure_sojournLaw (by norm_num)

/-- 块测度：`((ν_v × ν_L) × ν_κ)` 经 `Block.ofRaw` 推前。 -/
noncomputable def blockMeasure (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (νL : Measure (LIdx C)) : Measure (Block M C leaf a b) :=
  ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)).map
    (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b))

instance instIsProbabilityMeasureBlockMeasure (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ)
    (a b : ℝ≥0) (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    IsProbabilityMeasure (blockMeasure M C leaf a b νL) where
  measure_univ := by
    rw [blockMeasure, Measure.map_apply measurable_ofRaw MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ

/-- ★★★ **块样本空间**：`ℕ → Block` 上的**无穷乘积测度**（块 iid）。 -/
noncomputable abbrev blockSample (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (νL : Measure (LIdx C)) : Measure (ℕ → Block M C leaf a b) :=
  Measure.infinitePi fun _ : ℕ => blockMeasure M C leaf a b νL

instance instIsProbabilityMeasureBlockSample (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ)
    (a b : ℝ≥0) (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    IsProbabilityMeasure (blockSample M C leaf a b νL) := by
  rw [blockSample]
  infer_instance

/-- ★★ 坐标 `i` 的**边缘律**（`Measure.infinitePi_map_eval`）。 -/
theorem blockSample_map_eval (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (i : ℕ) :
    (blockSample M C leaf a b νL).map (fun ω : ℕ → Block M C leaf a b => ω i)
      = blockMeasure M C leaf a b νL :=
  Measure.infinitePi_map_eval (fun _ : ℕ => blockMeasure M C leaf a b νL) i

/-! ## 3. 单位点权重、块总权重、经验表 -/

/-- **单个位点的权重**（对拓扑 `T`）：`∑_{T'} τd θ T' · A (scale θ (κ i)) T' T`。 -/
noncomputable def siteW (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T : Topo)
    (bb : Block M C leaf a b) (i : Fin C) : ℝ :=
  ∑ T' : Topo, kingmanMSCTopoSym.τd (Block.θOf bb) T' *
    jc69PropAData.A (Prod.fst (M.scale (Block.θOf bb) (bb.κ i))) T' T

/-- ★★ **块总权重**：`∑_{i < L} siteW i`，写成 `Fin C` 上的**固定长度**和 ＋ 指示函数
（`L ≤ C` 由此成为**可测性**的条件，见文件头 §9）。 -/
noncomputable def blockW (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T : Topo)
    (bb : Block M C leaf a b) : ℝ :=
  ∑ i : Fin C, if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0

/-- **块位点数**（当作 `ℝ`）。 -/
def blockL (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (bb : Block M C leaf a b) : ℝ :=
  (bb.L : ℝ)

/-- **块位点数的 `ℕ` 值形态**（可测性的载体）。 -/
def blockLnat (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (bb : Block M C leaf a b) : ℕ :=
  bb.L

/-- ★ **经验表**（前 `n` 棵树）：**定义**为块级平均。它就是
`BlockSLLNTopoClose.empWeight_tendsto_ae` 的 `hrep` 所规定的形状（见文件头 §4.2）。 -/
noncomputable def empOfBlocks (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (n : ℕ) (ω : ℕ → Block M C leaf a b) : TopoWeight (Fin 4) :=
  fun _ _ T => (∑ j ∈ Finset.range n, blockW M C leaf a b T (ω j)) /
    (∑ j ∈ Finset.range n, blockL M C leaf a b (ω j))

/-- ★ **语义桥**：块总权重**逐字**等于「块内 `L` 个位点（在 `Fin C` 中的前 `L` 个）的求和」。 -/
theorem blockW_eq_sum_filter (T : Topo) (bb : Block M C leaf a b) :
    blockW M C leaf a b T bb
      = ∑ i ∈ Finset.univ.filter (fun i : Fin C => (i : ℕ) < bb.L),
          siteW M C leaf a b T bb i := by
  rw [blockW, ← Finset.sum_filter]

/-! ## 4. 可测性 -/

theorem measurable_blockLnat :
    Measurable (blockLnat (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) := by
  have h : blockLnat (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      = fun bb => (((Block.toRaw bb).1.2 : LIdx C) : ℕ) := rfl
  rw [h]
  exact measurable_subtype_coe.comp (measurable_toRaw (M := M) (C := C) (leaf := leaf)
    (a := a) (b := b)).fst.snd

theorem measurable_blockL :
    Measurable (blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b)) := by
  have h : blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      = fun bb => (((blockLnat M C leaf a b bb : ℕ)) : ℝ) := rfl
  rw [h]
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_blockLnat

theorem measurable_LIdx_val :
    Measurable fun l : LIdx C => (((l : ℕ)) : ℝ) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_subtype_coe

/-- ★★ **`Ã` 的单位项关于块可测**（`scale` 坐标展开 ＋ W13a 的 `measurable_geneScore`）。 -/
theorem measurable_scaleFst (i : Fin C) :
    Measurable fun bb : Block M C leaf a b =>
      Prod.fst (M.scale (Block.θOf bb) (bb.κ i)) := by
  have hκ : Measurable fun bb : Block M C leaf a b => bb.κ i :=
    (measurable_pi_apply i).comp
      (measurable_toRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)).snd
  have hρ : Measurable fun bb : Block M C leaf a b => M.ρ (bb.κ i) :=
    (measurable_of_rate M (fun j : M.Rate => M.ρ j)).comp hκ
  have hrmj : ∀ j : Fin 4, Measurable fun bb : Block M C leaf a b => M.r (bb.κ i) j :=
    fun j => (measurable_of_rate M (fun jj : M.Rate => M.r jj j)).comp hκ
  have hcomp1 : Measurable fun bb : Block M C leaf a b =>
      fun j : Fin 4 => M.r (bb.κ i) j * M.ρ (bb.κ i) * leaf j := by
    rw [measurable_pi_iff]
    intro j
    exact ((hrmj j).mul hρ).mul (measurable_const (a := leaf j))
  have hpair : Measurable fun bb : Block M C leaf a b =>
      ((fun j : Fin 4 => M.r (bb.κ i) j * M.ρ (bb.κ i) * leaf j),
        M.ρ (bb.κ i) * ((a : ℝ) + (b : ℝ))) :=
    Measurable.prod hcomp1 (hρ.mul (measurable_const (a := (a : ℝ) + (b : ℝ))))
  convert hpair using 1
  funext bb
  simp only [SiteRateModel.scale]
  rfl

theorem measurable_siteW (T : Topo) (i : Fin C) :
    Measurable fun bb : Block M C leaf a b => siteW M C leaf a b T bb i := by
  refine Finset.measurable_sum Finset.univ fun T' _ => ?_
  have hv : Measurable fun bb : Block M C leaf a b => bb.v :=
    (measurable_toRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)).fst.fst
  have hτ : Measurable fun bb : Block M C leaf a b => kingmanMSCTopoSym.τd (Block.θOf bb) T' := by
    have hθ : Block.θOf (M := M) (C := C) (leaf := leaf) (a := a) (b := b) =
        fun bb : Block M C leaf a b => toKingmanΘ ((leaf, a, b), bb.v) := rfl
    rw [hθ]
    exact (measurable_Kingmanτd T').comp (measurable_toKingmanΘ.comp
      (measurable_const.prodMk hv))
  have hA : Measurable fun bb : Block M C leaf a b =>
      jc69PropAData.A (Prod.fst (M.scale (Block.θOf bb) (bb.κ i))) T' T :=
    (measurable_geneScore T' T).comp (measurable_scaleFst (M := M) (C := C) (leaf := leaf)
      (a := a) (b := b) (i := i))
  exact hτ.mul hA

/-! ## 5. 一致界：块权重落在 `[-C, C]` 内 -/

theorem measurable_blockW (T : Topo) :
    Measurable fun bb : Block M C leaf a b => blockW M C leaf a b T bb := by
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  exact Measurable.ite
    (measurableSet_lt (f := fun _ : Block M C leaf a b => (i : ℕ)) measurable_const
      (measurable_blockLnat (M := M) (C := C) (leaf := leaf) (a := a) (b := b)))
    (measurable_siteW (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T i)
    measurable_const

/-- ★★ **`τd`-加权单位项有界**（`≤ 1`）：只需 `θ` 的枝长非负 —— 这是 W13a
`abs_geneScore_le_one` 的**必需**前提（负枝长时无界）。 -/
theorem abs_tauA_le_one {θ : KingmanΘ} (hl : ∀ i, 0 ≤ (θ).1.1 i) (hlx : 0 ≤ (θ).1.2)
    (T : Topo) (j : M.Rate) :
    |∑ T' : Topo, kingmanMSCTopoSym.τd θ T' *
        jc69PropAData.A (Prod.fst (M.scale θ j)) T' T| ≤ 1 := by
  have hlen : ∀ i : Fin 4, 0 ≤ (M.scale θ j).1.1 i := by
    intro i
    have hr : 0 ≤ M.r j i := le_trans M.rL_pos.le (M.rL_le j i)
    have hρ : 0 ≤ M.ρ j := le_trans M.ρL_pos.le (M.ρL_le j)
    simpa only [SiteRateModel.scale] using mul_nonneg (mul_nonneg hr hρ) (hl i)
  have hlenx : 0 ≤ (M.scale θ j).1.2 := by
    have hρ : 0 ≤ M.ρ j := le_trans M.ρL_pos.le (M.ρL_le j)
    simpa only [SiteRateModel.scale] using mul_nonneg hρ hlx
  have h2 : ∀ T' : Topo, |kingmanMSCTopoSym.τd θ T' *
        jc69PropAData.A (Prod.fst (M.scale θ j)) T' T| ≤ kingmanMSCTopoSym.τd θ T' := by
    intro T'
    rw [abs_mul, abs_of_nonneg (kingmanMSCTopoSym.τd_nonneg θ T')]
    calc kingmanMSCTopoSym.τd θ T' *
          |jc69PropAData.A (Prod.fst (M.scale θ j)) T' T|
        ≤ kingmanMSCTopoSym.τd θ T' * 1 :=
          mul_le_mul_of_nonneg_left (abs_geneScore_le_one T' T _ _ hlen hlenx)
            (kingmanMSCTopoSym.τd_nonneg θ T')
      _ = kingmanMSCTopoSym.τd θ T' := mul_one _
  calc |∑ T' : Topo, kingmanMSCTopoSym.τd θ T' *
        jc69PropAData.A (Prod.fst (M.scale θ j)) T' T|
      ≤ ∑ T' : Topo, |kingmanMSCTopoSym.τd θ T' *
          jc69PropAData.A (Prod.fst (M.scale θ j)) T' T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' := Finset.sum_le_sum fun T' _ => h2 T'
    _ = 1 := kingmanMSCTopoSym.τd_sum θ

theorem θOf_fst_fst (bb : Block M C leaf a b) : (Block.θOf bb).1.1 = leaf := rfl

theorem θOf_fst_snd (bb : Block M C leaf a b) : (Block.θOf bb).1.2 = (a : ℝ) + (b : ℝ) := rfl

theorem abs_siteW_le_one (hleaf : ∀ i, 0 ≤ leaf i)
    (T : Topo) (bb : Block M C leaf a b) (i : Fin C) :
    |siteW M C leaf a b T bb i| ≤ 1 := by
  have hl : ∀ j : Fin 4, 0 ≤ (Block.θOf bb).1.1 j := by
    intro j
    rw [θOf_fst_fst]
    exact hleaf j
  have hlx : 0 ≤ (Block.θOf bb).1.2 := by
    rw [θOf_fst_snd]
    exact add_nonneg a.2 b.2
  exact abs_tauA_le_one (M := M) hl hlx T (bb.κ i)

theorem abs_blockW_le (hleaf : ∀ i, 0 ≤ leaf i)
    (T : Topo) (bb : Block M C leaf a b) :
    |blockW M C leaf a b T bb| ≤ (C : ℝ) := by
  have h1 : |blockW M C leaf a b T bb|
      ≤ ∑ i : Fin C, |if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0| := by
    rw [blockW]
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i : Fin C,
      |if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0| ≤ (1 : ℝ) := by
    intro i
    by_cases h : (i : ℕ) < bb.L
    · have heq : (if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0)
          = siteW M C leaf a b T bb i := by simp [h]
      rw [heq]
      exact abs_siteW_le_one hleaf T bb i
    · have heq : (if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0) = 0 := by simp [h]
      rw [heq, abs_zero]
      norm_num
  calc |blockW M C leaf a b T bb|
      ≤ ∑ i : Fin C, |if (i : ℕ) < bb.L then siteW M C leaf a b T bb i else 0| := h1
    _ ≤ ∑ _i : Fin C, (1 : ℝ) := Finset.sum_le_sum fun i _ => h2 i
    _ = (C : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## 6. 识别等式（`hlim`）：用有限和绕开 Wald 恒等式 -/

/-- ★ 有限和交换：`∑_{T'} τd T' · Ã T' T = ∑_j w_j · (∑_{T'} τd T' · A_j T')`。 -/
theorem sum_tau_mul_Abar (θ : KingmanΘ) (T : Topo) :
    (∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T)
      = ∑ j : M.Rate, M.w j * (∑ T' : Topo, kingmanMSCTopoSym.τd θ T' *
          jc69PropAData.A (Prod.fst (M.scale θ j)) T' T) := by
  simp only [SiteRateModel.Abar, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun T' _ => ?_
  ring

/-- ★★ **逐位点权重的 `τd` 加权和**（识别等式的被积函数）。 -/
noncomputable def kappaMean (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T : Topo)
    (v : ℝ × ℝ) : ℝ :=
  ∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
    M.Abar (toKingmanΘ ((leaf, a, b), v)) T' T

/-- ★★ **计数引理**：`∑_{i < C} [i < N] · c = N · c`（`N ≤ C`）。`L ≤ C` 在这里是**必需**的
（W13j 实测：无界时前缀平均在 `0` 与 `1/3` 之间振荡 ⇒ 结论为假）。 -/
theorem sum_ite_lt_card {N Cn : ℕ} (h : N ≤ Cn) (c : ℝ) :
    (∑ i : Fin Cn, if (i : ℕ) < N then c else 0) = (N : ℝ) * c := by
  classical
  rw [← Finset.sum_range (fun j : ℕ => if j < N then c else 0)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range Cn).filter fun i => i < N) = Finset.range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun hh => hh.2
    · intro hh
      exact ⟨lt_of_lt_of_le hh h, hh⟩
  rw [hcard, Finset.card_range]

instance instIsProbabilityMeasureSojournLawTwoProd :
    IsProbabilityMeasure ((sojournLaw 2).prod (sojournLaw 2)) := inferInstance

/-- ★★ **对 `κ` 逐坐标积分**（**纯有限和**）：`∫_κ blockW = L · kappaMean`。

`L ≤ C` 的作用有两处：① `blockW` 是**固定长度**和（可测性）；② 计数引理 `sum_ite_lt_card`。 -/
theorem integral_kappa_blockW (hleaf : ∀ i, 0 ≤ leaf i)
    (T : Topo) (v : ℝ × ℝ) (l : LIdx C) :
    ∫ k : Fin C → M.Rate,
        blockW M C leaf a b T (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
          ((v, l), k)) ∂(ratePi M C)
      = ((l : ℕ) : ℝ) * kappaMean M leaf a b T v := by
  classical
  have hl : ∀ i : Fin 4, 0 ≤ (toKingmanΘ ((leaf, a, b), v)).1.1 i := by
    intro i
    rw [show (toKingmanΘ ((leaf, a, b), v)).1.1 = leaf from rfl]
    exact hleaf i
  have hlx : 0 ≤ (toKingmanΘ ((leaf, a, b), v)).1.2 := by
    rw [show (toKingmanΘ ((leaf, a, b), v)).1.2 = (a : ℝ) + (b : ℝ) from rfl]
    exact add_nonneg a.2 b.2
  have hbd : ∀ j : M.Rate,
      |∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
        jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) j)) T' T| ≤ 1 :=
    fun j => abs_tauA_le_one (M := M) hl hlx T j
  have hpt : (fun k : Fin C → M.Rate =>
        blockW M C leaf a b T (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
          ((v, l), k)))
      = fun k => ∑ i : Fin C, if (i : ℕ) < l.1 then
          (∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T)
          else 0 := rfl
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum (Finset.univ)]
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (sum_ite_lt_card l.2.2 (kappaMean M leaf a b T v))
    by_cases hi : (i : ℕ) < l.1
    · have hR : (if (i : ℕ) < l.1 then kappaMean M leaf a b T v else 0)
          = kappaMean M leaf a b T v := by simp [hi]
      have hif : (fun k : Fin C → M.Rate => (if (i : ℕ) < l.1 then
          (∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T)
          else 0))
        = fun k : Fin C → M.Rate => ∑ T' : Topo,
            kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T := by
        funext k
        simp [hi]
      rw [hR, hif, MeasureTheory.integral_comp_eval (μ := fun _ : Fin C => rateMeasure M)
        (f := fun j : M.Rate => ∑ T' : Topo,
          kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
          jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) j)) T' T)
        ((measurable_of_rate M _).aestronglyMeasurable)]
      rw [integral_rateMeasure]
      exact (sum_tau_mul_Abar (M := M) (θ := toKingmanΘ ((leaf, a, b), v)) T).symm
    · have hR : (if (i : ℕ) < l.1 then kappaMean M leaf a b T v else 0) = 0 := by simp [hi]
      have hif : (fun k : Fin C → M.Rate => (if (i : ℕ) < l.1 then
          (∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T)
          else 0)) = fun _ : Fin C → M.Rate => (0 : ℝ) := by
        funext k
        simp [hi]
      rw [hR, hif, integral_zero]
  · intro i _
    by_cases hi : (i : ℕ) < l.1
    · have hif : (fun k : Fin C → M.Rate => (if (i : ℕ) < l.1 then
          (∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T)
          else 0))
        = fun k : Fin C → M.Rate => ∑ T' : Topo,
            kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T := by
        funext k
        simp [hi]
      rw [hif]
      exact MeasureTheory.integrable_comp_eval (μ := fun _ : Fin C => rateMeasure M)
        (integrable_of_abs_bound (measurable_of_rate M _).aestronglyMeasurable (C := 1)
          (Eventually.of_forall fun j => hbd j))
    · have hif : (fun k : Fin C → M.Rate => (if (i : ℕ) < l.1 then
          (∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ ((leaf, a, b), v)) T' *
            jc69PropAData.A (Prod.fst (M.scale (toKingmanΘ ((leaf, a, b), v)) (k i))) T' T)
          else 0)) = fun _ : Fin C → M.Rate => (0 : ℝ) := by
        funext k
        simp [hi]
      rw [hif]
      exact integrable_of_abs_bound (measurable_const (a := (0 : ℝ))).aestronglyMeasurable
        (C := 0) (Eventually.of_forall fun _ => by simp)

/-- ★★★ **识别等式的 `θ`-侧**：`∫_v kappaMean = expWeight ν_θ τd Ã T`
（`ν_θ = kingmanMSCMeasure (dirac (leaf, a, b))` = `ν_v` 的推前，故由 `integral_map` 得到）。 -/
theorem integral_kappaMean (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T : Topo) :
    ∫ v : ℝ × ℝ, kappaMean M leaf a b T v ∂((sojournLaw 2).prod (sojournLaw 2))
      = expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T := by
  have hg : Measurable fun v : ℝ × ℝ => toKingmanΘ ((leaf, a, b), v) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  rw [kingmanMSCMeasure_dirac_eq_map (leaf, a, b)]
  rw [expWeight, Phylo.Stat.CASTEREngine.geneExpect]
  rw [integral_map hg.aemeasurable (measurable_abarHint M T).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun _ => rfl)

/-- ★★★ **识别等式（`blockW` 侧）**：`∫ blockW = 𝔼[L] · expWeight ν_θ τd Ã T`。 -/
theorem blockW_integral (hleaf : ∀ i, 0 ≤ leaf i) (T : Topo) :
    ∫ bb, blockW M C leaf a b T bb ∂(blockMeasure M C leaf a b νL)
      = (∫ l, ((l : ℕ) : ℝ) ∂νL) * expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T := by
  have hmap : (∫ bb, blockW M C leaf a b T bb ∂(blockMeasure M C leaf a b νL))
      = ∫ p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
          blockW M C leaf a b T (Block.ofRaw p) ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod
            (ratePi M C)) := by
    rw [blockMeasure]
    exact integral_map measurable_ofRaw.aemeasurable
      (measurable_blockW (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T).aestronglyMeasurable
  rw [hmap]
  have hInt : Integrable (fun p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate) =>
      blockW M C leaf a b T (Block.ofRaw p))
      ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)) :=
    integrable_of_abs_bound ((measurable_blockW (M := M) (C := C) (leaf := leaf) (a := a)
        (b := b) T).comp measurable_ofRaw).aestronglyMeasurable (C := (C : ℝ))
      (Eventually.of_forall fun p =>
        abs_blockW_le (M := M) (C := C) (leaf := leaf) (a := a) (b := b) hleaf T
          (Block.ofRaw p))
  rw [MeasureTheory.integral_prod _ hInt]
  rw [show (∫ x : (ℝ × ℝ) × LIdx C, (∫ k : Fin C → M.Rate,
        blockW M C leaf a b T (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
          (x, k)) ∂(ratePi M C)) ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL)))
      = ∫ x : (ℝ × ℝ) × LIdx C,
          kappaMean M leaf a b T x.1 * ((x.2 : ℕ) : ℝ)
          ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL)) from
    integral_congr_ae (Eventually.of_forall fun x =>
      (integral_kappa_blockW (M := M) (C := C) (leaf := leaf) (a := a) (b := b) hleaf T
        x.1 x.2).trans (mul_comm _ _))]
  rw [MeasureTheory.integral_prod_mul (μ := ((sojournLaw 2).prod (sojournLaw 2))) (ν := νL)
    (f := fun v : ℝ × ℝ => kappaMean M leaf a b T v) (g := fun l : LIdx C => ((l : ℕ) : ℝ))]
  rw [integral_kappaMean]
  exact mul_comm _ _

omit [IsProbabilityMeasure νL] in
/-- ★★★ **识别等式（`blockL` 侧）**：`∫ blockL = 𝔼[L]`。 -/
theorem blockL_integral :
    ∫ bb, blockL M C leaf a b bb ∂(blockMeasure M C leaf a b νL)
      = ∫ l, ((l : ℕ) : ℝ) ∂νL := by
  have hmap : (∫ bb, blockL M C leaf a b bb ∂(blockMeasure M C leaf a b νL))
      = ∫ p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
          blockL M C leaf a b (Block.ofRaw p) ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod
            (ratePi M C)) := by
    rw [blockMeasure]
    exact integral_map measurable_ofRaw.aemeasurable
      (measurable_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b)).aestronglyMeasurable
  rw [hmap]
  have hstep : (∫ p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
        blockL M C leaf a b (Block.ofRaw p)
        ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
      = ∫ p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
          (((p.1.2 : LIdx C) : ℕ) : ℝ)
          ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)) :=
    integral_congr_ae (Eventually.of_forall fun _ => rfl)
  rw [hstep]
  have hfst : (∫ p : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
        (((p.1.2 : LIdx C) : ℕ) : ℝ)
        ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
      = (ratePi M C).real Set.univ • ∫ x : (ℝ × ℝ) × LIdx C, (((x.2 : LIdx C) : ℕ) : ℝ)
          ∂(((sojournLaw 2).prod (sojournLaw 2)).prod νL) :=
    MeasureTheory.integral_fun_fst (μ := (((sojournLaw 2).prod (sojournLaw 2)).prod νL))
      (ν := ratePi M C) (f := fun x : (ℝ × ℝ) × LIdx C => (((x.2 : LIdx C) : ℕ) : ℝ))
  rw [hfst, show (ratePi M C).real Set.univ = (1 : ℝ) from by
    rw [Measure.real, measure_univ, ENNReal.toReal_one], one_smul]
  have hsnd : (∫ x : (ℝ × ℝ) × LIdx C, (((x.2 : LIdx C) : ℕ) : ℝ)
        ∂(((sojournLaw 2).prod (sojournLaw 2)).prod νL))
      = (((sojournLaw 2).prod (sojournLaw 2))).real Set.univ •
          ∫ l : LIdx C, ((l : ℕ) : ℝ) ∂νL :=
    MeasureTheory.integral_fun_snd (μ := ((sojournLaw 2).prod (sojournLaw 2))) (ν := νL)
      (f := fun l : LIdx C => ((l : ℕ) : ℝ))
  rw [hsnd, show (((sojournLaw 2).prod (sojournLaw 2))).real Set.univ = (1 : ℝ) from by
    rw [Measure.real, measure_univ, ENNReal.toReal_one], one_smul]

/-- ★★ `LIdx C` 上的恒等函数可积（`L ≤ C`）。 -/
theorem integrable_LIdx_val :
    Integrable (fun l : LIdx C => ((l : ℕ) : ℝ)) νL :=
  integrable_of_abs_bound measurable_LIdx_val.aestronglyMeasurable (C := (C : ℝ))
    (Eventually.of_forall fun l => by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast l.2.2)

/-- ★★ **`𝔼[L] > 0`**（由 `L ≥ 1`；取商由此合法）。 -/
theorem integral_LIdx_pos :
    0 < ∫ l, ((l : ℕ) : ℝ) ∂νL := by
  have hone : (∫ _l : LIdx C, (1 : ℝ) ∂νL) = 1 := by
    rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hmono : (∫ _l : LIdx C, (1 : ℝ) ∂νL) ≤ ∫ l, ((l : ℕ) : ℝ) ∂νL :=
    integral_mono_ae (integrable_const 1) integrable_LIdx_val
      (Eventually.of_forall fun l => by
        have h1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast l.2.1
        simpa using h1)
  linarith

/-- ★★★ **识别等式 `hlim`（本文件的核心交付）**：
`(∫ blockW)/(∫ blockL) = W̃ T`，**不需要任何 Wald 恒等式 / 条件期望**。 -/
theorem blockW_div_blockL (hleaf : ∀ i, 0 ≤ leaf i) (T : Topo) :
    (∫ bb, blockW M C leaf a b T bb ∂(blockMeasure M C leaf a b νL)) /
        (∫ bb, blockL M C leaf a b bb ∂(blockMeasure M C leaf a b νL))
      = expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T := by
  rw [blockW_integral (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL) hleaf T,
    blockL_integral (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL)]
  rw [mul_comm]
  exact mul_div_cancel_right₀ _ (ne_of_gt (integral_LIdx_pos (C := C) (νL := νL)))

/-! ## 7. 桥的**五条块层假设**（逐个实例化） -/

theorem block_measurable_pair (T : Topo) :
    Measurable fun bb : Block M C leaf a b =>
      (blockW M C leaf a b T bb, blockL M C leaf a b bb) :=
  (measurable_blockW (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T).prod
    (measurable_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b))

/-- ★★★ **块层两两独立**（`iIndepFun_infinitePi`）。 -/
theorem block_iIndepFun (T : Topo) :
    iIndepFun (fun j (ω : ℕ → Block M C leaf a b) =>
      (blockW M C leaf a b T (ω j), blockL M C leaf a b (ω j)))
      (blockSample M C leaf a b νL) := by
  rw [blockSample]
  exact iIndepFun_infinitePi (X := fun _ (bb : Block M C leaf a b) =>
    (blockW M C leaf a b T bb, blockL M C leaf a b bb))
    (fun _ => block_measurable_pair (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T)

/-- ★★★ **块层同分布**（坐标边缘律相同 ⇒ `IdentDistrib`）。 -/
theorem block_identDistrib (T : Topo) (j : ℕ) :
    IdentDistrib (fun ω : ℕ → Block M C leaf a b =>
        (blockW M C leaf a b T (ω j), blockL M C leaf a b (ω j)))
      (fun ω => (blockW M C leaf a b T (ω 0), blockL M C leaf a b (ω 0)))
      (blockSample M C leaf a b νL) (blockSample M C leaf a b νL) := by
  refine IdentDistrib.mk ?_ ?_ ?_
  · exact ((block_measurable_pair (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T).comp
      (measurable_pi_apply j)).aemeasurable
  · exact ((block_measurable_pair (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T).comp
      (measurable_pi_apply 0)).aemeasurable
  · rw [show (fun ω : ℕ → Block M C leaf a b =>
          (blockW M C leaf a b T (ω j), blockL M C leaf a b (ω j)))
        = (fun bb : Block M C leaf a b => (blockW M C leaf a b T bb, blockL M C leaf a b bb)) ∘
          (fun ω : ℕ → Block M C leaf a b => ω j) from rfl,
      show (fun ω : ℕ → Block M C leaf a b =>
          (blockW M C leaf a b T (ω 0), blockL M C leaf a b (ω 0)))
        = (fun bb : Block M C leaf a b => (blockW M C leaf a b T bb, blockL M C leaf a b bb)) ∘
          (fun ω : ℕ → Block M C leaf a b => ω 0) from rfl]
    rw [← Measure.map_map (block_measurable_pair (M := M) (C := C) (leaf := leaf) (a := a)
        (b := b) T) (measurable_pi_apply j),
      ← Measure.map_map (block_measurable_pair (M := M) (C := C) (leaf := leaf) (a := a)
        (b := b) T) (measurable_pi_apply 0),
      blockSample_map_eval (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL) (i := j),
      blockSample_map_eval (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL) (i := 0)]

/-- ★★★ **`L ≥ 1`**（模型给的）。 -/
theorem block_L1 (j : ℕ) (ω : ℕ → Block M C leaf a b) :
    (1 : ℝ) ≤ blockL M C leaf a b (ω j) := by
  rw [blockL]
  exact_mod_cast (ω j).hL1

/-- ★★★ **`hintM`：块总权重可积**（一致界 `C`）。 -/
theorem block_eval_integrable_W (hleaf : ∀ i, 0 ≤ leaf i) (T : Topo) :
    Integrable (fun ω : ℕ → Block M C leaf a b => blockW M C leaf a b T (ω 0))
      (blockSample M C leaf a b νL) := by
  have h1 : Integrable (fun bb : Block M C leaf a b => blockW M C leaf a b T bb)
      ((blockSample M C leaf a b νL).map (fun ω : ℕ → Block M C leaf a b => ω 0)) := by
    rw [blockSample_map_eval]
    exact integrable_of_abs_bound
      (measurable_blockW (M := M) (C := C) (leaf := leaf) (a := a) (b := b) T).aestronglyMeasurable
      (C := (C : ℝ)) (Eventually.of_forall fun bb => abs_blockW_le hleaf T bb)
  have h2 := h1.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  simpa [Function.comp_def] using h2

/-- ★★★ **`hintL`：块位点数可积**。 -/
theorem block_eval_integrable_L :
    Integrable (fun ω : ℕ → Block M C leaf a b => blockL M C leaf a b (ω 0))
      (blockSample M C leaf a b νL) := by
  have h1 : Integrable (fun bb : Block M C leaf a b => blockL M C leaf a b bb)
      ((blockSample M C leaf a b νL).map (fun ω : ℕ → Block M C leaf a b => ω 0)) := by
    rw [blockSample_map_eval]
    exact integrable_of_abs_bound
      (measurable_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b)).aestronglyMeasurable
      (C := (C : ℝ)) (Eventually.of_forall fun bb => by
        rw [blockL, abs_of_nonneg (by positivity)]
        exact_mod_cast bb.hLC)
  have h2 := h1.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  simpa [Function.comp_def] using h2

/-- ★★★ **`hlim` 在样本空间上的形态**（把块层积分搬到 `ω ↦ blockW (ω 0)`）。 -/
theorem block_hlim (hleaf : ∀ i, 0 ≤ leaf i) (T : Topo) :
    (∫ ω, blockW M C leaf a b T (ω 0) ∂(blockSample M C leaf a b νL)) /
        (∫ ω, blockL M C leaf a b (ω 0) ∂(blockSample M C leaf a b νL))
      = expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T := by
  have hmapW : (∫ ω, blockW M C leaf a b T (ω 0) ∂(blockSample M C leaf a b νL))
      = ∫ bb, blockW M C leaf a b T bb
          ∂((blockSample M C leaf a b νL).map (fun ω : ℕ → Block M C leaf a b => ω 0)) :=
    (integral_map (μ := blockSample M C leaf a b νL)
      (φ := fun ω : ℕ → Block M C leaf a b => ω 0)
      (f := fun bb : Block M C leaf a b => blockW M C leaf a b T bb)
      (measurable_pi_apply 0).aemeasurable
      (measurable_blockW (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
        T).aestronglyMeasurable).symm
  have hmapL : (∫ ω, blockL M C leaf a b (ω 0) ∂(blockSample M C leaf a b νL))
      = ∫ bb, blockL M C leaf a b bb
          ∂((blockSample M C leaf a b νL).map (fun ω : ℕ → Block M C leaf a b => ω 0)) :=
    (integral_map (μ := blockSample M C leaf a b νL)
      (φ := fun ω : ℕ → Block M C leaf a b => ω 0)
      (f := fun bb : Block M C leaf a b => blockL M C leaf a b bb)
      (measurable_pi_apply 0).aemeasurable
      (measurable_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
        ).aestronglyMeasurable).symm
  rw [hmapW, hmapL, blockSample_map_eval (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
    (νL := νL) (i := 0)]
  exact blockW_div_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL) hleaf T

/-! ## 8. ★★★ `hconv` 是定理（桥的实例化） -/

/-- ★★★ **`TopoClose` 形态的 a.e. 收敛**：把 §7 的五条 ＋ `hlim` 喂进
`BlockSLLNTopoClose.empWeight_tendsto_ae`，得到**不假设 `hconv`** 的 a.e. 收敛。

`hrep`（经验表 = 块级平均）由 `empOfBlocks` 的**定义**给出（`rfl`）——
这正是库内桥本身规定的接口形状（`n` 为**基因树棵数**）。 -/
theorem block_emp_tendsto_ae (hleaf : ∀ i, 0 ≤ leaf i) :
    ∀ᵐ ω ∂(blockSample M C leaf a b νL), ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (empOfBlocks M C leaf a b n ω)
        (fun _ _ T => expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T) ε := by
  refine empWeight_tendsto_ae (μ := blockSample M C leaf a b νL) (X := Fin 4)
    (fun _ T => expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
      kingmanMSCTopoSym.τd M.Abar T)
    (empOfBlocks M C leaf a b)
    (Mf := fun k j ω => blockW M C leaf a b k.2 (ω j))
    (Lf := fun _ j ω => blockL M C leaf a b (ω j))
    (fun k => block_iIndepFun (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      (νL := νL) k.2)
    (fun k j => block_identDistrib (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      (νL := νL) k.2 j)
    (fun _ j ω => block_L1 j ω)
    (fun k => block_eval_integrable_W (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      (νL := νL) hleaf k.2)
    (fun _ => block_eval_integrable_L (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
      (νL := νL))
    (fun k => block_hlim (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL)
      hleaf k.2)
    (fun _ _ _ _ _ => rfl)

/-! ## 9. ★★★ 端到端：**不假设 `hconv`** 的 CASTER 统计一致性 -/

/-- ★★★ **端到端 a.e. 统计一致性（不假设 `hconv`）** —— 本批的验收判据。

证明 = `block_emp_tendsto_ae`（`hconv` 由块概率空间**供给**）＋ 库内旗舰端点
`CASTERRateAE.abar_caster_statisticallyConsistent_kingman_ae`（它吃 `hconv` 与 `hE`）。

**假设面**（`set_option autoImplicit false` 下无隐式变量）：模型 `M`、物种树 `(leaf, a, b)`
＋ `0 < a + b`、叶长非负 `hleaf`、块长上界常数 `C`、位点数分布 `νL`（概率测度），
以及**算法性质** `hE`（经验得分被 `E n ω` 最大化）。**不含 `hconv`** ✓。 -/
theorem abar_caster_statisticallyConsistent_kingman_ae_blocks
    (M : SiteRateModel) (leaf : Fin 4 → ℝ) (hleaf : ∀ i, 0 ≤ leaf i)
    (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ))
    (C : ℕ) (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {E : ℕ → (ℕ → Block M C leaf a b) → TopoChoice (Fin 4)}
    (hE : ∀ᵐ ω ∂(blockSample M C leaf a b νL), ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (empOfBlocks M C leaf a b n ω) q
        ≤ topoScore (empOfBlocks M C leaf a b n ω) (E n ω)) :
    ∀ᵐ ω ∂(blockSample M C leaf a b νL), ∃ N : ℕ, ∀ n ≥ N,
      IsTrueT (fun _ _ => Topo.ab_cd) (E n ω) := by
  refine abar_caster_statisticallyConsistent_kingman_ae M leaf a b hab
    (blockSample M C leaf a b νL) (empOfBlocks M C leaf a b) ?_ hE
  filter_upwards [block_emp_tendsto_ae (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
    (νL := νL) hleaf] with ω hω ε hε
  exact hω ε hε

/-! ## 10. 退化一致性与反空洞 -/

/-- ★★ **退化一致性（`r ≡ 1, ρ ≡ 1`）**：`M = twoRate1` 时识别等式的右端**逐字退回**
库内无速率层的 `expWeight ν τd jc69PropADataK.A T`。 -/
theorem twoRate1_Wtilde_eq (ν : Measure KingmanΘ) (τd : KingmanΘ → Topo → ℝ) (T : Topo) :
    expWeight ν τd SiteRateMixture.SiteRateModel.twoRate1.Abar T
      = expWeight ν τd jc69PropADataK.A T :=
  twoRate1_expWeight_eq ν τd T

/-- ★★ **退化一致性（`L ≡ 1` 的最简退化）**：`C = 1` 时块位点数恒为 `1`。 -/
theorem blockL_eq_one_of_C_eq_one (hC : C = 1) (bb : Block M C leaf a b) :
    blockL M C leaf a b bb = 1 := by
  have h : bb.L = 1 := le_antisymm (le_trans bb.hLC (le_of_eq hC)) bb.hL1
  rw [blockL, h]
  norm_num

/-- ★★ **反空洞（块空间）**：只要 `1 ≤ C`，块空间非空。 -/
theorem block_nonempty' (hC : 1 ≤ C) : Nonempty (Block M C leaf a b) := block_nonempty hC

/-- ★★ **反空洞（`Block` 与块测度同时非空）**：给出块测度是概率测度的见证。 -/
theorem block_measure_isProbability (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    ∃ μ : Measure (Block M C leaf a b), IsProbabilityMeasure μ :=
  ⟨blockMeasure M C leaf a b νL, inferInstance⟩

end Phylo.Stat.BlockModelAE

end
