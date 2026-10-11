/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERRateBoxAE
import Phylo.Stat.BlockModelAE

/-!
# `Phylo.Stat.BlockModelRhoAE` —— **物种树也随机**的块概率空间（W16a 第 ① 件）

> ★★ **本件超出 W13 规格（beyond-spec）**，且是 **W15a 自己登记的缺口的续作**。
> 规格 §1.2 把物种树取为**固定**（等价于 `ρ = Measure.dirac (leaf, a, b)`），
> 故 **Dirac 情形已经满足规格**；本件补的是「一般物种树测度 `ρ`」这一层。

## 0. 这一件解决的问题（缺口原文）

`Phylo/Stat/CASTERRateBoxAE.lean` 文件头 §4 诚实边界 4（**逐字**）登记：

> `hconv` 仍作为参数 …… **没有**升到 `BlockModelAE.abar_caster_statisticallyConsistent_kingman_ae_blocks`
> 那一层（**不假设 `hconv`**）：那一层的块概率空间（`Block M C leaf a b`）
> **把物种树固定在 `(leaf, a, b)` 里**，要一般 `ρ` 就得重造一个「物种树也随机」的块空间
> 并重证其坐标独立 / 恒同分布 / `hlim` / `hL1` —— 那是**另一件**，本文件**不做**，如实登记。

本文件就是那一件，**第 ① 件**：把块空间重造出来，并把
**坐标独立**（`blockR_iIndepFun`）与**恒同分布**（`blockR_identDistrib`）
两个陈述证成**定理**（不是假设）。

## 1. 载体：物种树侧与块数据**并列**（这是可测性的关键）

`BlockModelAE.Block M C leaf a b` 把物种树 `(leaf, a, b)` 写**在类型参数里** ——
这正是「物种树确定」的根源。本文件的载体把它搬进**数据**：

```
BlockR M C  ≃  ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)                    ← 物种树侧（随机，独立分量）
              × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate))     ← 块数据（**左嵌套**，与 `Block` 生空间同形）
```

★★ **为什么块数据要「左嵌套」**：`BlockModelAE.Block` 的生空间正是
`((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)`；把它**整体**作为一个独立分量后，
`BlockR.ofRaw` 就是 `⟨p.1, p.2⟩` —— 于是 `toRaw`/`ofRaw` 的互逆是 `rfl`，
且**「物种树侧 → 权重」的依赖可以被隔离到一个非依赖的乘积上**（见 §3）。

★★★ **★A/★D 实测的硬障碍（本件的技术要点，值得单独记一笔）**：
Lean 4 的 `Measurable f` **要求余定义域是固定类型**（`f : α → β`，无依赖）。
若把 `(leaf, a, b)` 与 `Block` 打包成一个依赖族
`bb ↦ Block M C bb.sp.1 bb.sp.2.1 bb.sp.2.2`，则**连陈述都写不出来**：

```
error: Application type mismatch: The argument ... has type
  (p : ...) → Block M C p.1.1 p.1.2.1 p.1.2.2
but is expected to have type ?m.1 → ?m.2   in the application `Measurable ...`
```

（已实测，探针 `_scripts_tmp/w16a_diag.lean` **exit 0 / 0 字节**：固定参数的
`Block.ofRaw` 可测 ✓；依赖参数版本**无法陈述** ✗。）
⇒ 本件的对策有**两条**，缺一不可：
1. **载体并列**（`BlockR`），使块数据单独成为一个**固定形状**的分量；
2. **权重在 `BlockR` 上原生重定义**（§3），使 `Measurable` 面对的函数
   余定义域**恒为 `ℝ`**，而物种树参数只出现在**参数**位置。

★ **`a b : ℝ≥0` 是数学上必需的**（`MSCKingmanMeasure.lean` 文件头 §4.3 已交代）：
它让「内枝长 `a + b ≥ 0`」**由类型保证**，故 `abs_geneScore_le_one` 所需的非负性
在本载体上**处处**成立，无需 `a.e.` 搬运（第 ② 件用）。

★ 与 `KingmanParam = ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ)`（`MSCKingmanMeasure.lean:97`）
的关系：`BlockR` 的**第一分量就是 `KingmanParam` 的物种树侧**，
⇒ `kingmanMSCMeasure ρ` 的输入空间与前推映射 `toKingmanΘ` **逐字复用**，无需重造。

## 2. 概率空间：乘积测度经**一个可测映射**推前

```
blockRPMeasure = (ρ ⊗ (sojournLaw 2 ⊗ sojournLaw 2) ⊗ νL ⊗ ν_κ) 经 BlockR.ofRaw 推前
blockRSample   = Measure.infinitePi (fun _ : ℕ => blockRPMeasure)
```

块的边缘是**四块乘积**，且 `ν_κ = ratePi M C = Measure.pi (fun _ : Fin C => rateMeasure M)`
**坐标 iid** ⇒ 块坐标 iid 由 `iIndepFun_infinitePi` **直接**给出（见 §5）。

## 3. ★ 权重在 `BlockR` 上的**原生**定义（可测性的枢纽）

关键观察：`BlockModelAE.siteW` 的**值**只通过 `(叶长, a, b, v, L, κ)` 依赖块，
而这几项在 `BlockR` 上都是**非依赖**的投影。于是把 `scale` 的**坐标展开**直接写在 `BlockR` 上：

```
Prod.fst (M.scale (thetaR bb) (bb.rest.2 i))
  = (fun j => M.r j (bb.rest.2 i) * M.ρ (bb.rest.2 i) * bb.sp.1 j,
     M.ρ (bb.rest.2 i) * ((bb.sp.2.1 : ℝ) + (bb.sp.2.2 : ℝ)))
Prod.snd (M.scale ...) = Prod.snd (thetaR bb)          -- 两个 Bool，不被 scale 改动
```

这就是 `BlockModelAE.measurable_scaleFst` 的**联合版**（物种树参数不再固定），
而它的可测性只需各分量的可测性 ⇒ **纯复合**，不再撞依赖余定义域那面墙。

## 4. ★ 相对既有三件的**层次表**

| | `BlockModelAE`（W13） | `CASTERRateBoxAE`（W15a） | **本文件（W16a ①）** |
|---|---|---|---|
| 物种树 | **写死在类型里** | 一般 `ρ`（端到端层） | **进块数据**（块层） |
| 块空间 | `Block M C leaf a b` | 无（未做） | **`BlockR M C`** |
| 坐标 iid | 定理 | — | **定理**（`blockR_iIndepFun`） |
| 恒同分布 | 定理 | — | **定理**（`blockR_identDistrib`） |
| `hconv` | 定理（块层供给） | **仍是假设** | 待第 ② 件 |

## 5. ★A 纪律：本文件引用的每个既有名字都**读过定义处**

逐条列出（`grep` 命中处 → 命名空间，**不猜前缀**）：

| 名字 | 定义处 | 命名空间 |
|---|---|---|
| `KingmanParam` / `toKingmanΘ` / `kingmanMSCMeasure` | `MSCKingmanMeasure.lean:97/101/138` | `Phylo.Stat.MSCKingmanMeasure` |
| `measurable_toKingmanΘ` | `MSCKingmanMeasure.lean:116` | 同上 |
| `sojournLaw` | `KingmanCoalescent.lean` | `Phylo.Stat.KingmanCoalescent` |
| `SiteRateModel` / `scale` / `Abar` / `scale_fst_fst` | `SiteRateMixture.lean:104/171/240/176` | `Phylo.Stat.SiteRateMixture` |
| `Block` / `LIdx` / `Block.θOf` / `Block.toRaw` / `Block.ofRaw` | `BlockModelAE.lean:177/172/195/198/202` | `Phylo.Stat.BlockModelAE` |
| `ratePi` / `rateMeasure` / `siteW` / `blockW` / `blockL` | `BlockModelAE.lean:161/140/274/281/286` | 同上 |
| `measurable_of_rate` / `measurable_blockW` / `measurable_blockL` | `BlockModelAE.lean:135/374/319` | 同上 |
| `measurable_Kingmanτd` / `measurable_geneScore` | `BlockModelAE.lean:364/368` 处**引用** | `MSCKingmanMeasure` / `SiteWeightMeasurable` |
| `Topo` | `CASTERWeights.lean` | `Phylo.Stat.CASTERWeights` |
| `iIndepFun_infinitePi` | Mathlib `Probability/Independence/InfinitePi.lean:124` | `ProbabilityTheory` |
| `Measure.infinitePi_map_eval` | Mathlib `Probability/ProductMeasure.lean:477` | `MeasureTheory` |

⚠️ **未定位（记作未知，不是「不存在」）**：
* `Measure.infinitePi` 的 `IsProbabilityMeasure` **实例名**（本文件用 `inferInstance`，未去查名字）；
* `IdentDistrib.mk` 的三个字段名（既有 `block_identDistrib` 已用，本文件照抄其**用法**）。

## 6. 诚实边界（本件**只做第 ① 件**）

1. **本文件不证识别等式 `hlim`、也不给端到端定理** —— 那是第 ② 件。
   本件交付的是**两个定理**：坐标独立 ＋ 恒同分布（＋ 概率空间本身）。
2. `BlockR` 的**内枝长正性 `0 < a + b` 不在类型里**（`a b : ℝ≥0` 只给 `≥ 0`）。
   与既有 `BlockModelAE.Block` **同口径**：那里把 `0 < a + b` 作为**定理的参数**传递。
   本件**同样**不强制它 —— 而它在箱体先验下是**定理**（`CASTERRateBoxAE.hlx_of_boxTheta`，第 ② 件用）。
3. **权重的原生定义与 `BlockModelAE` 的关系**：`blockWR_eq_blockW` / `siteWR_eq_siteW`
   给出**逐字**（`rfl`）的一致性 —— 故第 ② 件的识别等式能直接搬用既有结果。
4. `π` / `κ` 仍**只登记不使用**（走 JC69 端，与 `SiteRateMixture`/`CASTERRateAE`/`BlockModelAE` 口径一致）。
5. **不改任何既有文件里的声明**（★C）：本文件只**新增**，且只 `import`。
6. **无未完成证明 / 无新增公理声明**：全部声明正面构造。
-/

set_option autoImplicit false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Phylo.Stat.BlockModelRhoAE

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.MSCKingman (KingmanΘ kingmanMSCTopoSym)
open Phylo.Stat.MSCKingmanMeasure
open Phylo.Stat.KingmanCoalescent (sojournLaw)
open Phylo.Stat.SiteRateMixture
open Phylo.Stat.BlockModelAE
open Phylo.Stat.SiteWeightMeasurable
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.CASTERRateAE

variable {M : SiteRateModel} {C : ℕ}

/-! ## 1. 载体：物种树侧与块数据**并列** -/

/-- ★★★ **「物种树也随机」的块**：物种树侧参数 `sp`（＝ `KingmanParam` 的第一分量）
**并列**于块数据 `rest`（形状与 `BlockModelAE.Block` 的生空间**逐字相同**）。

★ 与 `BlockModelAE.Block M C leaf a b` 的**唯一**差别：物种树 `(leaf, a, b)`
从**类型参数**搬进了**数据**（作为**独立的第一分量**，见文件头 §1 的硬障碍说明）。 -/
structure BlockR (M : SiteRateModel) (C : ℕ) where
  /-- 物种树侧参数：叶长 `Fin 4 → ℝ`、根以下两段内枝长 `(a, b) : ℝ≥0 × ℝ≥0`。 -/
  sp : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0
  /-- 块数据：溯祖等待时间 `v`、位点数 `l`（`1 ≤ l ≤ C`）、逐位点速率类别 `κ`。 -/
  rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)

/-- 块的**生空间**：物种树侧与块数据的**右嵌套**二元组
（与 `Measure.prod` 的嵌套逐字对应）。 -/
abbrev BlockR.Raw (M : SiteRateModel) (C : ℕ) : Type :=
  ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate))

/-- 生空间 → 块。 -/
def BlockR.ofRaw (p : BlockR.Raw M C) : BlockR M C := ⟨p.1, p.2⟩

/-- 块 → 生空间。 -/
def BlockR.toRaw (bb : BlockR M C) : BlockR.Raw M C := (bb.sp, bb.rest)

/-- ★ `toRaw` 是 `ofRaw` 的**左逆**（`rfl`）。 -/
theorem BlockR.toRaw_ofRaw (p : BlockR.Raw M C) : BlockR.toRaw (BlockR.ofRaw p) = p := by
  obtain ⟨sp, rest⟩ := p
  rfl

/-- ★ `ofRaw` 是 `toRaw` 的**右逆**（`rfl`）。 -/
theorem BlockR.ofRaw_toRaw (bb : BlockR M C) : BlockR.ofRaw (BlockR.toRaw bb) = bb := by
  obtain ⟨sp, rest⟩ := bb
  rfl

/-- 可测结构：经 `toRaw` 拉回（与 `BlockModelAE.instMeasurableSpaceBlock` 同一手法）。 -/
instance instMeasurableSpaceBlockR (M : SiteRateModel) (C : ℕ) :
    MeasurableSpace (BlockR M C) :=
  MeasurableSpace.comap (BlockR.toRaw (M := M) (C := C)) inferInstance

theorem measurable_toRawR :
    Measurable (BlockR.toRaw (M := M) (C := C)) :=
  Measurable.of_comap_le le_rfl

theorem measurable_ofRawR :
    Measurable (BlockR.ofRaw (M := M) (C := C)) := by
  refine Measurable.of_comap_le ?_
  rw [instMeasurableSpaceBlockR]
  rw [MeasurableSpace.comap_comp,
    show (BlockR.toRaw (M := M) (C := C)) ∘ (BlockR.ofRaw (M := M) (C := C)) = id from
      funext fun p => BlockR.toRaw_ofRaw p,
    MeasurableSpace.comap_id]

/-- ★★ **反空洞**：块非空（物种树取零参数、`l = 1`、速率类别取库内正权类别 `kRef`）。 -/
theorem blockR_nonempty (hC : 1 ≤ C) : Nonempty (BlockR M C) :=
  ⟨BlockR.ofRaw (M := M) (C := C)
    ((((fun _ : Fin 4 => (0 : ℝ)), (0 : ℝ≥0), (0 : ℝ≥0)),
      ((((0 : ℝ), (0 : ℝ)), ⟨1, le_rfl, hC⟩), (fun _ : Fin C => M.kRef))))⟩

/-! ## 2. 树侧数据 -/

namespace BlockR

/-- ★★ **块的树侧 `KingmanΘ` 数据**：`θ = toKingmanΘ (sp, v)`（与 `Block.θOf` 同一公式）。 -/
def thetaOf (bb : BlockR M C) : KingmanΘ := toKingmanΘ ((bb.sp, bb.rest.1.1))

end BlockR

theorem measurable_thetaOfR :
    Measurable (BlockR.thetaOf (M := M) (C := C)) :=
  measurable_toKingmanΘ.comp
    (Measurable.prod ((measurable_toRawR (M := M) (C := C)).fst)
      ((measurable_toRawR (M := M) (C := C)).snd.fst.fst))

/-! ## 3. ★★★ 权重在 `BlockR` 上的**原生**定义（可测性的枢纽） -/

/-- ★★ **`scale` 的第一分量**（逐位点速率类别 `i`）—— 把物种树参数**显式**留在外面，
故余定义域是**固定类型**（`(Fin 4 → ℝ) × ℝ`），`Measurable` 可以陈述。 -/
theorem measurable_scaleFstR (i : Fin C) :
    Measurable fun bb : BlockR M C =>
      Prod.fst (M.scale (BlockR.thetaOf bb) (bb.rest.2 i)) := by
  have hk : Measurable fun bb : BlockR M C => bb.rest.2 i :=
    (measurable_pi_apply i).comp (measurable_toRawR (M := M) (C := C)).snd.snd
  have hρ : Measurable fun bb : BlockR M C => M.ρ (bb.rest.2 i) :=
    (measurable_of_rate M (fun j : M.Rate => M.ρ j)).comp hk
  have hrmj : ∀ j : Fin 4, Measurable fun bb : BlockR M C => M.r (bb.rest.2 i) j :=
    fun j => (measurable_of_rate M (fun jj : M.Rate => M.r jj j)).comp hk
  have hleaf : Measurable fun bb : BlockR M C => bb.sp.1 :=
    (measurable_toRawR (M := M) (C := C)).fst.fst
  have hcomp1 : Measurable fun bb : BlockR M C =>
      fun j : Fin 4 => M.r (bb.rest.2 i) j * M.ρ (bb.rest.2 i) * bb.sp.1 j := by
    rw [measurable_pi_iff]
    intro j
    exact ((hrmj j).mul hρ).mul ((measurable_pi_apply j).comp hleaf)
  have hlen : Measurable fun bb : BlockR M C => (bb.sp.2.1 : ℝ) + (bb.sp.2.2 : ℝ) :=
    (measurable_subtype_coe.comp (measurable_toRawR (M := M) (C := C)).fst.snd.fst).add
      (measurable_subtype_coe.comp (measurable_toRawR (M := M) (C := C)).fst.snd.snd)
  have hpair : Measurable fun bb : BlockR M C =>
      ((fun j : Fin 4 => M.r (bb.rest.2 i) j * M.ρ (bb.rest.2 i) * bb.sp.1 j),
        M.ρ (bb.rest.2 i) * ((bb.sp.2.1 : ℝ) + (bb.sp.2.2 : ℝ))) :=
    Measurable.prod hcomp1 (hρ.mul hlen)
  convert hpair using 1
  funext bb
  rfl

/-- **单个位点的权重**（随机物种树版）：在 `BlockR` 上**原生**定义（见文件头 §3）。 -/
noncomputable def siteWR (M : SiteRateModel) (C : ℕ) (T : Topo) (bb : BlockR M C)
    (i : Fin C) : ℝ :=
  ∑ T' : Topo, kingmanMSCTopoSym.τd (BlockR.thetaOf bb) T' *
    jc69PropAData.A (Prod.fst (M.scale (BlockR.thetaOf bb) (bb.rest.2 i))) T' T

/-- ★★★ **块总权重**（随机物种树版）：`∑_{i < L} siteWR i`，写成 `Fin C` 上的**固定长度**和
＋指示函数（与 `BlockModelAE.blockW` **逐字同形**）。 -/
noncomputable def blockWR (M : SiteRateModel) (C : ℕ) (T : Topo) (bb : BlockR M C) : ℝ :=
  ∑ i : Fin C, if (i : ℕ) < bb.rest.1.2.1 then siteWR M C T bb i else 0

/-- **块位点数**（随机物种树版）。 -/
def blockLR (M : SiteRateModel) (C : ℕ) (bb : BlockR M C) : ℝ :=
  (bb.rest.1.2.1 : ℝ)

/-! ### 3.1 ★ 与 `BlockModelAE` 的**逐字一致性**（第 ② 件与退化探针的接口） -/

/-- ★★ **`BlockR` ↔ `BlockModelAE.Block` 的粘合**：把物种树侧与块数据原样喂进 `Block`。 -/
def blockRToBlock (bb : BlockR M C) :
    Block M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 :=
  Block.ofRaw (M := M) (C := C) (leaf := bb.sp.1) (a := bb.sp.2.1) (b := bb.sp.2.2) bb.rest

/-- ★ **树侧 `θ` 与 `Block.θOf` 逐字一致**（`rfl`）。 -/
theorem blockRToBlock_thetaOf (bb : BlockR M C) :
    BlockR.thetaOf bb = Block.θOf (blockRToBlock bb) := rfl

/-- ★★★ **`siteWR` 与 `BlockModelAE.siteW` 逐字一致**（`rfl`）。

⇒ 第 ② 件的识别等式（`blockW_integral` 等）可以直接搬用，无需重证。 -/
theorem siteWR_eq_siteW (T : Topo) (bb : BlockR M C) (i : Fin C) :
    siteWR M C T bb i = siteW M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 T (blockRToBlock bb) i := by
  unfold siteWR siteW blockRToBlock Block.ofRaw BlockR.thetaOf Block.θOf
  rfl

/-- ★★★ **`blockWR` 与 `BlockModelAE.blockW` 逐字一致**（`rfl`）。 -/
theorem blockWR_eq_blockW (T : Topo) (bb : BlockR M C) :
    blockWR M C T bb = blockW M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 T (blockRToBlock bb) := by
  unfold blockWR blockW siteWR siteW blockRToBlock Block.ofRaw BlockR.thetaOf Block.θOf
  rfl

/-- ★★★ **`blockLR` 与 `BlockModelAE.blockL` 逐字一致**（`rfl`）。 -/
theorem blockLR_eq_blockL (bb : BlockR M C) :
    blockLR M C bb = blockL M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 (blockRToBlock bb) := by
  unfold blockLR blockL blockRToBlock Block.ofRaw
  rfl

/-- ★ **`blockLR` 只依赖位点数**（物种树随机不影响位点数）。 -/
theorem blockLR_eq (bb : BlockR M C) : blockLR M C bb = (bb.rest.1.2.1 : ℝ) := rfl

/-! ### 3.2 ★★★ 退化一致性（门 5）：`ρ = dirac` 的块**逐字退回**库内既有结论

★ **最强探针的形态**：物种树侧取**固定的** `(leaf, a, b)` 时，
本文件的 `blockWR` / `blockLR` **逐字**（`rfl` 级、即**定义层同一**）退回
`BlockModelAE.blockW` / `blockL` —— 而后者正是库内
`abar_caster_statisticallyConsistent_kingman_ae_blocks`（`:844`）所用的那一张表。

⇒ 故「一般 `ρ`」的新结论在 Dirac 上**不是新东西**，而是既有结果的**特例** ✓。 -/

/-- ★★★ **退化一致性（门 5，块总权重）**：`bb.sp = (leaf, a, b)`（即 `ρ = Measure.dirac`）时，
`blockWR` **逐字退回** `BlockModelAE.blockW`。 -/
theorem blockWR_dirac_W (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T : Topo)
    (rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) :
    blockWR M C T (BlockR.ofRaw ((leaf, a, b), rest))
      = blockW M C leaf a b T
        (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b) rest) :=
  blockWR_eq_blockW (M := M) (C := C) T (BlockR.ofRaw ((leaf, a, b), rest))

/-- ★★★ **退化一致性（门 5，块位点数）**：同上，`blockLR` 退回 `BlockModelAE.blockL`。 -/
theorem blockLR_dirac_W (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) :
    blockLR M C (BlockR.ofRaw ((leaf, a, b), rest))
      = blockL M C leaf a b
        (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b) rest) :=
  blockLR_eq_blockL (M := M) (C := C) (BlockR.ofRaw ((leaf, a, b), rest))

/-- ★★★ **退化一致性（门 5，块空间到既有块空间的映射）**：物种树固定为 `(leaf, a, b)` 时，
`BlockR.restToBlock` 型映射**逐字**就是 `Block.ofRaw`。 -/
theorem blockRToBlock_dirac (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) :
    blockRToBlock (M := M) (C := C) (BlockR.ofRaw ((leaf, a, b), rest))
      = Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b) rest := rfl

/-- ★★★ **退化一致性（门 5，`θ` 数据）**：`BlockR.thetaOf` 在固定物种树上**逐字退回**
`Block.θOf`（`rfl`）。 -/
theorem blockRToBlock_thetaOf_dirac (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) :
    BlockR.thetaOf (BlockR.ofRaw ((leaf, a, b), rest))
      = Block.θOf (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b) rest) := rfl

/-! ## 4. 概率空间：块测度与块样本（无穷乘积） -/

/-- ★★★ **随机物种树的块测度**：
`(ρ ⊗ (sojournLaw 2 ⊗ sojournLaw 2) ⊗ νL ⊗ ratePi M C)` 经 `BlockR.ofRaw` 推前。

★ 分解读法：`ρ` 抽物种树 → 两个 `sojournLaw 2` 抽根以下两侧的溯祖等待时间
→ `νL` 抽位点数 → `ratePi M C` 抽逐位点速率类别（**坐标 iid**）。
这与 `kingmanMSCMeasure ρ` 的物种树侧**完全同一个 `ρ`**（无重复、无错配）。 -/
noncomputable def blockRPMeasure (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) (νL : Measure (LIdx C)) : Measure (BlockR M C) :=
  Measure.map (BlockR.ofRaw (M := M) (C := C))
    (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))

/-- ★★ 块测度是**概率测度**（四块都是概率测度 ⇒ 乘积是，推前保概率）。 -/
instance instIsProbabilityMeasureBlockRPMeasure (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    IsProbabilityMeasure (blockRPMeasure M C ρ νL) where
  measure_univ := by
    rw [blockRPMeasure, Measure.map_apply measurable_ofRawR MeasurableSet.univ, Set.preimage_univ]
    simp

/-- ★★★ **块样本空间**：`ℕ → BlockR` 上的**无穷乘积测度**（块 iid）。 -/
noncomputable abbrev blockRSample (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) (νL : Measure (LIdx C)) :
    Measure (ℕ → BlockR M C) :=
  Measure.infinitePi fun _ : ℕ => blockRPMeasure M C ρ νL

instance instIsProbabilityMeasureBlockRSample (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    IsProbabilityMeasure (blockRSample M C ρ νL) := by
  rw [blockRSample]
  infer_instance

/-- ★★ 坐标 `i` 的**边缘律**（`Measure.infinitePi_map_eval`）。 -/
theorem blockRSample_map_eval (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (i : ℕ) :
    (blockRSample M C ρ νL).map (fun ω : ℕ → BlockR M C => ω i) = blockRPMeasure M C ρ νL :=
  Measure.infinitePi_map_eval (fun _ : ℕ => blockRPMeasure M C ρ νL) i

/-! ## 5. ★★ 可测性（原生定义下的纯复合） -/

/-- ★★ **`siteWR` 可测**：`τd` 与 `A ∘ scale` 的可测性逐项相乘再有限求和。 -/
theorem measurable_siteWR (T : Topo) (i : Fin C) :
    Measurable fun bb : BlockR M C => siteWR M C T bb i := by
  refine Finset.measurable_sum Finset.univ fun T' _ => ?_
  have hτ : Measurable fun bb : BlockR M C => kingmanMSCTopoSym.τd (BlockR.thetaOf bb) T' :=
    (measurable_Kingmanτd T').comp (measurable_thetaOfR (M := M) (C := C))
  have hA : Measurable fun bb : BlockR M C =>
      jc69PropAData.A (Prod.fst (M.scale (BlockR.thetaOf bb) (bb.rest.2 i))) T' T :=
    (measurable_geneScore T' T).comp (measurable_scaleFstR (M := M) (C := C) i)
  exact hτ.mul hA

/-- ★★ **块总权重关于块可测**（随机物种树版）。 -/
theorem measurable_blockWR (T : Topo) :
    Measurable fun bb : BlockR M C => blockWR M C T bb := by
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  have hL : MeasurableSet {bb : BlockR M C | (i : ℕ) < bb.rest.1.2.1} :=
    measurableSet_lt measurable_const
      (measurable_subtype_coe.comp (measurable_toRawR (M := M) (C := C)).snd.fst.snd)
  exact Measurable.ite hL (measurable_siteWR (M := M) (C := C) T i) measurable_const

/-- ★★ **块位点数关于块可测**（随机物种树版）。 -/
theorem measurable_blockLR :
    Measurable fun bb : BlockR M C => blockLR M C bb :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_subtype_coe.comp (measurable_toRawR (M := M) (C := C)).snd.fst.snd)

/-- ★★ **对子可测**（`(blockWR, blockLR)`）。 -/
theorem blockR_measurable_pair (T : Topo) :
    Measurable fun bb : BlockR M C => (blockWR M C T bb, blockLR M C bb) :=
  (measurable_blockWR (M := M) (C := C) T).prod (measurable_blockLR (M := M) (C := C))

/-! ## 6. ★★★ 坐标独立（`iIndepFun`）与恒同分布（`IdentDistrib`） -/

/-- ★★★ **块层两两独立（随机物种树版）**（`iIndepFun_infinitePi`）。

`(W̃_j, L̃_j)_j` 在 `blockRSample` 下**两两独立** —— 这是 W15a 登记的
「重证坐标独立」那一条，**是定理，不是假设**。 -/
theorem blockR_iIndepFun (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (T : Topo) :
    iIndepFun (fun j (ω : ℕ → BlockR M C) =>
      (blockWR M C T (ω j), blockLR M C (ω j)))
      (blockRSample M C ρ νL) := by
  rw [blockRSample]
  exact iIndepFun_infinitePi (X := fun _ (bb : BlockR M C) =>
    (blockWR M C T bb, blockLR M C bb))
    (fun _ => blockR_measurable_pair (M := M) (C := C) T)

/-- ★★★ **块层恒同分布（随机物种树版）**：任意两个坐标 `j` 与 `0` 同分布
（无穷乘积测度的坐标边缘律相同 ⇒ `IdentDistrib`）。

这是 W15a 登记的「重证恒同分布」那一条，**是定理，不是假设**。 -/
theorem blockR_identDistrib (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (T : Topo) (j : ℕ) :
    IdentDistrib (fun ω : ℕ → BlockR M C => (blockWR M C T (ω j), blockLR M C (ω j)))
      (fun ω => (blockWR M C T (ω 0), blockLR M C (ω 0)))
      (blockRSample M C ρ νL) (blockRSample M C ρ νL) := by
  refine IdentDistrib.mk ?_ ?_ ?_
  · exact ((blockR_measurable_pair (M := M) (C := C) T).comp
      (measurable_pi_apply j)).aemeasurable
  · exact ((blockR_measurable_pair (M := M) (C := C) T).comp
      (measurable_pi_apply 0)).aemeasurable
  · rw [show (fun ω : ℕ → BlockR M C => (blockWR M C T (ω j), blockLR M C (ω j)))
        = (fun bb : BlockR M C => (blockWR M C T bb, blockLR M C bb)) ∘
          (fun ω : ℕ → BlockR M C => ω j) from rfl,
      show (fun ω : ℕ → BlockR M C => (blockWR M C T (ω 0), blockLR M C (ω 0)))
        = (fun bb : BlockR M C => (blockWR M C T bb, blockLR M C bb)) ∘
          (fun ω : ℕ → BlockR M C => ω 0) from rfl]
    rw [← Measure.map_map (blockR_measurable_pair (M := M) (C := C) T) (measurable_pi_apply j),
      ← Measure.map_map (blockR_measurable_pair (M := M) (C := C) T) (measurable_pi_apply 0),
      blockRSample_map_eval (M := M) (C := C) (ρ := ρ) (νL := νL) (i := j),
      blockRSample_map_eval (M := M) (C := C) (ρ := ρ) (νL := νL) (i := 0)]

/-- ★★★ **`L̃ ≥ 1` 处处成立**（随机物种树版）：由 `LIdx` 的**类型**保证，与物种树无关。
这是 W15a 登记的「重证 `hL1`」那一条。 -/
theorem blockR_L1 (j : ℕ) (ω : ℕ → BlockR M C) : (1 : ℝ) ≤ blockLR M C (ω j) := by
  rw [blockLR_eq]
  exact_mod_cast (ω j).rest.1.2.2.1

end Phylo.Stat.BlockModelRhoAE

end
