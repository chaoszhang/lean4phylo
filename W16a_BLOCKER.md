# W16a 精确卡点报告 —— `Measurable` 与「物种树随机化」在**陈述层**相撞

> 作者：W16a 子代理。时间：2026-10-12 约 06:1x。
> 状态：**第 ① 件的载体＋概率空间已全绿**（冻结基线 md5 `b613d62c3894d6b736536d1cbda36e1a`，320 行）；
> **iid / 恒同分布两条未证出**，卡点如下（已定位到**陈述层**，不是证明技巧问题）。

---

## 1. 障碍陈述（附**确切 error 原文**）

Lean 4 的 `Measurable f` 要求 **余定义域是固定类型**（`f : α → β`，`β` 不含 `f` 的自变量）。
把物种树 `(leaf, a, b)` 与 `Block` **打包**后，映射

```lean
fun bb => Block M C bb.sp.1 bb.sp.2.1 bb.sp.2.2      -- 类型 bb ↦ Block M C bb.sp.1 …
```

是一个**依赖族**（余定义域依赖 `bb`），于是 `Measurable` **连陈述都写不出来**：

```
error: Application type mismatch: The argument
  <lambda>
has type
  (p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (...)) → Block M C p.1.1 p.1.2.1 p.1.2.2
but is expected to have type
  ?m.1 → ?m.2
in the application
  Measurable <lambda>
```

⚠️ 注意：这个 error 发生在**陈述的 elaboration 阶段** —— 也就是说，**连 `theorem ... :` 那一行都过不去**，
不是"证不出来"。

## 2. 根因

`BlockModelAE.Block` 把物种树**编进了【类型】**：

```lean
structure Block (M : SiteRateModel) (C : ℕ) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) where
  v : ℝ × ℝ
  L : ℕ
  hL1 : 1 ≤ L
  hLC : L ≤ C
  κ : Fin C → M.Rate
```

⇒ `Block M C leaf a b` 里的 `leaf a b` 是**类型参数**，不是数据。
"让物种树随机化"＝让类型随样本变化 ⇒ 与 `Measurable`（要求固定类型）**根本不相容**。

★★ **这是一条对库设计有用的结构性认识**：
「把环境参数编进类型」在**固定环境**下很省事（`BlockModelAE` 因此能把
`abs_geneScore_le_one` 的非负前提**处处**满足），但它**排除了**"环境本身随机"的推广。
要推广，必须**在数据上原生重定义**权重（见 §4），不能对固定环境的 `blockW` 做依赖复合。

## 3. 试过的四条路（各自在哪一步失败）

| 路径 | 做法 | 失败点 |
|---|---|---|
| ① `rw` | `rw [show (fun p => Block.ofRaw … p) = Block.ofRaw … ∘ (fun p => (p.1, p.2)) from rfl]` | **`rw` 无法在 `Measurable` 目标下改写**：目标里出现 `?m.2` 元变量，`rw` 报 `has type … expected ?m.2` ✗ |
| ② `convert` | `convert (measurable_ofRaw …) using 2` | `convert` 留下**无法求解的元变量** `⊢ Measurable ?m.2`，`No goals`／元变量悬挂 ✗ |
| ③ `Measurable.of_comap_le` | 用 `Block` 的可测结构是 `comap Block.toRaw` 这一事实，把目标化为 `comap` 等式 | **目标本身仍是依赖族**：`of_comap_le` 的 `f` 也必须进 `Measurable`，同一面墙 ✗ |
| ④ `Sigma` 打包 | 把 `(leaf,a,b)` 与 `Block` 打成一个 `Sigma` 类型，希望余定义域固定 | `Sigma` 只是**换个地方**陈述依赖；`Measurable` 对 `Sigma` 值函数同样要求**固定**的 `Sigma` 类型，而这里的 `Sigma` 索引仍是变量的函数 ✗（且 `Measurable.sigma` 在库内**未定位**，见 §5） |

## 4. ★ 出路（**已验证方向**，未实施完）

**在 `BlockR` 上原生重定义权重**，使所有进入 `Measurable` 的函数**余定义域恒为 `ℝ`**，
物种树参数只出现在**参数**位置：

```lean
structure BlockR (M : SiteRateModel) (C : ℕ) where
  sp   : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0                            -- 物种树侧（随机，独立分量）
  rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)              -- 块数据（与 Block 生空间同形）
```

关键观察：**`siteW` 的「值」只通过 `(叶长, a, b, v, L, κ)` 依赖块**，而这几项在 `BlockR` 上都是
**非依赖**投影。于是把 `scale` 的**坐标展开**直接写在 `BlockR` 上：

```
Prod.fst (M.scale (thetaR bb) (bb.rest.2 i))
  = (fun j => M.r j (bb.rest.2 i) * M.ρ (bb.rest.2 i) * bb.sp.1 j,
     M.ρ (bb.rest.2 i) * ((bb.sp.2.1 : ℝ) + (bb.sp.2.2 : ℝ)))
```

⇒ 这是 `BlockModelAE.measurable_scaleFst` 的**联合版**（物种树参数不再固定），
其可测性是**纯复合**，不再撞依赖余定义域那面墙。
随后照 `BlockModelAE.measurable_siteW` / `measurable_blockW` 的老路
（`Finset.measurable_sum` ＋ `Measurable.ite` ＋ `measurable_Kingmanτd` ＋ `measurable_geneScore`）
逐项重证即可。

**实现位置**：`Phylo/Stat/BlockModelRhoAE2.lean`（新文件，冻结基线不动）。

### ★★★ 实测结果（**已打通，2026-10-12 约 06:3x**）

上述出路**完全奏效** ✓ —— `Phylo/Stat/BlockModelRhoAE2.lean`
（**469 行**，md5 见 §9）**`exit 0` / stdout 0 字节 / stderr 0 字节**，
`lake build` **3867 jobs** exit 0，`#print axioms` 全净 ✓。

**打通的关键三步**（供后人复用）：
1. **载体并列**：`BlockR` 把物种树侧 `sp` 与块数据 `rest` 做成**并列的两个分量**
   （`rest` 的形状**逐字**取 `Block` 的生空间 `((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)`）；
2. **原生重定义**：`siteWR` / `blockWR` / `blockLR` **不经过** `BlockModelAE.blockW`，
   而是直接在 `BlockR` 上按**同一算式**定义 ⇒ 所有进 `Measurable` 的函数余定义域**恒为 `ℝ`**；
3. **逐项重证可测性**：`measurable_scaleFstR`（`scale` 的坐标展开，物种树参数留在**参数**位）
   ⇒ `measurable_siteWR`（`τd` × `A∘scale`，有限和）⇒ `measurable_blockWR`（`Finset.measurable_sum`
   ＋ `Measurable.ite` ＋ `measurableSet_lt`）⇒ `blockR_measurable_pair`
   ⇒ `blockR_iIndepFun`（`iIndepFun_infinitePi`）＋ `blockR_identDistrib`。

★ **"两处都是 `ℝ` 值"是本条路成功的原因**：物种树随机性只移动**参数**，
不移动**余定义域**。这也解释了为什么"依赖复合 `blockW`"必然失败。

★ **对库设计的推论**：若将来还要做"环境随机化"的推广，
**应把环境参数放进数据、并把该层函数写成乘积空间上的非依赖函数**；
"环境编进类型"只在**固定环境**下可取。

## 5. ★A 名单（本卡点相关的引用，均已读定义处）

| 名字 | 定义处 | 命名空间 |
|---|---|---|
| `Block` / `blockW` / `siteW` / `LIdx` | `BlockModelAE.lean:177/281/274/172` | `Phylo.Stat.BlockModelAE` |
| `measurable_ofRaw` / `measurable_blockW` / `measurable_of_rate` | `BlockModelAE.lean:221/374/135` | 同上 |
| `measurable_Kingmanτd` | **`CASTERRateAE.lean:138`** | `Phylo.Stat.CASTERRateAE` |
| `jc69PropAData` | **`CASTERGeneTree.lean:593`** | `Phylo.Stat.CASTERGeneTree` |
| `measurable_geneScore` | `SiteWeightMeasurable.lean` | `Phylo.Stat.SiteWeightMeasurable` |
| `toKingmanΘ` / `kingmanMSCMeasure` / `measurable_toKingmanΘ` | `MSCKingmanMeasure.lean:101/138/116` | `Phylo.Stat.MSCKingmanMeasure` |
| `iIndepFun_infinitePi` | Mathlib `Probability/Independence/InfinitePi.lean:124` | `ProbabilityTheory` |
| `Measure.infinitePi_map_eval` | Mathlib `Probability/ProductMeasure.lean:477` | `MeasureTheory` |

⚠️ **未定位（记作未知，不是「不存在」）**：
* `Measurable.sigma`（把依赖族打成 `Sigma` 的可测性引理）—— **未定位**（`grep` 无命中，
  只找到 `measurable_sigmaCurry` / `measurable_sigmaUncurry`）；
* `Measure.infinitePi` 的 `IsProbabilityMeasure` **实例名**（用的 `inferInstance`）；
* `IdentDistrib.mk` 的三个字段名（照抄既有 `block_identDistrib` 的**用法**）。

## 6. 探针证据

* `_scripts_tmp/w16a_diag.lean`（镜像内，**exit 0 / stdout 0 字节 / stderr 0 字节**）：
  * DIAGNOSTIC 1：固定参数的 `Block.ofRaw`（`leaf := fun _ => 0`, `a := b := 0`）**可测** ✓
    （`measurable_ofRaw` 直接给出）；
  * DIAGNOSTIC 2（**注释形式**，因为写出来就是 error）：依赖参数版本**无法陈述** ✗；
  * DIAGNOSTIC 3：把 `leaf` 固定、只让**块数据**变动 ⇒ 余定义域又变回固定 ✓（**出路**）。
* `_scripts_tmp/w16a_probe2.lean` / `w16a_probe5.lean` / `w16a_probe6.lean`：
  路径 ①/③ 的最小复现（都在同一处报同一个 error）✗。

## 7. 冻结基线（**保证下行有界**）

`Phylo/Stat/BlockModelRhoAE.lean`（**320 行**，md5 `b613d62c3894d6b736536d1cbda36e1a`）：

* **单文件门**：`lake env lean` → **`exit 0`，stdout **0 字节**，stderr **0 字节** ✓**
* **`lake build`**：**3867 jobs，exit 0** ✓
* **`#print axioms`**（7 条全查）：**全部恰 `[propext, Classical.choice, Quot.sound]`** ✓
* **文本级扫描**：`sorry` 0 · `axiom` 0 · `native_decide` 0 · `if_pos/if_neg` 0 · `Set.mem_setOf_eq` 0 ✓
* 已证 9 条：`BlockR`（物种树侧与块数据并列的结构）· `BlockR.toRaw_ofRaw` · `BlockR.ofRaw_toRaw`
  （双射，两条 `rfl`）· `instMeasurableSpaceBlockR` · `measurable_toRawR` · `measurable_ofRawR` ·
  **反空洞** `blockR_nonempty` · **块测度** `blockRPMeasure` ＋ **概率测度实例** ·
  **块样本** `blockRSample`（无穷乘积）＋ **概率测度实例** · **边缘律** `blockRSample_map_eval`
* 副本：`_scripts_tmp/FROZEN_BlockModelRhoAE_320lines.lean`（md5 同上）

## 8. ★★★ 第 ② 件的**已推好的归约**（交给下一位，省一轮推导）

> 状态：**未实施**（第 ① 件已完整交付）。下面是**已经手推清楚**的路线 ＋ **类型已对齐**的关键点。

### 9.1 ★ 已就位的接口（`BlockModelRhoAE2.lean`，全部已证）
```lean
blockWR_eq_blockW  : blockWR M C T bb = blockW M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 T (blockRToBlock bb)
blockLR_eq_blockL  : blockLR M C bb   = blockL M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 (blockRToBlock bb)
siteWR_eq_siteW    : siteWR M C T bb i = siteW M C bb.sp.1 bb.sp.2.1 bb.sp.2.2 T (blockRToBlock bb) i
blockRToBlock_thetaOf : BlockR.thetaOf bb = Block.θOf (blockRToBlock bb)
blockWR_dirac_W / blockLR_dirac_W / blockRToBlock_dirac / blockRToBlock_thetaOf_dirac   -- 门 5
```

### 9.2 ★★ 关键：**测度的嵌套已经对齐**（这一点省掉 `Measure.prod_assoc` 搬运）
`blockRPMeasure M C ρ νL` 定义为
```
Measure.map BlockR.ofRaw (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
```
而 `BlockR.Raw = sp × rest`，`rest = ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)`
—— **与 `BlockModelAE.Block` 的生空间逐字同型** ✓。
⇒ 故 `ρ.prod (restMeasure)` 的**第二分量测度** 就是 `BlockModelAE.blockMeasure` 里用的那个
`((σ).prod νL).prod ratePi`（**同一形状、同一类型**）✓
⇒ 于是 `BlockModelAE.blockW_integral` **可以逐字搬用**，不需要任何结合律搬运 ✓。

### 9.3 归约链（`∫ blockWR ∂(blockRPMeasure ρ νL)`）
1. `integral_map`：`= ∫ p : sp × rest, blockWR T (BlockR.ofRaw p) ∂(ρ.prod restMeasure)`；
2. `blockWR_eq_blockW`（定义层）：`blockWR T (ofRaw (sp, r)) = blockW M C sp.1 sp.2.1 sp.2.2 T (Block.ofRaw r)`；
3. `MeasureTheory.integral_prod`（拆第一分量）：
   `= ∫ sp, (∫ r, blockW M C sp.1 sp.2.1 sp.2.2 T (Block.ofRaw r) ∂restMeasure) ∂ρ`；
4. 内层 `integral_map` **反向** ＋ **`BlockModelAE.blockW_integral`**（固定物种树 `sp`）：
   `= ∫ sp, (∫ l, ((l:ℕ):ℝ) ∂νL) * expWeight (kingmanMSCMeasure (Measure.dirac sp)) τd M.Abar T ∂ρ`；
5. 提出常数：`= (∫ l, ((l:ℕ):ℝ) ∂νL) * ∫ sp, expWeight (kingmanMSCMeasure (Measure.dirac sp)) τd M.Abar T ∂ρ`。

### 9.4 ★★★ 剩下的**唯一实质引理**（「Dirac 混合 ＝ 混合」）
```lean
theorem integral_expWeight_dirac_mix (M : SiteRateModel)
    {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)} [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    (∫ p, expWeight (kingmanMSCMeasure (Measure.dirac p)) kingmanMSCTopoSym.τd M.Abar T ∂ρ)
      = expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T
```
**证明骨架**（两边都化到 `∫ q, G (toKingmanΘ q) ∂(ρ.prod σ)`，`σ := (sojournLaw 2).prod (sojournLaw 2)`，`G θ := ∑ T', τd θ T' * M.Abar θ T' T`）：
* 右：`expWeight` 展开 = `∫ θ, G θ ∂(map toKingmanΘ (ρ.prod σ))`
  `= ∫ q, G (toKingmanΘ q) ∂(ρ.prod σ)`（`integral_map` ＋ `measurable_toKingmanΘ`）
  `= ∫ sp, ∫ v, G (toKingmanΘ (sp, v)) ∂σ ∂ρ`（`integral_prod`）；
* 左：逐项 `kingmanMSCMeasure (dirac sp) = map toKingmanΘ ((dirac sp).prod σ)`
  ⇒ `expWeight (kingmanMSCMeasure (dirac sp)) … = ∫ v, G (toKingmanΘ (sp, v)) ∂σ`
  ⇒ `∫ sp, (…) ∂ρ` ＝ 同一个二重积分 ✓（`integral_prod` 反向）。
* **可积性**（`integral_prod`/`integral_map` 要的前提）：由**箱体先验**供给 ——
  `CASTERRateBoxAE.abarHint_integrable_of_boxParam`（`G` 关于 `kingmanMSCMeasure ρ` 可积）
  ＋ `ae_boxTheta_of_ae_boxParam` ＋ `abs_hint_le_one`（`|G θ| ≤ 1` 在 `BoxTheta` 上）✓。

### 9.5 组端到端（与 `BlockModelAE.abar_caster_statisticallyConsistent_kingman_ae_blocks` 同形）
`blockL_integral_R`（`= ∫ l, ((l:ℕ):ℝ) ∂νL`，可直接搬 `BlockModelAE.blockL_integral` 的 `integral_fun_fst`/`_snd` 两步）
⇒ `blockW_div_blockL_R`（商 ＝ `expWeight (kingmanMSCMeasure ρ) τd M.Abar T`，用 `integral_LIdx_pos` 消分母）
⇒ **`abarTopoIdealBox`（W15a 已有）的 `W`** 逐字相同 ⇒ 套 `BlockModelAE.block_emp_tendsto_ae` 的五条假设
（`blockR_iIndepFun` ✓ / `blockR_identDistrib` ✓ / `blockR_L1` ✓ / 可积性由箱体先验给 / `hlim` 即上一步）
⇒ 得到**不假设 `hconv`** 的端到端定理 `…_ae_blocks_box`。

### 9.6 ★ 需要的**既有名字**（第 ② 件用，已定位）
`kingmanMSCMeasure_dirac_eq_map`（`BlockModelAE:598` 处用过，`MSCKingmanMeasure`）·
`measurable_abarHint` / `measurable_abarHint`（`MSCKingmanMeasure`）·
`abs_hint_le_one` / `abarHint_integrable_of_boxParam` / `ae_boxTheta_of_ae_boxParam` / `BoxParam`（`CASTERRateBoxAE`）·
`expWeight` / `geneExpect`（`CASTERBridge` / `CASTEREngine`）·
`MeasureTheory.integral_prod` / `integral_prod_mul` / `integral_fun_fst` / `integral_fun_snd`

## 9. 冻结点状态（★ 落盘请以此为准）

* **交付件**：`Phylo/Stat/BlockModelRhoAE2.lean` —— **483 行**，
  md5 **`44e5d9913436496adc26be17cd25a751`**
  （镜像备份：`_scripts_tmp/VERIFIED_BlockModelRhoAE2_483lines.lean`，md5 同上 ✓）
* **不登记**：`Phylo/Stat/BlockModelRhoAE.lean`（320 行 / `b613d62c3894d6b736536d1cbda36e1a`，
  被 `RhoAE2` 完全覆盖，**勿落盘**）
* 单文件门 / `lake build` / `#print axioms` / 文本级扫描 —— **全绿**（见 §7）✓

## 10. 诚实边界

1. 即使 §4 打通，**第 ② 件**（不假设 `hconv` 的端到端）**仍有独立风险**：
   `block_hlim`（识别等式）与 `block_L1` 的**块层**版本需要在 `BlockR` 上重做
   `blockW_integral` / `blockL_integral` / `blockW_div_blockL` 三条积分恒等式；
   它们的**陈述**不涉及依赖族（都是 `ℝ` 值积分），**预期不受本卡点影响** ✓，
   但工作量**另计**（估 60–120 分钟）。⇒ **第 ② 件是否在射程内：方向上在，时间上不保证。**
2. 本卡点**不是数学内容为假** —— 命题为真，纯属**形式化表述受阻** ✓（这一点已用探针确证）。
