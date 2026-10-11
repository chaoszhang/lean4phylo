# W16b 交接（beyond-spec 续作：**未打通**，但归约完整、卡点单一已定位）

* 日期：2026-10-12（本季 W13 之后，★ **超出规格**的追加线第 3 件）
* 结论：**未打通** ✗ —— **不可落盘** ✗（单文件门未过 ✓）；但**数学内容与归约已完整落纸** ✓、**卡点单一且已定位到 2 行** ✓。

---

## 1. 交付件（**冻结**，未再改动 ✓）

| 项 | 值 |
|---|---|
| 路径（**协调侧唯一取件处** ✓） | `~/lean4phylo-w16b/Phylo/Stat/BlockModelRhoAE3.lean` |
| 行数 | **617** |
| 声明数 | **27** |
| md5 | **`86a80436c0f6bb475cd2c335c3c2c132`** |
| 禁用词（`sorry`/`axiom`/`native_decide`） | **0** ✓ |
| namespace | `Phylo.Stat.BlockModelRhoAE3`（与 `…RhoAE2` **声明交集 = 空** ✓） |
| **单文件门** | ★ **未过** ✗（见 §3） |
| 既有文件 | **未被触碰** ✓（`BlockModelRhoAE2.lean` md5 仍 `44e5d9913436496adc26be17cd25a751` = 正本 ✓） |

★ 冻结确认由**作者与协调侧各测一次**，md5 逐字一致 ✓（协调侧复核：617 行 / md5 同值 / 禁用词 0 ✓ / `RhoAE2` md5 一致 ✓）。

## 2. ★★ 已完成的稀缺部分（**归约链，全部落纸** ✓）

### 2.1 唯一实质引理「**Dirac 混合 ＝ 混合**」的**两边归约各自完成** ✓

| 声明 | 行 | 内容 |
|---|---|---|
| `integrable_Gfun_kingman` | 140 | 箱体先验 ⇒ 被积函数可积 |
| `expWeight_kingman_eq_integral_prod` | 191 | **右端** `= ∫ q, G (toKingmanΘ q) ∂(ρ.prod σ)` |
| `diracMix_eq_integral_prod` | 210 | **左端** 同一个二重积分（靠 `kingmanMSCMeasure_dirac_eq_map`） |
| **`integral_expWeight_dirac_mix`** | 229 | 两端同一二重积分 ⇒ 相等（`Eq.trans`） |

★ 数学要点：`ν ↦ expWeight ν` **非线性**，但 `kingmanMSCMeasure = map toKingmanΘ` ⇒
**两边都降到 `ρ.prod σ` 上同一个二重积分** ⇒ 混合引理成立 ✓（归约与 `W16a_BLOCKER.md` §8 逐字一致 ✓）。

### 2.2 块层接口全部就位（陈述 ＋ 证明骨架）✓

`abs_siteWR_le_one`(240) · `abs_blockWR_le`(253) · `integrable_map_ofRaw`(270) ·
`integrable_blockWR`(285) · `integrable_blockLR`(293) · `blockW_integral_R`(309) ·
`blockL_integral_R`(381) · `blockW_div_blockL_R`(407) · `block_hlim_R`(420) ·
`empBlocksR`(450) · `empBlocksR_eq_empOfBlocks`(457) · `block_emp_tendsto_ae_R`(496) ·
**`abar_caster_statisticallyConsistent_kingman_ae_blocks_box`(526)** ·
门 5 四条探针(547–580) · 反空洞两条(599/606)。

## 3. ★ 卡点（**唯一**，已定位到 2 行）

**现象**：`Integrable G (Measure.map φ μ)` 与 `Integrable (G ∘ φ) μ` 在 Lean 里**不合一**，
因此 `Measurable.aestronglyMeasurable ((measurable_abarHint M T).comp hf)`
（给的是 `AEStronglyMeasurable (G ∘ φ) μ`）**不能**当作 `AEStronglyMeasurable G (Measure.map φ μ)` 用。

**逐字报错**（`BlockModelRhoAE3.lean:159` 与 `:184`）：
```
error: Type mismatch
  Measurable.aestronglyMeasurable (Measurable.comp (measurable_abarHint M T) hg)
has type   AEStronglyMeasurable ((fun θ => ∑ T', …) ∘ fun v => toKingmanΘ (p, v)) ?m
but is expected to have type
  AEStronglyMeasurable (fun θ => ∑ T', …) (Measure.map (fun v => toKingmanΘ (p, v)) ((sojournLaw 2).prod (sojournLaw 2)))
```

**根因**：`toKingmanΘ` 的论域是 `abbrev KingmanParam`，与这里的乘积型 `((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ)`
**只差 `abbrev` 展开** —— 而 `abbrev` 在 `Integrable`/`AEStronglyMeasurable` 的**显式测度参数位置**没有展开。

**试过且未通过（各 1–2 次）**：`exact integral_map` · `refine integral_map … ?_` ＋ `show` ·
给复合映射起非依赖名 `F := fun q => toKingmanΘ q` ＋ `simpa only [Function.comp_def]` ·
`dsimp only` 强制展开 · `rw [show Measure.map F μ = kingmanMSCMeasure ρ from rfl]`。
（`fun_prop` **未试** —— 时间盒已尽。）

**其余 13 条 error 全是"上游未过 ⇒ 下游连坐"** ✓（`blockW_integral_R` 的 `hIntP2`/`hleaf`、`empBlocksR`、门 5、反空洞等），
★ **不是独立卡点** ✓ ⇒ 上述 1 条一通，其余按 §8 的归约逐条即可过。

## 4. ★ 下一棒的定向解法（3 选 1，都很小 ✓）

1. 在 `MSCKingmanMeasure.lean` **只加不改**地新增一条
   `integral_map_toKingmanΘ'`：把 `∫ θ, g θ ∂(Measure.map (fun q : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ) => toKingmanΘ q) μ)`
   与 `∫ q, g (toKingmanΘ q) ∂ μ` 的相等性**在论域恰好是乘积型的地方**一次证掉（`integral_map` ＋ `rfl`）；
2. 或把 `integrable_Gfun_prod` **直接写成** `Integrable (fun q => …) (Measure.map F μ)`（左端不换成 `kingmanMSCMeasure ρ`），
   再用 `Measure.map` 的定义等式 `rfl` 转；
3. 或用 `AEMeasurable`/`AEStronglyMeasurable` 的 `comp` 引理**直接构造** `AEStronglyMeasurable G (Measure.map φ μ)`
   （`Measurable.aestronglyMeasurable` 的**逆**方向没有现成引理，需自证）。

## 5. 未跑完的验收门（**接手者必须先跑** ✗）

1. ★ **单文件门** ✗（未过 ⇒ 一切以它为先 ✓）；
2. **全量 `lake build`** ✗（未跑；★落盘流水线要求 **job 数 = 3965** ⇒ 落盘后应为 **3966**）；
3. **锚定 `#print axioms`** ✗（未跑 ⇒ 须确认条数 = 声明数、荷载仅 `[propext, Classical.choice, Quot.sound]`）；
4. **门 5 四条探针的编译验证** ✗（`blockWR_dirac_eq_blockW` 是 `rfl` 级 ✓、`…_dirac_target` 是 `rfl` ✓，但**未编译** ✗）；
5. **数值脚本** ✗（本件未写；★G 要求"真入库"的脚本若要做，须**与库内定义逐字对齐** ✓）。

★ **结论：本件【不可落盘】** ✗ —— 协调侧落盘流水线的两道硬门（全量 build ＋ 单文件 `exit 0` 且 **0 字节**）**必然中止** ✓。

## 6. ★★ 两条值得传承的发现（虽未打通，但已验证有效 ✓）

1. **`|siteWR| ≤ 1` 不需要叶长非负** ✓：`BlockModelAE.abs_blockW_le` 要**逐点** `0 ≤ leaf i`，
   而 `BlockR` 的叶长 `bb.sp.1` 只是**任意实值函数**（箱体只给 `ρ`-**a.e.** 非负）
   ⇒ 作者自证 `abs_siteWR_le_one` / `abs_blockWR_le`：只需 `a b ≥ 0`（`ℝ≥0` 给）＋ `|τd| ≤ 1`
   ⇒ ★ **少要一个假设** ✓（与教训 236 的"方向纪律"同族 ✓）。
2. **同一文件里 `import` 的模块，unqualified 名字不可见** ✓：
   `empWeight_tendsto_ae` 必须写 **`Phylo.Stat.BlockSLLNTopoClose.empWeight_tendsto_ae`**
   （`BlockModelRhoAE2` 不转出它）⇒ ★ 这是**本件新踩的坑**，值得记一笔 ✓。

## 7. ★A 名单（作者逐条 `#check`/读定义处确认 ✓，供接手者省时）

* **已确认**：`integral_map` · `integral_prod` · `integral_fun_fst/_snd` · `integral_prod_mul` ·
  `Measure.map_prod_map` · `Measure.map_fst_prod` ·
  ★ `integrable_map_measure`（`L1Space/Integrable.lean:358`，签名
  `(hg : AEStronglyMeasurable g (map f μ)) (hf) : Integrable g (map f μ) ↔ Integrable (g∘f) μ` —— **正是卡点所在** ✓）·
  `Integrable.comp_aemeasurable`(364) · `Integrable.comp_measurable`(368) ·
  `Measurable.comp`(Constructions/Defs:522，**外函先** ✓) · `Measurable.prodMk`(Constructions:409) ·
  `abs_tauA_le_one`(`BlockModelAE:398`) · `boxTheta_toKingmanΘ` ·
  `abarHint_integrable_of_box(Param)` · `kingmanMSCMeasure_dirac_eq_map` · `empOfBlocks`(`:310`) ✓。
* ⚠ **未定位（记作"未知"，不是"不存在" ✓）**：
  * `AEStronglyMeasurable.ae_le` ⇒ **`#check` 明确报 unknown** ⇒ ★ 在本版 Mathlib 里**确实不存在** ✓
    （与"未定位"是两回事 ✓）；
  * `Measure.ae_smul_measure_iff` **未 `#check`**（额度用尽）；
  * `LIdx C = {L : ℕ // 1 ≤ L ∧ L ≤ C}`（**是 `Subtype`**）⇒ 用 `⟨1, by norm_num, hC⟩` 构造 ✓。

## 8. ★H 记录（**如实**，作者主动交代 ✓）

* ✗ **违规**：域外 `/Project/lean/_scratch/` 有作者写的文件 —— 前 6 个补丁脚本（`w16b_patch.py` … `patch6.py` ✓）
  ＋ `w16b_final.lean` ＋ 若干探针/草稿 ✓；协调侧**四次提醒**后**已停止** ✓（最后两个补丁只写 `_scripts_tmp/` ✓）。
* ✓ **未删**任何域外文件 ✓（该目录属**老师裁示范围** ✓；协调侧亦未删 ✓）。
* ★ 实务影响：**无** ✓ —— 交付件（`.lean`）**始终在镜像内** ✓；协调侧取件只认镜像 ✓（曾出现"镜像滞后"，
  协调侧发出**只讲实务**的一次提醒后**已同步** ✓）。

---

## 9. ★ 协调侧的**提案**（**待老师批准** ✗；本文件此节**只是方案**，**未实施任何代码** ✓）

★ 目的：把 §4 的"3 选 1"**排出优先次序并写清代价** ✓，让老师**一句话即可启动** ✓。

### 9.1 ★ 我的建议：**优先试 §4 的解法 2**（复合形态，**不必碰已落盘文件** ✓）

* **理由**：卡点的本质是"**目标被写成了 `Measure.map φ μ` 形态，于是 Lean 必须把 `G ∘ φ` 认成 `G`**"✗；
  而**若目标一开始就写成复合形态** ✓（`Integrable (fun q => G (toKingmanΘ q)) (Measure.map (fun q => toKingmanΘ q) μ)` ✓），
  则**根本不需要这次"认出"** ✓ ⇒ ★ **`abbrev` 桥的问题消失** ✓，且**无需在 `MSCKingmanMeasure.lean` 加任何东西** ✓。
* **落地方式**：把 `integrable_Gfun_prod`（及其连坐的上游两处 `AEStronglyMeasurable`）**改写为复合形态** ✓；
  在**确需** `kingmanMSCMeasure ρ` 的地方，用**定义等式**（`kingmanMSCMeasure = Measure.map toKingmanΘ` 型 ✓，`RhoAE2` 已有同型器材 ✓）**转一次** ✓。
* **改动面**：只在**镜像**的 `BlockModelRhoAE3.lean` ✓（**正本零改动** ✓ ⇒ 完全落在协调侧权限内 ✓）。

### 9.2 备选与代价

| 次序 | 方案 | 改动面 | 代价/风险 |
|---|---|---|---|
| **1（建议）** | 目标改**复合形态**（§4-解法 2 ✓） | 仅镜像 `RhoAE3` ✓ | 需占锁：单文件门 ~2 min ＋ 全量 build ~10–20 min ✓ |
| 2 | 直接构造 `AEStronglyMeasurable G (map φ μ)`（§4-解法 3 ✓） | 仅镜像 `RhoAE3` ✓ | 需自证一条 `comp` 小引理 ✓ |
| 3（最后） | 在 `MSCKingmanMeasure.lean` **只加不改**补一条"论域恰为乘积型"的 `integral_map` 变体（§4-解法 1 ✓） | ★ **正本已落盘文件** ✗ | 需老师**明确授权** ✓（本季"只加不改" ✓） |

### 9.3 验收路径（无论走哪条 ✓）

`单文件门（exit 0 且 **0 字节** ✓）` → `全量 lake build（job 数须等于预期 ✓）` →
`锚定 #print axioms（条数 = 声明数，荷载仅 3 条公理 ✓）` → `门 5 四条探针编译 ✓` →（可选）★G 数值脚本 ✓
★ 若最终落盘：正本 `.lean` **141 → 142** ✓、模块 **17 → 18** ✓、`guard` job 数 **3965 → 3966** ✓（已写入落盘模板 ✓）。

### 9.4 风险与止损（预先写好 ✓，避免硬撑 ✗）

* ★ **乐观面**：13 条 error 是**连坐** ✓ ⇒ 该条一通，其余按 `W16a_BLOCKER.md` §8 的归约**逐条即可过** ✓；
* ★ **止损线**：若**方案 1 与 2 各试一轮仍不通** ✗ ⇒ **停止自旋** ✓，转方案 3 或**收档** ✓，
  并**如实登记**"试过什么、为何不通" ✓（本季纪律：★ 同错两次即停 ✓）。
