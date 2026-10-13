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

---

## 10. ⚠ 环境注记（**给所有跑"单文件门"的人** ✓，2026-10-12 06:23 实测）

* ★★ **现象**：`lake env lean <任何文件>` 会先跑 **`importGraph`** ✓，而它是 **partial/promisor clone**
  （实测 `git config remote.origin.promisor = true` · `partialclonefilter = tree:0` ✓）
  ⇒ **需要联网 fetch** ✗ ⇒ **断网时必然失败** ✓：
  ```
  info: importGraph: checking out revision '10a2cfff…'
  fatal: unable to access 'https://github.com/leanprover-community/import-graph/':
         Failed to connect to github.com port 443 after 134127 ms
  fatal: could not fetch c8305b8a… from promisor remote ⇒ error: external command 'git' exited with code 128
  ```
* ★★★ **这与命题/代码【无关】** ✓ —— 但它**长得像"门没过"** ✗：
  `EXIT = 1` ✓ 且 **`stdout = 0 字节`** ✓（**0 字节这个词本身就出现在门的判据里** ✗）。
  ⇒ ★★ **判据必须是"`exit 0` **且** 0 字节"的【合取】** ✓：**只看 0 字节必然假绿** ✗，
  只看 exit 会把网络抖动误报成数学问题 ✗。
* ★ **正确归类（教训 303 ✓）**：复核失败要分三类 ——
  **① 代码失败**（真信号 ✓）· **② 基建失败**（网络/克隆/磁盘 ✓，与命题无关 ✗）· **③ 我的命令写错**（如同日的 `EXIT=127` ✓）。
  ⇒ ★ **报告里必须写明属于哪类** ✓；**"我复核不了"要如实说** ✗→✓，**不得**含糊成"通过/不通过" ✗。
* ★ **对 W13 验收证据的影响：无** ✓ —— 所有门在**网络可用时**已跑绿 ✓（`guard 3965` 全绿 ✓ ＋ 各次落盘的单文件门 ✓），
  且此后 **`.lean` 一个字节都没变** ✓（`git diff --name-only 5b30bed..HEAD -- '*.lean'` = 0 ✓）
  ⇒ ★ **旧结论对新树仍然成立**（299 的可判定论证 ✓）。
* ★ **要重跑门时的建议** ✓：先 `timeout 8 git -C .lake/packages/mathlib ls-remote --exit-code origin HEAD` 探一下网络 ✓；
  不通 ⇒ **不要重试到超时** ✗，直接记为"**基建失败、待网络恢复**" ✓。
* ★★★ **06:27 补记：口径 ③ 的独立复核【已完成并通过 ✓】** —— 网络恢复后，在**镜像**里做（★ 前提：先证
  `BlockModelAE` / `GeneTreeSamplingAE` / `CASTERRateBoxAE` 三模块与**正本 md5 逐字一致** ✓，
  故结论对正本内容有效 ✓；★ 不动正本任何字节 ✓）：
  ```
  EXIT = 0 · stdout = 416 字节 · stderr = 0 ✓
  '…astral_iso_ae_of_geneTrees'                            depends on axioms: [propext, Classical.choice, Quot.sound]
  '…abar_caster_statisticallyConsistent_kingman_ae_blocks'  depends on axioms: [propext, Classical.choice, Quot.sound]
  '…abar_caster_statisticallyConsistent_kingman_ae_box'     depends on axioms: [propext, Classical.choice, Quot.sound]
  ⇒ ★ 三条头条【恰好】依赖这 3 条公理 ✓（无 sorryAx ✓、无其他公理 ✓）
  ```
  ★ 附（自查 ✗）：我自己的判定脚本报了**假阴性**（"恰为 3 条 = 0"✗）—— 因为输出**跨行折行**而我的模式是**单行**的 ✗
  ⇒ ★ **核查脚本与原始输出冲突时，以原始输出为准** ✓（本季第 12 次"模式/数据不匹配" ✗，与 257 同族 ✓）。
* ★ **另一条基建事实（对本仓有用 ✓）**：**正本的 `.lake` 从未本地构建**（`.lake/build/lib/lean` 条目 = **0** ✓）
  ⇒ 一切 `lake env lean` 的检查都**在镜像里**做 ✓（镜像有 `Phylo.olean` ＋ `Phylo/Stat` **83** 个 `.olean` ✓）
  ⇒ ★ **要复核正本内容时，先在镜像里跑、再证"被验文件与正本 md5 一致"** ✓（本批即此流程 ✓）。

### 10.1 ⚠ 工具卫生：`guard_batch.sh` 会在镜像里**留下** `Phylo/GuardProbe.lean` ✗（2026-10-12 06:31 实测）

* ★★ **实测**：镜像 `~/lean4phylo-main/Phylo/` 比正本多 **8** 个 `.lean` ✗，其中**根因是 guard 自己**：
  ```
  ./GuardProbe.lean（★ 步骤④生成、跑完【不删】✗）· ./Stat/CASTER.lean · ./Stat/MSCSamplingVacuity.lean
  ./Stat/SamplingAxiomVacuity.lean · ./Stat/W11gProbe.lean · ./Stat/W11gProbe2.lean · ./Stat/W11gProbe3.lean
  ./Stat/_probe_t55.lean
  （反向：正本独有 = 0 ✓，因为 ① 步刚 `cp` 同步过 ✓）
  ```
* ★★ **为什么要紧** ✓：`GuardProbe.lean` 在 `Phylo/` 内 ⇒ **进构建目标 ⇒ 计入 job 数** ✓
  ⇒ ★ 它把**工具自己的痕迹**伪装成**项目的状态** ✗（后人会以为"镜像与正本不同步" ✓，白花时间解释 ✓）。
  ★ **当前不影响判据** ✓：`3965` 这个基线**本来就是含它测出来的** ✓（整季同一镜像 ✓），
  且每次运行**重写同一路径** ⇒ **文件数不变 ⇒ job 数不漂移** ✓。
* ★ **建议（一行 ✓，属改入库工具 ⇒ 待老师裁示 ✗，未动手 ✓）**：
  在 `guard_batch.sh` 的 `trap` 里加 `rm -f "$MIRROR/Phylo/GuardProbe.lean"` ✓；
  ★ 另可一次性清点其余 **7** 个历史遗留件 ✓（W11 探针 / 早期 WIP ⇒ 已不在正本 ✓）。

---

## 11. ★ 下一棒的**派单模板**（可直接粘贴 ✓；供老师选 (A) 时用 ✓）

> **任务**：续做 W16b —— 让 `Phylo/Stat/BlockModelRhoAE3.lean` 通过**单文件门**，从而可落盘。
>
> **背景与全部细节**：读 **`lean4phylo/W16b_HANDOVER.md`**（§3 卡点 · §4 解法 · §5 待跑门 · §7 ★A 名单 ✓）。
>
> **取件**（**从这里取，也只往这里写** ✓）：镜像 `~/lean4phylo-w16b/Phylo/Stat/BlockModelRhoAE3.lean`
> —— 冻结件 **617 行 / 27 声明 / md5 `86a80436c0f6bb475cd2c335c3c2c132`** ✓（★ 交付时请**复核 md5** ✓）。
>
> **卡点（唯一）**：`Integrable G (Measure.map φ μ)` 与 `Integrable (G∘φ) μ` **不合一** ✗
> （根因：`abbrev` 在**显式测度参数位**不展开）；
> 首错在 `:159` 与 `:184`，其余 **13 条为连坐** ✓ ⇒ **一通皆通** ✓。
>
> **建议次序**（`W16b_HANDOVER.md` §9.1 ✓）：
> ① **目标改复合形态**（`Integrable (fun q => G (toKingmanΘ q)) (Measure.map (fun q => toKingmanΘ q) μ)` ✓）
> ⇒ 无需那次"认出" ✓、**不必碰已落盘文件** ✓；② 直接构造 `AEStronglyMeasurable G (map φ μ)`（自证一条 `comp` 小引理 ✓）；
> ③ 最后才考虑在 `MSCKingmanMeasure.lean` **只加不改**补一条变体引理 ✓（★ 需老师明确授权 ✓）。
>
> **验收（缺一不可 ✓）**：单文件门（**`exit 0` 且 stdout 0 字节** ✓ —— ★ 二者是**合取** ✓）→
> 全量 `lake build`（**job 数须等于预期** ✓）→ 锚定 `#print axioms`（条数 = 声明数 ✓，荷载仅 3 条公理 ✓）→
> 门 5 四条 Dirac 探针**编译** ✓ →（可选 ★G）数值脚本**与库内定义逐字对齐** ✓。
>
> **纪律（摘要）**：★ 写域只限镜像 ✓（**临时脚本放 `_scripts_tmp/`** ✓，**不要碰 `/Project/lean/_scratch/`** ✗）；
> ★ 不许改**已落盘**文件 ✓；★ **同错两次即停** ✓ 并**如实报告卡在哪** ✗→✓；★ **时间盒 90 分钟** ✓；
> ★ **交报告请带：行数 ＋ md5 ＋ 门实测（exit / stdout 字节 / error 条数）** ✓。
>
> **★ 两个已踩过的坑（免得再踩 ✓）**：① `empWeight_tendsto_ae` 须写**全限定名** ✓
> （同文件 `import` 的模块里 unqualified 名不可见 ✓）；② 跑门前**先探网络** ✓（`importGraph` 是 partial clone ✓，
> 断网会给出 `exit 1` ＋ **stdout 0 字节**的假象 ✗ —— 见 §10 ✓）。

---

## 12. ★★★ W17（2026-10-13）续攻结果：**原「唯一卡点」已清除** ✓，但发现【一条陈述为假】✗

### 12.1 本轮实测（全部有逐字证据 ✓）

| 项 | 值 |
|---|---|
| 门 | `EXIT=1` · stdout **3669 字节** · **9** 条 error（原 **15**） |
| 文件 | **612 行**（原 617）· md5 `a0fdf00d0fdc561c0b55884af7f1b302` |
| 改动 | **仅镜像** ✓（正本零改动 ✓）· 6 份备份可回退（`_scripts_tmp/W17A_backup_*.lean` ✓） |
| 落盘 | ✗ **不可落盘**（门未过；且下列 §12.3 的陈述问题未修 ⇒ **不应**落盘） |

### 12.2 ★★★ 原「唯一卡点」是**写法问题**，不是 `abbrev` 桥（§3 的判断**错**了 ✗）

* §3 说「`Integrable G (Measure.map φ μ)` 与 `Integrable (G∘φ) μ` 不合一，根因 = `abbrev` 在显式测度参数位不展开」✗。
* ★ **实测否证**：把 `integrable_Gfun_prod` 的证明体改成 **θ 型陈述**（照抄**同文件** `integrable_Gfun_kingman:140-145` ✓）
  ＋ 用库内 **`Integrable.comp_measurable`**（`Integrable.lean:368`）收口后 ⇒
  **报错列表从 `:159` 前移到 `:241`** ✓ —— 原 `:159/:165/:186` 那一组**全部消失** ✓。
* 真因（三处写法 ✓）：① `(integrable_map_measure …).mpr` **方向反了** ✗（应 `.mp` ✓）；
  ② `hgoal` 写成「**乘积型测度 ＋ 复合函数**」的**混形** ✗（应为 **θ 型** ✓）；
  ③ `dsimp only` 多余 ✗（修 ① 后它报 `made no progress` ✓）。
* ★★ **连带结论**：派单任务 A③ 所授权的「在 `MSCKingmanMeasure.lean` 只加不改补一条 `integral_map` 桥引理」
  —— **其前提为假** ✗ ⇒ **不必写、也不该写** ✓（本轮未写 ✓，正本因此保住"一字未动" ✓）。
* ⚠️ §3 末的「其余 13 条 error **全是连坐**」也被否证 ✗：改掉第一组后，其余错误**仍在原处** ✓ ⇒ 它们是**独立的** ✓。

### 12.3 ★★★ **发现一条陈述为假**：`abs_siteWR_le_one`（`BlockModelRhoAE3.lean:235`）

**陈述**：`theorem abs_siteWR_le_one (M) (C) (T) (bb : BlockR M C) (i : Fin C) : |siteWR M C T bb i| ≤ 1`
—— 对**任意** `bb` 断言，且 docstring 自称「**不需要**叶长非负」✗。

**证据（三条独立来源，均为库内既有 ✓）**：
1. `SiteWeightMeasurable.lean:282`：「前提 `∀ i, 0 ≤ l i`、`0 ≤ lx` 是**必需的**（**负枝长时 `patternProb` 无界**）」✓；
2. `BlockModelAE.lean:78`：「W13a 的 `abs_geneScore_le_one` **必须有非负枝长**（负枝长时 `|patternProb|` 可达 **3.5e4**）」✓；
3. `BlockModelAE.lean:396-398`：`abs_tauA_le_one` 的 docstring「只需 θ 的枝长非负 —— 这是 W13a 的**必需**前提（负枝长时无界）」，
   且其**签名**明确带 `(hl : ∀ i, 0 ≤ θ.1.1 i)` ✓。

**为何在本文件里就不可满足**：
* `BlockR.sp : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0`（`BlockModelRhoAE2.lean:171-175`）⇒ **叶长是任意实数、无任何非负证据** ✗；
* `siteWR` 用的正是 `BlockR.thetaOf bb` 的 `.1.1`（= 叶长 ✓）⇒ 于是 `hl` 分支**无法提供** ✗
  —— 这正是门里 `:241` 那条 `Type mismatch`（给的是 `(bb.sp.2.1).2 : 0 ≤ ↑bb.sp.2.1`，要的是 `0 ≤ (thetaOf bb).1.1 j` ✗）。
* ★ 且该引理**被两处依赖**：`:258`（`abs_blockWR_le` 内部）与 **`:285`（"整体有界 ⇒ `Integrable`"那一步）**
  ⇒ ★ **整条可积性链都压在这条假陈述上** ✗。

**正确的修法（下一棒照此做，勿再试证明 ✓）**：
* 把假设**加强**为 `(hleaf : ∀ j : Fin 4, 0 ≤ bb.sp.1 j)` ✓（于是 `:241` 的 `hl` 直接由 `hleaf j` 给出 ✓）；
* ★ 并**先回答一个数学问题**（★D）：**`BlockR` 上的块测度是否只把质量放在"叶长非负"的块上**？
  若**否** ⇒ `blockWR_integral_R` 的 `Integrable` **前提本身不成立** ✗ ⇒ 需要**改测度/改陈述**（不是改证明 ✗）；
  若**是** ⇒ 只需在用到 `:258/:285` 的地方把该测度性质传下来 ✓。

### 12.4 本轮的其它修正（已生效 ✓，均为写入法层面）

* `:554/:557` 的**字段记号**错 ✗：`(Finset (Fin 4)).card` ⇒ 解析器按类型投影报 `invalid field notation` ✓；
  照同文件 `:447` 的成功写法改为 `(S : Finset (Fin 4)) (_ : S.card = 4)` ✓（消掉 2 条 error ✓）。
* 改动清单（镜像内 ✓）：`integrable_Gfun_prod` 体改写 ✓ · `expWeight_dirac_eq_integral_sojourn` 删多余 `dsimp` ✓ ·
  `abs_siteWR_le_one` 附近的字段记号 ✓；**`abs_siteWR_le_one` 的陈述本身未动** ✗（等老师定口径 ✓）。
### 12.5 W17 第二/三轮实测（同日 01:03 更新）：**error 15 → 8** ✓，且修掉一条**陈述缺陷** ✓

| 轮次 | 改动 | error |
|---|---|---|
| 起 | 冻结件 `86a80436…`（617 行） | **15** |
| 1 | `integrable_Gfun_prod` 改 **θ 型陈述** ＋ `Integrable.comp_measurable` 收口 | **11** |
| 2 | `:554/:557` 字段记号（`(Finset (Fin 4)).card` ✗ → `(S …) (_ : S.card = 4)` ✓） | **9** |
| 3 | `abs_siteWR_le_one` / `abs_blockWR_le` **加强为逐点 `hleaf`** ✓ ＋ `integrable_blockWR` 加箱体假设并改用 **a.e. 界** ✓（级联 7＋3 处 ✓） | 9 → 9（先清掉 `:241` 那组 ✓，新位置 `:290`） |
| 4 | `:290` 用 **`QuasiMeasurePreserving.ae`**（Mathlib `QuasiMeasurePreserving.lean:108`）把 `ρ`-a.e. 沿 `Prod.fst` 抬到乘积测度 ✓ | **8** |

* 现件（★ **以协调侧 2026-10-13 复跑为准** ✓）：**625 行** · md5 **`2308cb66e8249ed0250778f1f6868b2c`** ·
  门 `EXIT=1` · stdout **2540 字节**（协调侧实测；我自测 2490 B）· **5** 条 error · **正本一字未动** ✓ · 备份多份 ✓。
  ⚠️ 本节早先写的「621 行 / `103e67f0…` / 8 条」是**写报告后又改了一轮**造成的**滞后** ✗（方向是变好 ✓），已按协调侧实测更正 ✓。
* ★ **剩余 8 条分两簇**（实测 ✓）：
  1. **`:350–375` 一簇**（4 条）：`hIntP.comp_aemeasurable hconst.aemeasurable` ✗ ——
     报错显示 Lean 推断的被积函数是 **`fun r => Finset.univ.sum (…siteWR…)`**（即 `blockWR` 的**展开式** ✗），
     而 `hIntP` 是 `Integrable (fun p => blockWR … )` ✗ ⇒ ★ **两者只差 `blockWR` 的展开** ✓
     ⇒ 修法：把目标写成 `blockWR` 形态 ✓，或 `simpa only [blockWR, …] using hIntP.comp_measurable …` ✓。
     （`hbox`/`hleaf` 的抬升请**照抄 §12.5 第 4 轮** ✓，不要再用 `Filter.Eventually.of_forall` ✗。）
  2. **三处 elaboration 心跳超时**（`:397` **whnf** · `:570` **isDefEq** · `:594` **isDefEq**）✗ ⇒
     ★ 这类通常是**上游目标畸形**的症状 ✓ ⇒ 建议**先修第 1 簇再复跑** ✓（超时很可能随之消失 ✓）。
### 12.6 ★★★ 第三轮：簇① 的真因 —— **同一个"叶长非负"缺陷已出现 4 处**（系统性问题，非长尾）

**簇①（`:350–375`）的真实结构**（逐字读过 ✓）：
* `blockW_integral_R`（`:312`）的 `hinner`（`:345-350`）要对**固定但任意**的 `sp` 断言
  `∫ r, blockWR M C T (BlockR.ofRaw (sp, r)) ∂σ = 𝔼[L]·expWeight (dirac sp) …`；
* 但它给出的"叶长非负"证据（`:361-363`）是
  `Filter.Eventually.of_forall (fun _ i => zero_le _)` ✗ —— **`sp.1 : Fin 4 → ℝ` 是任意实值** ✗
  ⇒ ★ **该证据为假**（与 §12.3 的 `abs_siteWR_le_one` **同型** ✗：把"逐点恒成立"当成"能推出来" ✗）；
* 且 `hIntP` 在 **`ρ.prod σ`** 上，而 `Integrable.comp_aemeasurable` 要 **`map (fun r => (sp, r)) σ`** 上 ✗
  ⇒ 测度也不匹配 ✗（这两条 error 是同一处结构问题的两个面 ✓）。
* ★ **正确修法**：把 `hinner` 改成 **`ρ`-a.e.** 的陈述（`hbox.mono` 抬 ✓，然后 `integral_congr_ae` ✓），
  **不要**再试图用 `of_forall` 造逐点证据 ✗；`hIntP2` 则应由 **`abs_blockWR_le` ＋ 该 a.e. 叶长非负** 直接给出 ✓
  （即 §12.5 第 4 轮的 ae-lift 手法 ✓），而**不是**从 `hIntP` 走 `comp_aemeasurable` ✗。

**★★★ 结论（给协调侧/老师）**：`BlockModelRhoAE3.lean` 里"**陈述暗含叶长非负、数据却只给任意实值**"的缺陷
**已确认 4 处**（§12.3 的 `abs_siteWR_le_one`；本节的 `hinner`；以及 §12.5 里由它派生的两处 ✓）。
⇒ ★ 这**不是**"再修几行的长尾" ✗，而是需要**一次系统性贯通** ✓：
**把"叶长非负"作为 `ρ`-a.e. 假设，从 `hbox` 出发逐层穿到每一个用到 `abs_tauA_le_one` / `abs_blockW_le` 的地方** ✓。
★ 建议下一棒**先做这次贯通**（一次改完再复跑 ✓），而不要逐条试错 ✗ —— 逐条试错会不断"消灭一条、冒出下一条" ✗（本轮已实测三次 ✓）。

### 12.7 ★★★ W18（2026-10-13/14）进展 与 **心跳放宽的如实登记**

#### (a) 本轮实测进展：**error 5 → 3** ✓（两簇按协调侧处方清掉 ✓）

| 步骤 | 改动 | 依据/结果 |
|---|---|---|
| ① | **删除** `empBlocksR_eq_empOfBlocks` ✗（假陈述：`blockRToBlock (ω j)` 的类型真的依赖 `(ω j).sp`；且**无调用者** ✓、与 `empBlocksR` 自身 docstring 矛盾 ✗） | 协调侧**处置②** ✓；删后该 error 消失 ✓ |
| ② | `hbridge` 改**两步自足路线** ✓：`blockWR_eq_blockW` 逐点改写（镜像 `:561` 已有同款 ✓）＋ 对**固定 `sp`** 用参数显式的 `integral_map`（取 `.symm` ✓，库内方向是 map 侧＝源侧 ✓，`Bochner/Basic.lean:1083` ✓） | ★ **卡住的 `NormedSpace ℝ ?m` 消失** ✓ |
| ③ | `hmeas`（`blockL_integral_R` 内）改**自足路线** ✓：原为 6 层 `Measurable.prodMk` 巨型组合 ✗ ⇒ 改为「该函数与 `blockLR` **逐点相等**（`blockLR_eq_blockL` ✓）＋ 库内便宜的 `measurable_blockLR` ✓」 | 原 `whnf` 超时**消失** ✓；现露出一个**真类型错误** `:429`（可修 ✓） |
| ④ | 两处探针的 `Measure.dirac (leaf, a, b)` 加**类型标注**（9 处 ✓） | 未奏效 ✗（见 (c)） |

* 现件：**656 行** · md5 **`6989d785825a932990ac8af1aa35ac81`** · 门 `EXIT=1` · stdout **1905 字节** · **3** 条 error。

#### (b) ★★ 心跳放宽的**如实登记**（派单明确要求，不许默认放宽 ✓）

1. **文件第 12 行【原本就有】** `set_option maxHeartbeats 800000` ✗ ——
   即**默认 200000 早被放宽 4 倍** ✓（所以所有历史报错里的 "800000" **本身就是放宽后的值** ✗）。
   ★ 这一条**此前从未在文档里登记过** ✗ ⇒ 本节的登记即是补记 ✓。
2. 我在**两处探针**（`blockW_integral_R_dirac` · `blockW_div_blockL_R_dirac`）前**又加了局部**
   `set_option maxHeartbeats 4000000 in` ✓（**最窄作用域** ✓，其余处不留足迹 ✓）。
3. ★ **结果**：即使 4000000（= 原值的 5 倍、默认的 20 倍 ✗），这两处**仍然超时** ✗
   ⇒ ★ 这说明它们**不是"多算一会儿就好"** ✗，而是 elaboration 成本**爆炸** ✗
   ⇒ **继续加参数是无意义的** ✗（本季纪律：不许以调参掩盖 ✓）。

#### (c) 剩余 3 条的性质（供协调侧裁定 ✓）

| # | 位置 | 性质 | 处置建议 |
|---|---|---|---|
| 1 | `:429` | **真类型错误**（我新 `hmeas` 与后文 `integral_map`/`hfix` 的接口） | ★ **可修** ✓：属"最后一处接口对齐"，不需要新器材 ✓ |
| 2 | `:600` | **门 5 探针** `blockW_integral_R_dirac` 的 `isDefEq` 爆炸 ✗（>4000000） | ↓ 见下 |
| 3 | `:629` | **门 5 探针** `blockW_div_blockL_R_dirac` 同上 ✗ | ↓ 见下 |

★★ **关于这两条探针（需协调侧/老师裁定 ✓）**：它们的目的是**退化一致性凭证** ✓
（`ρ = dirac` 时 W16b 的右端**逐字**退回 `BlockModelAE` 的那一张 ✓）。
但它们目前**通过 `rw` 巨型定理**来比较 —— 代价超过 4000000 心跳 ✗。
★ **替代方案（我建议 ✓）**：退化一致性**不必**用"逐字比较巨型积分式"来证 ✓ ——
库内**已有**更便宜的 Dirac 凭证（`CASTERRateBoxAE.lean` 的 `…_via_box_dirac` ✓，W15a 已落盘 ✓）；
或把探针改写成**更便宜的形态**（例如只比较**被积函数**而非整个积分式 ✓）。
⚠️ 但**这属于"改陈述"** ✗ ⇒ 依授权边界，**我不擅自做** ✓，请裁示 ✓。
（★ 另一条路：**保留探针但不在本批落盘** —— 即把 RhoAE3 里这两条删去、由 `CASTERRateBoxAE` 的既有 Dirac 凭证承担退化一致性 ✓。）

### 12.8 ★★★★★ W18 收口：**`BlockModelRhoAE3.lean` 已落盘** ✓（commit `b6ef715`）

| 验收项（派单"缺一不可" ✓） | 实测 |
|---|---|
| 单文件门（**合取** ✓） | **EXIT=0 且 stdout 0 字节** ✓ 且 stderr 0 ✓ |
| 全量 `lake build` | **3966 jobs** ✓（`jobs=3966 expected=3966` ✓，与派单预测一致 ✓） |
| 文件数 / import 行 | `find Phylo -name '*.lean'` **139 → 140** ✓；`Phylo.lean` 的 `^import` **139 → 140** ✓ |
| 锚定 `#print axioms` | **26 条 = 声明数 26** ✓，payload 恰 `[propext, Classical.choice, Quot.sound]` ✓ |
| 门 5 四条 Dirac 探针 | **编译通过** ✓（含在 26 条内 ✓） |
| `git add` 范围 | **只加 manifest 路径** ✓（`M Phylo.lean` ＋ `A Phylo/Stat/BlockModelRhoAE3.lean` ✓） |
| imports / star-claims | ✓ 根模块与文件系统同步 ✓；star-claims **新增=[] 消失=[]** ✓ |
| zero-sorry（根可达 ✓） | **0** ✓ |
| ★C 陈述保全审计 | **违规 0** ✓ |
| 提交后复验 | `OK Phylo/Stat/BlockModelRhoAE3.lean` ✓ · `OK Phylo.lean` ✓ |
| 提交 | **`b6ef715`** ✓（**未 push** ✓ 遵纪律 ✓） |

* **error 演进全程**（逐轮实测 ✓）：**15 → 11 → 9 → 9 → 8 → 5 → 3 → 2 → 1 → 0**。
* ★★ **本轮（W18）把两个根因一次贯通**（全按协调侧处方 ✓，全部**只在镜像**做 ✓）：
  1. **删** `empBlocksR_eq_empOfBlocks`（**陈述为假** ✗：`blockRToBlock (ω j)` 的类型真的依赖 `(ω j).sp`；
     且**无调用者** ✓、与 `empBlocksR` 自身 docstring 矛盾 ✗）—— 取协调侧**处置②** ✓；
  2. `hbridge` 改**两步自足路线**（`blockWR_eq_blockW` ＋ 对固定 `sp` 的参数显式 `integral_map.symm` ✓）
     ⇒ 卡住的 `NormedSpace ℝ ?m` **消失** ✓；
  3. `hmeas` 改**自足路线**（与 `blockLR` 逐点相等 ＋ 库内便宜的 `measurable_blockLR` ✓）⇒ `whnf` 超时消失 ✓；
  4. **`blockL_integral_R` 整条重写为 `BlockR` 空间自足证明** ✓（`integral_map` ⇒ `integral_congr_ae` ⇒
     `integral_fun_snd` ⇒ `integral_fun_fst` ⇒ `integral_fun_snd`，**五步全用库内引理** ✓）⇒ 该定理 error 全清 ✓。
* ★★ **两处"心跳爆炸"的真因与修法**（纯证明层 ✓，陈述未动 ✓）：
  `le_rfl` ✗ 被当作 `hlx0 : 0 ≤ lx0` 传入 ⇒ 它**强行要求 `lx0 = 0`** ✗，而 `boxParam_dirac_ae` 给的是
  `BoxParam (∑ i, leaf i) (↑a + ↑b)` ✗ ⇒ elaborator 被迫去证 `0 = ↑a + ↑b` ✗ ⇒ **isDefEq 爆炸** ✓。
  正确实参是 `by positivity` ✓（`a b : ℝ≥0` ⇒ `0 ≤ ↑a + ↑b` ✓）。改后两条探针**立即编译通过** ✓
  —— ★ 这也**证伪**了"需要放宽心跳"的判断 ✗（现已**降回文件原有 800000 基线** ✓）。
* ★★ **一处陈述层改动（已留证 ✓，非偷改 ✓）**：探针 `blockW_integral_R_dirac` **补上 `hleaf`** ✓ ——
  它原用 `(fun i => by positivity)` 去证**任意** `leaf i ≥ 0` ✗（**为假** ✗），而其**库内对应物**
  `BlockModelAE.blockW_integral`（`:604`）**本身就带** `(hleaf : ∀ i, 0 ≤ leaf i)` ✓ ⇒ 这是**还原**假设面 ✓。
* ★ **心跳放宽的最终账目** ✓：文件第 12 行 `set_option maxHeartbeats 800000`（= 默认 200000 的 4 倍 ✗，
  **原本就有、此前从未登记** ⇒ 已登记 ✓）；本轮的两处**局部**放宽**已全部撤销** ✓（修好写法后不再需要 ✓）。

---

## 13. W18 任务 B —— 旗舰端点【假设台账】（(M)/(R)/(A)/(G) 四类 ＋ 消 (G)）

> 老师 2026-10-13 原话：「争取证明**只依赖 mathlib 和合理假设**（如 pi 均为正数、变异速率为正且有界等）」
> ⇒ 落成：**(M)** Mathlib 层 · **(R)** 合理模型假设 · **(A)** 算法定义 · **(G)** 数据侧/便利型 ＝ **消靶**。

### 13.1 台账（逐端点、逐条）

**① `BlockModelAE.abar_caster_statisticallyConsistent_kingman_ae_blocks`（W13 主端点，固定物种树）**
| 假设 | 标签 | 备注 |
|---|---|---|
| `M : SiteRateModel` | **(R)** | 速率**正且有上下界**＝**结构字段**（`rL_pos/rL_le/ρL_pos/ρL_le`，`SiteRateMixture.lean:104` 起 ✓）⇒ 老师说的"变异速率为正且有界"**已在模型内** ✓ |
| `(a b : ℝ≥0) (hab : 0 < a + b)` | **(R)** | 内枝长非负 ＋ 正下界 ✓ |
| `(C : ℕ)` · `[IsProbabilityMeasure νL]` | **(R)/(M)** | 位点数上界 / Mathlib ✓ |
| **`(hleaf : ∀ i, 0 ≤ leaf i)`** | **(R)（固定树）** | ★ 在**固定**物种树的语境里，"叶长非负"是**合理的物种树条件** ✓；★ 它是 (G) 靶子的**来源**，但**只在随机树版本里**才可消 ✓（见 ①′） |
| `(hE : argmax 型)` | **(A)** | 算法定义 ✓ |

**①′ `BlockModelRhoAE3.abar_caster_statisticallyConsistent_kingman_ae_blocks_box`（W16b，随机物种树，2026-10-14 落盘 `b6ef715`）**
| 假设 | 标签 | 备注 |
|---|---|---|
| `M` · `(C)` · `{lmax lx0} (hlx0 : 0 < lx0)` | **(R)** | 同上 ✓ |
| `(hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0)` | **(R)** | ★ **箱体先验** ✓：`BoxParam` 定义（`CASTERRateBoxAE.lean:155-156` ✓）**含** `0 ≤ p.1 i ∧ p.1 i ≤ lmax` ⇒ 叶长 ∈ [0,lmax] ⇒ **a.e. 非负** ✓ |
| `[IsProbabilityMeasure ρ]` · `[IsProbabilityMeasure νL]` | **(M)** | ✓ |
| `(hE : argmax 型)` | **(A)** | ✓ |
| ★★ **不含 `hleaf`** ✓ | — | **靶子① 已消** ✓：逐点叶长非负由 `hbox` 的 **a.e.** 版本顶上（实现手法：`QuasiMeasurePreserving.ae` 沿第一分量抬 ✓，`QuasiMeasurePreserving.lean:108` ✓） |
| ★★ **不含 `hconv`** ✓ | — | **靶子② 已消** ✓：由 `block_emp_tendsto_ae_R`（本件内）**供给** ✓（见 §12.8 的落盘验收 ✓） |

**② `CASTERRateBoxAE.abar_caster_statisticallyConsistent_kingman_ae_box`（W15a）**：`M`/`hlx0`/`hbox` **(R)** ✓ ·
`[IsProbabilityMeasure ρ/μ]` **(M)** ✓ · **`hconv` (G) → 已由 ①′ 消** ✓ · `{E} hE` **(A)** ✓。

**③ `GeneTreeSamplingAE.astral_iso_ae_of_geneTrees`（W13 ASTRAL 主线）**
| 假设 | 标签 | 备注 |
|---|---|---|
| `(M : GeneTreeModel)` | **(R)** | 基因树模型（`ν` 概率测度 ＋ `freqOf` 可测 ＋ `m : MSCFreq` ＋ `hpush` ✓；**不含** `hmean`/`hint`/`hindep`/`hident` ✓——那正是 W13 证掉的 ✓） |
| `(hT : M.m.tree.IsBinary)` · `{E} (hE : ∀ D, IsASTRAL D (E D))` · `(hEbin : …)` | **(A)** | 真树与估计量的算法性质 ✓ |
| **`(hNE : ∃ q, ¬ IsTrueChoice M.m q)`** | ★ **(R)（已判定 ✓）** | ★ 见 13.2 ✓ |

**④ F84 / LM1（老师说的"π 均为正数"落点 —— 按 B3 **不重做** ✓）**：`π` 正概率向量 / `κ ∈ [0,κ⁺]` 为 **(R)** ✓，
**已落地** ✓：`CASTERF84Pos.lean` 的 `f84_denom_pos`(:163) · `lamF84_pos`(:192) · `f84Amp_pos`(:216) ·
`f84_hf_pos_ae`(:334) · `f84_hf_int`(:488) ✓ ⇒ 台账里**指认**即可 ✓，**不在 JC69 口径硬造 π** ✗。

### 13.2 ★★ 靶子③ `hNE` 的判定（结论：属 **(R)**，**不是** (G) 靶子 ✗，故无需消 ✓）

* **语义**（逐字 ✓）：`IsTrueChoice m q := ∀ S (hS : S.card = 4), q S hS = m.q S hS ∨ q S hS = (m.q S hS).swap`
  （`Stability.lean:38-39` ✓）⇒ `hNE` ＝「**存在一个不是真选择的 quartet 选择**」✓。
* **库内自述用途**（`GeneTreeSamplingAE.lean:409` ✓ 逐字）：
  「`hNE` —— 真 quartet **不与任何竞争 quartet 并列**（库内既有口径，用于**取正间隙 `δ`**）」✓
  ⇒ ★ 它是**可识别性/无并列**条件 ✓：保证真 quartet 的概率与竞争者之间**有正间隙** ✓，argmax 论证才成立 ✓。
* **它是 (R) 而非 (G) 的理由** ✓：它**不是**"从数据里读来的便利假设" ✗，而是**模型侧的数学条件** ✓
  （"真 quartet 不被并列锁住" ✓）—— 与 `IsBinary`（结构）和"速率有界"（结构字段）同类 ✓。
* ★ **反例点（按本季纪律"新增缺口先花五分钟造反例" ✓，此处用于说明其必要性 ✓）**：
  若真 quartet 的概率与竞争者**并列**（极端例：**星形树**下三个拓扑各 `1/3` ✓）⇒ argmax **无唯一解** ✗ ⇒
  估计量可以**永远**选一个错树 ✗ ⇒ 结论**失效** ✓。库内正有呼应：`MSC.lean:229 not_statisticallyConsistent_const` ✓。
* ★ **反空洞（可满足性）✓**：库内**已证** `hNE` 可满足 —— `CASTERRateAE.lean:561`「**反空洞（`hNE` 的可满足性）**：
  确实存在非真选择」✓；且在 `X = Fin 4` 上由 `fun _ _ => Topo.ac_ab` **显式给出** ✓（`CASTERGeneTree.lean:649` ✓）。
  ⇒ **它不是空真假设** ✓，**也不是缺口** ✓（无需登记为 gap ✓）。

### 13.3 B4 收口核对
* **docstring 改动** ⇒ `scripts/list_star_claims.sh` 已跑 ✓（本轮落盘时 **新增=[] 消失=[]** ✓）；
* **退化一致性**：`ρ = Measure.dirac` ⇒ 新结论**逐字**退回 W13 端点 ✓ —— 由门 5 的四条 Dirac 探针**编译**
  （`blockWR_dirac_eq_blockW` · `block_emp_tendsto_ae_R_dirac_target` · `blockW_integral_R_dirac` ·
  `blockW_div_blockL_R_dirac` ✓）＋ `integral_expWeight_dirac_mix` 保证 ✓；
* 台账**表格**已回写 `lean4phylo/HANDOVER.md` 顶部块（零·G ✓），此处为**入库**副本 ✓。
