# 已收口缺口的「非退化实例」覆盖率报告（W35-9① ⇒ **W39-5 全表刷新**）

> **来源**：外部审查 `lean4phylo_review.md` §A 第 3 条 —— `scripts/check_vacuous.sh` 只对 **7** 条
> （6 条 VACUOUS ＋ 1 条已修复的 `TreeMarkovFactorGap`）设了机械判据，其余「已收口」条目**没人管**。
> 本报告是对**全部 44 条**的逐条核查，回答：**这条缺口除了「真值已定」，有没有被用在具体对象上？**
>
> **这不是判据改动**：`gap_ledger.py` / `list_gaps.sh` 的口径**一字未改**；
> 本报告是覆盖度审计，结论**不回写**台账桶位（桶位仍以 `bash scripts/list_gaps.sh B` 为准）。
>
> **★ W39-5（2026-10-27）全表刷新**：44 行的 `def` 位置与收口定理位置**全部现场重取**
> （数据源 = `bash scripts/list_gaps.sh B` 与 `bash scripts/check_vacuous.sh` 的实跑输出，不是抄旧表）。
> 表内**不再抄行号**（旧表里 `名字:NNN` 一律剥掉）—— 行号随每次改动漂移，权威行号一律看脚本输出。
> 名字按 W36 后的现状：`_legacy` / 正名 / `_vacuous_*` / `atteson_lemma11_gap_order_form`。
> 机械护栏：`bash scripts/check_vacuous.sh` 现在覆盖**全部 44 条**（实例 25 · 自由槽 6 · 无实例 13）。

### ★D 更正：派单给的自查命令会对任何正确的表误报

派单要求的自查是「`_` ＋ `v` ＋ 数字 的旧版本后缀，或 `_correct_shape\b`，命中数应为 0」。实际**两处都不成立**：

* `fourPointOfSplitMetricSum_gap_correct_shape`、`pauplinEdgeCoeff_gap_correct_shape` 是**在册正名**
  （`bash scripts/list_gaps.sh B` 的【已收口】里就有，**不是废名**）⇒ 任何正确的表都会命中 `_correct_shape\b`；
* 版本后缀的判据也不该写成字面量 —— 本文件要**引用**这条规则时自己就会命中（自指误报）。

⇒ 改用两条**更强且不自指**的判据（本表都过）：

* **集合相等**：`scripts/check_vacuous.sh` 的 44 行名字与 `list_gaps.sh B` 的【已收口】43 条
  ＋【追溯】那条 `_legacy` **逐个相等**（脚本自动比对）⇒ 表里不可能藏废名、也不可能多一个；
* **版本后缀**：`grep -rnE '_v[0-9]+' Phylo/ scripts/ | grep -v '\.md:'` = 0（W36 之前的旧名一个不留）。

## 方法与判定（三选一）

| 归类 | 含义 |
|---|---|
| **实例**（有非退化实例） | 库内另有定理把这个 gap 用在**具体对象**上（具体 `Fin 4` / 具体树 / 具体 `δ` / 具体数值），且实例本身要真算。表内给该定理名，`check_vacuous.sh` 机械核。 |
| **自由槽** | `def` 体内 `∃` 绑定的**数据**可任意取退化值使 Prop 恒真（表内写出退化见证）；= `gap_ledger.py` 的 `VACUOUS` 6 键。 |
| **无实例** | 已复核：**没有**非退化的具体对象用法。正规 `∀ … → 结论` 形态、证明含真数学，但库里没人在具体对象上用它。每条给出「可造性预判」（能造 / 不能造 / 缺什么器材）。 |

⚠️ **「含 `∃`」不等于自由槽**（本报告最重要的方法论结论）：

* `circularIndicatorFullRank_gap` 的 `∃ n f` 在**前件**里（结论是 `Function.Injective …`）⇒ 不是；
* `atteson_reduction_gap_correct_shape` 的 `∃ (Y : Type u) … (δm)` 绑定了**类型数据**，
  但三条取值等式把见证**钉死** ⇒ 不是；
* `neighborNetAgglomeration_gap` 的 `∃ Step` **无任何值约束**，且 `_iff_star` 把它与输入 `d` 双向消去 ⇒ **是**。

⚠️ **「把已证的 `∀…` 特化」不算实例**（W39-3 定下的口径）：特化一条 `∀δ` / `∀T` / `∀C` 定理是零信息量的。
所以两条 `∀`-形态的缺口（`atteson_lemma11_gap_order_form`、`mnCorollary_gap`）**没有**用特化充数 ——
W39-3 是**新造**了不经过收口定理、逐项算出常数的具体实例（见总表第 6、8 行的「机械依据」列）。

⇒ 按名字或「含 `∃`」分桶会把前两条误判成第三条。**故本报告是逐条读源码得出的，不是脚本自动分桶。**

## 汇总（44 条）

| 归类 | 条数 | 说明 |
|---|---|---|
| **实例** | **25** | 有具体的定理/`example` 证据（多数是 `example` 或 `_fin4/_card_four` 一类的逐字实例）；W39-3 新增 2 条 |
| **自由槽** | **6** | 与 `gap_ledger.py` 的 `VACUOUS` 白名单**完全重合**（6/6）—— 两个独立口径互证 |
| **无实例** | **13** | **不是空转**：零假设收口、证明含真数学，只是库里没有具体对象实例；每条附可造性预判 |

★ 回答派单的问题：「44 条里几条有非退化实例」= **25 条**；
「几条疑似空转」= **6 条**（全部已登记、且 `check_vacuous.sh` 有机械依据）；
剩下 **13 条**是「真证明、零实例」。

★ W35 的旧统计是 **23 / 6 / 15**；W39-3 把 `atteson_lemma11_gap_order_form` 与 `mnCorollary_gap`
从「无实例」升为「实例」（各新造一条具体对象定理，**未改任何既有 `def`/`theorem`**）⇒ 23→25、15→13。

## 总表（44 条，`#` 与 `list_gaps.sh`【已收口】的打印顺序一致，`#44` 是【追溯】里那条空转 legacy）

> 「def 位置」「收口定理」两列是**现场实测**；「机械依据」列是 `check_vacuous.sh` 里 `grep -F` 的固定串。

| # | 缺口名 | def 位置 | 收口定理 | 归类 | 机械依据（`check_vacuous.sh`） | 非退化实例 / 用途证据 | 一行依据 |
|---|---|---|---|---|---|---|---|
| 1 | `nniDistance_min_gap` | `Phylo/Algorithm/NNINeighborhood.lean:643` | `nniDistance_min_gap_proved`@`Phylo/Algorithm/NNINeighborhood.lean:647` | **实例** | `theorem tree_nniDist₁₂_eq_one` | `tree_nniDist₁₂_eq_one`（`Fin 4` 具体 `tree₁/tree₂`，真实 1 步；比 `_nonempty` 的 0 步自反强） | `n,S,S'` 都出现在结论里；`∃!k` 被 `NNIDist` 钉住，取不到恒真见证 |
| 2 | `circularIndicatorFullRank_gap` | `Phylo/Algorithm/NeighborNet.lean:436` | `circularIndicatorFullRank_gap_proved`@`Phylo/Algorithm/NeighborNet.lean:1171` | **实例** | `theorem alm_injective_of_three_le` | `alm_injective_of_three_le`（`Fin n` 弧族 `Alm` 上用同一 §7 逆矩阵工具）；`Arc n` 模型 `arcSplit_isCyclicArc` | 证明是显式逆矩阵（`circularIndicator_injective`）；`∃n f` 在前件、结论不含它 |
| 3 | `neighborNetAgglomeration_gap` | `Phylo/Algorithm/NeighborNet.lean:453` | `neighborNetAgglomeration_gap_vacuous_holds`@`Phylo/Algorithm/NeighborNet.lean:3361` | **自由槽** | `theorem neighborNetAgglomeration_gap_vacuous_holds` | 残量 `neighborNetAgglomeration_gap_iff_star`；库内退化见证 `example`（`Step := (F = trivialSplitSet X)`） | 取 `Step d F := (F = starSplits X h2)`，与 `d` 无关 ⇒ `d` 在 `_iff_star` 中整个消失 |
| 4 | `circularDistanceRealization_gap_corrected` | `Phylo/Algorithm/NeighborNet.lean:1301` | `circularDistanceRealization_gap_corrected_holds`@`Phylo/Algorithm/NeighborNet.lean:3211` | **实例** | `theorem circularRealization_fin4` | `circularWeights_realization_gap_fin_le_five`（`X := Fin n`、`f := refl` 的 `n = 3,4,5` 特化）；`circularRealization_fin4` | `F,w` 须逐点实现 `d`；取 `F = ∅, w = 0` 只对零距离成立 |
| 5 | `circularWeights_realization_gap` | `Phylo/Algorithm/NeighborNet.lean:1673` | `circularWeights_realization_gap_proved`@`Phylo/Algorithm/NeighborNet.lean:2977` | **实例** | `theorem circularWeights_realization_gap_fin_le_five` | `circularWeights_realization_gap_fin_le_five` = 本 gap 在 `n = 3 ∧ 4 ∧ 5` 的逐字实例 | `w` 被 `phyleticDist F w = d` 钉住；`n = 3,4,5` 已逐字实例化 |
| 6 | `atteson_lemma11_gap_order_form` | `Phylo/AttesonRadius.lean:859` | `atteson_lemma11_gap_order_form_holds`@`Phylo/AttesonRadius.lean:992` | **实例** | `theorem atteson_lemma11_gap_order_form_at_exDiss` | ★W39-3 新造：`..._at_exDiss` 在 `exDiss`（4 叶真树度量）上逐对算出 `δmin = 5`、间隙 `10 = 2(n−3)·5` | 实例**不经过** `_order_form_holds`，是逐对实算的常数；序关系形态本身对一切 `δ` 为真 |
| 7 | `atteson_reduction_gap_correct_shape` | `Phylo/AttesonRadius.lean:1455` | `atteson_reduction_gap_correct_shape_proved`@`Phylo/AttesonRadius.lean:1471` | **无实例** | — | 原形态在具体 `exDiss`（`Fin 4`、`θ = 1/2`）上被否：`atteson_reduction_gap_refuted`；本形态无具体对象实例 | `∃Y,q,δm` 被三条取值等式钉死（非自由槽）；只有零信息特化可用 |
| 8 | `mnCorollary_gap` | `Phylo/ConsensusAxioms.lean:497` | `mnCorollary_gap_proof`@`Phylo/ConsensusAxioms.lean:801` | **实例** | `theorem mnCorollary_gap_at_thresholdRule` | ★W39-3 新造：`..._at_thresholdRule` 取 `C := ThresholdRule k t`（`t ≤ k < 2t`），六条前提逐条证 | `t` 由 `C P = ThresholdRule k t P` 钉住；实例说明「阈值参数由规则本身确定」 |
| 9 | `QuartetBridgeGap` | `Phylo/FitchGeneral.lean:1149` | `QuartetBridgeGap_holds`@`Phylo/FitchGeneral.lean:1405` | **实例** | `theorem fitchCostGen_quartet` | 见证是具体 7 顶点树 `quartetTree`；逐 `σ` 计算 `fitchCostGen_quartet` | `∀σ` 等式把见证钉死（叶根树给 0 ≠ `Pattern.fitchCost 0`） |
| 10 | `pauplinFormula_gap` | `Phylo/PauplinFormula.lean:941` | `pauplinFormula_gap_of_isBinary`@`Phylo/PauplinFormula.lean:1107` | **实例** | `theorem ex4_bmeLength` | 4 叶端到端 `BMELeastSquares.lean`（`15 = l(T)`；`pauplinLength_eq_bmeLength` 是 `rfl`） | `l̂ = l` 经 `_of_correct_shape` + `sideDoublingSum_eq_one_of_isBinary` 实质证明 |
| 11 | `pauplinEdgeCoeff_gap_correct_shape` | `Phylo/PauplinFormula.lean:1011` | `pauplinEdgeCoeff_gap_correct_shape_of_isBinary`@`Phylo/PauplinFormula.lean:1029` | **实例** | `theorem ex4S_normalization` | 4 叶逐边 `ex4S_normalization`（真边归一化和 `= 2`） | 量词收到 `e ∈ T.graph.edgeSet`（原形态 `not_edgeCoeff_forall_eq_two` 为假）后实质证成 |
| 12 | `BinaryConnectedEqualsSideGap` | `Phylo/PerfectPhylogeny.lean:483` | `BinaryConnectedEqualsSideGap_holds`@`Phylo/Connectivity.lean:322` | **无实例** | — | 无：全库仅 def／收口／docstring，无具体 `T`、`A` 消费者；两半证明亦抽象 | ∀T A 的桥／跨界边论证实质，但无具体 `T`、`A` 实例、无下游 |
| 13 | `MultiStatePairwiseInsufficiencyGap` | `Phylo/PerfectPhylogeny.lean:500` | `MultiStatePairwiseInsufficiencyGap_holds`@`Phylo/PerfectPhylogeny.lean:1333` | **实例** | `theorem pairwise_displays_fitchMeachamF3` | `fitchMeachamF3` 具体矩阵（5 taxa × 3 字符 × 3 状态）；两两可解 ＋ 整体不可解 | 见证矩阵钉为 `F₃`；否定半靠候选二元叶侧必相交，取不到恒真见证 |
| 14 | `greedy_gap_correct_shape` | `Phylo/PhyloDiversity.lean:444` | `greedy_gap_correct_shape_proof`@`Phylo/PhyloDiversitySubtree.lean:689` | **无实例** | — | 无具体树：`PhyloDiversity.lean` 自认未构造 `Phylogram` 实例；消费仅泛型 `example` `Subtree` | `∃ prev next` 被 PD 极大性钉住、非自由槽；但无具体树实例、无下游 |
| 15 | `pdExchange_gap` | `Phylo/PhyloDiversity.lean:571` | `pdExchange_gap_proof`@`Phylo/PhyloDiversitySubtree.lean:684` | **无实例** | — | 消费仅 `greedy_gap_correct_shape_proof` `Subtree`（抽象 `T`）；无具体 `T`/`W`/`W'` | 加权交换不等式无 ∃ 槽，证明经 `HangOff` 不相交计数；无具体实例 |
| 16 | `quarnetRules_level1_gap` | `Phylo/QuarnetRules.lean:358` | `quarnetRules_level1_gap_degenerate`@`Phylo/QuarnetRules.lean:415` | **自由槽** | `theorem quarnetRules_level1_gap_vacuous_holds` | `_iff_display` 把四谓词消去为 `∃F` 残量；`_degenerate` 取 `Qnet=Net=PUnit`、`displayedBy≡⊥` | 取 `minimallyDense:=⊥` 使 (a) 空真、`displayedBy:=⊥` 配 `F={()}` 满足 (b)；与 quarnet 无关 |
| 17 | `level1QuartetSystem_gap` | `Phylo/QuarnetRules.lean:378` | `level1QuartetSystem_gap_vacuous_degenerate`@`Phylo/QuarnetRules.lean:401` | **自由槽** | `theorem level1QuartetSystem_gap_vacuous_degenerate` | 唯一收口即 `_degenerate`；grep 无 `_holds`、无一般形态定理 | 取 `QuartetSystem:=PUnit`、`multiplicity _ Y:=if card Y=4 then 2 else 0`，两合取项恒真 |
| 18 | `weakCompatibilityRealization_gap` | `Phylo/SplitWeak.lean:562` | `weakCompatibilityRealization_gap_holds`@`Phylo/SplitWeak.lean:2547` | **实例** | `theorem weakCompatibilityRealization_gap_card_four` | `_card_four`（card=4）、`_card_five`（card=5）为逐字数值实例；`w` 在结论消失 | `∃δ` 被 `IsDSplit↔F` 双向刻画钉住；card X=4/5 已逐字落地 |
| 19 | `fourPointCharacterization_gap` | `Phylo/SplitWeak.lean:637` | `fourPointCharacterization_gap_proof`@`Phylo/Stat/BunemanIndexBridge.lean:3299` | **无实例** | — | 无具体 `F`、`δ` 消费者；证明 = `_reverse` ＋ `_of_noWRealizer`，仅抽象 | `↔` 两侧为真刻画，无恒真见证；但库内无具体 `F`、`δ` 应用 |
| 20 | `fourPointOfSplitMetricSum_gap` | `Phylo/SplitWeak.lean:670` | `fourPointOfSplitMetricSum_gap_proof`@`Phylo/Stat/BunemanIndexBridge.lean:2910` | **实例** | `example : FourPointStd (fun x y : Fin 4 =>` | 匿名 `example` 在具体 `cexF2`（`Fin 4`、`w≡1`）上证 `FourPointStd`；注册形态收口复用它 | 三合取项由 `splitMetricSum_X_le_max` 三次重标号；`cexF2` 实例非平凡 |
| 21 | `notIsDSplit_of_splitMetricSum_gap` | `Phylo/SplitWeak.lean:689` | `notIsDSplit_of_splitMetricSum_gap_holds`@`Phylo/Stat/BunemanIndexBridge.lean:3291` | **无实例** | — | 抽象消费：`_of_noWRealizer`（`w≡1`）；无具体 `F`/`w` | 非成员 `¬IsDSplit` 由 (★′) `noWRealizer` 证成；仅作抽象前提，无具体实例 |
| 22 | `multinomial_weight_count_gap` | `Phylo/Stat/Bootstrap.lean:907` | `multinomial_weight_count_gap_proof`@`Phylo/Stat/Bootstrap.lean:924` | **实例** | `weightOf σ = (fun i : Fin 2 => if i = 0 then 2 else 0)` | 5 个具体 `(n,w)` 的 `example`：`n=2,w=(2,0)`、`(1,1)`、`(0,2)`，`n=3,w=(1,1,1)`、`(3,0,0)` | 轨道-稳定化子计数；5 个具体值逐字核对（`Nat.multinomial` 路线） |
| 23 | `bootstrap_confidence_gap` | `Phylo/Stat/Bootstrap.lean:1031` | `bootstrap_confidence_gap_vacuous_holds`@`Phylo/Stat/Bootstrap.lean:1102` | **自由槽** | `theorem bootstrap_confidence_gap_vacuous_holds` | 无；`exists_confidence_account_for` 反证任意 `s`（含低支持度 `fourAB`）均可当真树 | `Ω:=Empty` 令三条 `∀ω` 空真 ⇒ `↔True`；`Ω/TrueSplit/p` 与 `bootstrapSupport` 之间无桥 |
| 24 | `fourPointOfSplitMetricSum_gap_correct_shape` | `Phylo/Stat/BunemanIndexBridge.lean:659` | `fourPointOfSplitMetricSum_gap_correct_shape_proof`@`Phylo/Stat/BunemanIndexBridge.lean:2387` | **实例** | `example : FourPointStd (fun x y : Fin 4 =>` | 同上 `example`：具体 `cexF2`（`Fin 4`、`w≡1`）证 `FourPointStd`；注册形态收口复用它 | 三合取项由 `splitMetricSum_X_le_max` 三次重标号给出 |
| 25 | `canonicalSplitDecomposition_gap` | `Phylo/Stat/BunemanIndexBridge.lean:1156` | `canonicalSplitDecomposition_gap_holds`@`Phylo/Stat/BunemanIndexBridge.lean:4428` | **无实例** | — | 仅抽象：结论类（任意 `F,c`）被引用；无具体 `δ` | `δ₀` 被「非负+对角 0+划分版 split-prime」钉住；证明靠 `dSplits` 基数下降，无具体实例 |
| 26 | `noWRealizer_exists_gap` | `Phylo/Stat/BunemanIndexBridge.lean:2545` | `noWRealizer_exists_gap_proof`@`Phylo/Stat/BunemanIndexBridge.lean:3283` | **无实例** | — | 仅抽象：作前提被引用；无具体 `F`、四元组 | ∃ 四元组被 `Σ_{F.filter…} w = 0` 钉住；证明用 `laminar_sideNotMem` 链，无具体实例 |
| 27 | `weakCompatibilityRealization_gap_weights` | `Phylo/Stat/BunemanIndexBridge.lean:4856` | `weakCompatibilityRealization_gap_weights_holds`@`Phylo/Stat/BunemanIndexQuartet.lean:274` | **无实例** | — | 仅抽象：归约多吃 `coeffFaithfulDecomposition`；无具体 `F`、`w` | `↔` 内的 ∃ 是成员刻画（非槽）；两合取项 = `core_holds` ＋ `isolationIndex_eq_two_mul_weight` |
| 28 | `kolmogorov_extension_gap` | `Phylo/Stat/EmpiricalConvergence.lean:314` | `kolmogorov_extension_gap_proved`@`Phylo/Stat/EmpiricalConvergence.lean:322` | **实例** | `theorem kolmogorov_extension_gap_nonempty` | 有：`Ω₀:=Bool`／`coin`、边缘 `{true}=1/2`、联合 = 边缘乘积（三条具体数值） | `∃μ` 被「坐标边缘 `=μ₀` ＋ `iIndepFun`」钉死；硬币测度上给具体数值 |
| 29 | `variance_empFreq_gap` | `Phylo/Stat/EmpiricalConvergence.lean:379` | `variance_empFreq_gap_proved`@`Phylo/Stat/EmpiricalConvergence.lean:401` | **无实例** | — | 无；只证常值 `1/2` 可积（且 `1/2 ∉ {0,1}` 违反前提 1，W36-C 已撤回「非空真」） | 无 ∃；证明 = `variance_eq_integral` ＋ `variance_fun_sum'` 真内容，但无具体 `S`／`μ`／`q` 应用 |
| 30 | `evansSpeed_general_gap` | `Phylo/Stat/HadamardTransform.lean:329` | `evansSpeed_general_gap_proved`@`Phylo/Stat/HadamardTransform.lean:457` | **无实例** | — | 无模型实例；只证假设可满足（`ℤ`、`(−1)^a`） | 纯重指标恒等式，无树、无 GMM；无具体 `G`／`π`／`f` 应用 |
| 31 | `TreeMarkovFactorGap` | `Phylo/Stat/InvariantsRank.lean:367` | `treeMarkovFactorGap_holds`@`Phylo/Stat/InvariantsRank.lean:375` | **实例** | `theorem gmmFreq_factorizable` | 假设侧： 零张量实例、 具体 `deltaFreq`（秩 16）阴性对照； 消费收口 | 全在 4 叶 `κ=4` 具体层： `gmmFreq` 为显式 `Fin 4` 矩阵；证明 = `gmmFreq_factorizable` |
| 32 | `MultiLocusPosteriorConcentrationGap` | `Phylo/Stat/MSCBayes.lean:622` | `MultiLocusPosteriorConcentrationGap_holds`@`Phylo/Stat/MSCBayes.lean:663` | **无实例** | — | 无：无任何具体 `ι`／`prior`／`perLocus` 被代入 | 无 ∃ 自由槽，证明 = 指数衰减 ＋ `squeeze_zero'` 真内容；但无具体模型接线 |
| 33 | `rankedTree_card_gap` | `Phylo/Stat/RankedGeneTree.lean:683` | `rankedTree_card_gap_proved`@`Phylo/Stat/CoalescentHistoryCount.lean:583` | **实例** | `theorem card_mergeHistories_four_eq_H` | `RankedGeneTree.lean`（n=4→H₄）、`CoalescentHistoryCount.lean`（n=5→180） | 无 ∃；一般 n 走合并史逐层归纳，n=4/5 有独立数值实例。 |
| 34 | `rankedFiberCount_gap` | `Phylo/Stat/RankedGeneTree.lean:853` | `rankedFiberCount_gap_holds`@`Phylo/Stat/HookLength.lean:5108` | **实例** | `theorem rankedFiberCount_four_all` | `RankedGeneTree.lean`（n=4 一般 f）、（n=3 全部）；纤维非空 | 无 ∃；n≥2 由 reconstruct 满射 ＋ LE 收口，n=4 纤维 1/2 有独立实例 |
| 35 | `sd2012_eq4_uniform_rates_gap` | `Phylo/Stat/RankedGeneTree.lean:899` | `sd2012_eq4_uniform_rates_gap_proved`@`Phylo/Stat/RankedGeneTree.lean:1033` | **实例** | `theorem eq4_two_uniform_rates` | `RankedGeneTree.lean`（m=2 独立实例）、（m=2 复算） | 无 ∃；分母闭形式 ＋ 二项式定理实算，m=2 另有独立实例 |
| 36 | `ranked4_probability_gap` | `Phylo/Stat/RankedGeneTree.lean:910` | `ranked4_probability_gap_proved`@`Phylo/Stat/RankedGeneTree.lean:1058` | **实例** | `ranked4_probability_gap_proved 1 (by norm_num)` | `RankedGeneTree.lean`（`t=1` 实例）、（2+16 纤维计数） | p 被三式钉住、t 经 `mscConcordant t` 进入；c∈(1/3,1)，取 2 个 `c/2`、16 个 `(1−c)/16`，p=0 失败 |
| 37 | `YHKClanLawGap` | `Phylo/Stat/ReciprocalMonophyly.lean:924` | `yhkClanLawGap_holds`@`Phylo/Stat/RankedTreeClanLaw.lean:1166` | **实例** | `theorem yhkLawFour_clanEvent_two` | `ReciprocalMonophyly.lean`（n=4 整条）、（`clanProb 4 2 = 1/3`） | RHS 取 1/3 等非 0/1 值，退化分布填不出；n=4 切片有显式见证 |
| 38 | `TwoClanLawGap` | `Phylo/Stat/ReciprocalMonophyly.lean:985` | `twoClanLawGap_holds`@`Phylo/Stat/ClanPairLaw.lean:3458` | **实例** | `theorem yhkLawFour_twoClanEvent` | `ReciprocalMonophyly.lean`（n=4 整条）、（`qn 4 1 2 = 1/3`） | RHS 取 1/3 等非 0/1 值；载体 `RankedTree n` ＋ `prob≡1/H n` 显式装配 |
| 39 | `card_trivial_splits_gap` | `Phylo/Stat/SplitProbabilities.lean:407` | `card_trivial_splits_gap_holds`@`Phylo/Stat/TrivialSplitCount.lean:160` | **实例** | `theorem card_trivial_splits_four` | `TrivialSplitCount.lean`（n=4→8）、（可计算代理 4→8） | 无 ∃；`sideA`／`sideB` 双射实算，n=4 有独立实例 8 |
| 40 | `msc_split_probability_object_gap` | `Phylo/Stat/SplitProbabilities.lean:552` | `msc_split_probability_object_gap_vacuous_holds`@`Phylo/Stat/SplitProbabilities.lean:586` | **自由槽** | `theorem msc_split_probability_object_gap_vacuous_holds` | 退化见证 `SplitProbabilities.lean`：`σ=Unit`、`Displays=True`、`P`＝平凡 1／锚点 `2n−6` | 取 `σ=Unit`、`Displays=True`、`P` 压锚点即恒真；ε 只剩空转蕴含。 |
| 41 | `quartetMeanEquidistributed_gap` | `Phylo/Stat/TreeMetricDistribution.lean:667` | `quartetMeanEquidistributed_gap_holds`@`Phylo/Stat/QuartetMeanEquidistributed.lean:225` | **无实例** | — | 无（`X=Fin 3` 是退化支；`n=4` 只核右端 48，未给具体 𝒯 实例） | 无 ∃；证明是 6 侧×k 的实质双计数，但库内无 n≥4 具体 𝒯 上的实例／用途 |
| 42 | `two_parent_trees_gap` | `Phylo/SupertreeLimits.lean:693` | `two_parent_trees_gap_holds`@`Phylo/TwoParentTrees.lean:590` | **实例** | `theorem treeP1_displays_prof` | `TwoParentTrees.lean`（`treeP1`/`treeP2` 显式对＋②分类定理） | 显式 T₁/T₂ 展示 prof，分类定理已证；正确形态见证非退化。 |
| 43 | `two_parent_trees_gap_correct_shape` | `Phylo/SupertreeLimits.lean:722` | `two_parent_trees_gap_correct_shape_holds`@`Phylo/TwoParentTrees.lean:578` | **实例** | `theorem two_parent_trees_gap_correct_shape_holds` | `TwoParentTrees.lean`（`treeP1`/`treeP2`）、（`sP2a∈T₂∖T₁`） | ③ 直接排除 T₁=T₂；显式 split 系统与 σ 交换逐条 `decide`。 |
| 44 | `canonicalSplitDecomposition_gap_correct_shape_legacy` | `Phylo/Stat/BunemanIndexBridge.lean:728` | `canonicalSplitDecomposition_gap_correct_shape_legacy_holds`@`Phylo/Stat/BunemanIndexBridge.lean:884` | **自由槽** | `theorem canonicalSplitDecomposition_gap_correct_shape_legacy_holds` | 退化构造 `F:=univ`、`c≡M=2S+1`、`δ₀:=δ−M·Σδ_s`（非对角任意负）⇒ `SplitPrimeStd` 恒真 | W36-7b 降名 `_legacy`（进 `[追溯]`）；忠实形态另有正名 `canonicalSplitDecomposition_gap` |

## 备注（合并 4 条泳道的发现，按重要性）

### 1. 「已收口」不蕴含「非空转」

`neighborNetAgglomeration_gap_vacuous_holds`（W36-A 改名前的 `…_holds`）是一行**零假设**收口，
而它正是空转那条。⇒ `gap_ledger.py` 的「已收口」桶与 `VACUOUS` 集合**有交集**；
这也是本报告存在的理由。

### 2. 口径偏高的两条（已收口但比名字弱）

* `atteson_lemma11_gap_order_form`：`δmin` 只是 `∃` 的**数值松弛**（除 `0 < δmin` 外无约束），
  证得的是「每个非樱桃对都有 `Q` 更小的樱桃对」，**不含** Lemma 11 的 `3(n−4)·δmin` 间隙式；
  且它**无消费者**（`njCriterion_minimizer_is_cherry` 仍以 `hsep` 为假设）。
  ★ **W38-1 已按方案 d 处理**：序关系版改名 `_order_form`（名字直说了弱在哪），Lemma 11 的忠实形态
  另立为 `atteson_lemma11_gap_quantitative`（`[真开放]`，台账 71 → 72）。
  ★ **W39-3 又补了实例**：`…_order_form_at_exDiss` 在具体 4 叶树度量上逐对算出 `δmin = 5`（总表第 6 行）。
* `weakCompatibilityRealization_gap`：`w` 只出现在**假设**里、不进结论
  （`SplitWeak.lean` 的 def 处 docstring 自认）⇒ 它证的是 BdD Thm 3 的 (1)；系数形态另在
  `weakCompatibilityRealization_gap_weights` 登记。

### 3. 名字与实际形态不符（不影响判定，但会误导 reader）

* `pauplinFormula_gap` / `pauplinEdgeCoeff_gap_correct_shape` 的收口定理叫 `_of_isBinary`，但都是**零假设**
  （`IsBinary` 是 Prop 内部的蕴含前提，不是多吃进一个假设）。
* `QuartetBridgeGap` 名字无 `_gap` 后缀，且是**具体 `Fin 4` 断言**（不是一般 `n` 的桥）。
* `pdExchange_gap` / `fourPointOfSplitMetricSum_gap` 的具体实例是**匿名 `example`**，按命名定理统计会漏。

### 4. 台账引用可以更准的两处

* `nniDistance_min_gap` 的「非空真」引的是 `_nonempty`（`S = S'` 的 0 步自反**退化**见证）；
  真正非退化的实例是 `tree_nniDist₁₂_eq_one`（`Fin 4`、真实 1 步）。
* `variance_empFreq_gap` 的 docstring 曾称常值指示 `ind ≡ 1/2`
  使四条前提同时可满足 —— 但 `1/2 ∉ {{0,1}}` 违反前提 1；那条 `example` 只证常值**可积**。
  ⇒ 目前**没有**机器证据说它非空真（不影响它「已收口」，但「非空真」这句话要撤回或补真见证）。
  ★ **W36-C 已落地**：`EmpiricalConvergence.lean` 的该 docstring 已改成「**无见证**」并写明失实处
  （`ind ≡ 1/2` 违反前提 1；`example` 只证常值可积；卡点在第五条前提 `∫ ind = m.freq.p`）。
  ⇒ 本表第 30 行的判定**无需改动**（原本就记「无」）—— 派单称它「疑似自由槽」是**记错行**：
  疑似自由槽那 6 条 = `VACUOUS` 白名单，`variance_empFreq_gap` 不在其中。

### 5. `level1QuartetSystem_gap` 只有退化见证

全库 grep 无 `level1QuartetSystem_gap_holds`，唯一收口是 `_degenerate`。
⇒ 改名要写成 `_vacuous_degenerate`（不是 `_vacuous_holds`），台账后缀表需同时收两种。
★ **W36-A 已落地**：改名 `level1QuartetSystem_gap_vacuous_degenerate`；`CLOSURE_SUFFIXES` 已同收
`_vacuous_holds` 与 `_vacuous_degenerate`；七桶实测仍 **真开放 0 / 已收口 43**。

### 6. 4 条已收口的 `def` docstring 仍写「未证 / 仍然开着」

`rankedFiberCount_gap`、`quartetMeanEquidistributed_gap`、`two_parent_trees_gap`、
`two_parent_trees_gap_correct_shape` —— 四条 `def` 的 docstring 曾与台账「已收口」矛盾
（写「未证 / 仍然开着」），属 docstring 漂移，建议下一批统一订正（不动数学陈述，docstring 可改）。
★ **W36-B 已落地**：四条 docstring 首行已加 `✅ **已收口**（定理名，文件:行，批次）` 状态行，
并把文内「保留缺口 / 仍然开着 / 未证」全部转成过去时（`def` 本体一字未动）。

---

## 附：`ranked4_probability_gap` 单独立项核查（item 9②）—— **判定：不是空转，但内容薄**

* `def`（`RankedGeneTree.lean:911`）：`∀ t > 0, ∃ p, 非负 ∧ Σ p = 1 ∧ Σ_{平衡形} p = mscConcordant t`。
* `p` **不是**自由槽：第三条合取把 `t` 钉进结论（`mscConcordant t` 随 `t` 变）。
* 非恒真的证据：`p ≡ 0` 违反 `Σ = 1`；单点分布违反第三条（`mscConcordant t ∈ (1/3, 1)`）。
* 构造见证：平衡形 2 个 ranking 各 `c/2`、其余 16 个各 `(1−c)/16`，`c = mscConcordant t`；
  证明实际用到 `mscConcordant_nonneg`（`:1062`）与 `mscConcordant_le_one`（`:1040`/`:1064`）。
* **结论**：命题为真、非空转；但「存在 ＋ 边缘化 ＋ 归一」的内容等价于
  `0 ≤ mscConcordant t ≤ 1` ＋ 2/16 纤维可铺任意质量 ⇒ **不宜**按「ranked 概率表与 MSC 模型一致」宣传。
  `def` 的 docstring（`:904–906`）已如实写了这一点 ⇒ **不**按第 8 条改名 `_vacuous_holds`，桶位不动。

---

## 15 条「无实例」的**可造性预判**（W39-3 第一步交付）

> W35 表格里判为「无」的 15 条，逐条给出**能不能造出具体对象实例**。
> 口径：「能造」= 用库内现有器材能在合理成本内落下一条**不经过收口定理的**具体对象定理；
> 「只能零信息特化」= 唯一能做的是把已证的 `∀…` 套到一个具体对象上，不增信息（不算实例）；
> 「原理性不能造」= 造它等价于证明该条背后的真缺口。
> **13 条最终仍归「无实例」，2 条已造并入「实例」**（总数 44 不变）。

| # | 缺口 | 可造性预判 | 卡在哪（器材） | 处置 |
|---|---|---|---|---|
| 1 | `atteson_lemma11_gap_order_form` | **能造 ⇒ 已造** | 器材齐（`exDiss`/`exDiss_fourPoint`/`exDiss_isCherry_01`/Q 值表） | 例 `…_order_form_at_exDiss`，归「实例」 |
| 2 | `mnCorollary_gap` | **能造 ⇒ 已造** | 器材齐（`ThresholdRule` ＋ 六条性质引理） | 例 `…_at_thresholdRule`，归「实例」 |
| 3 | `atteson_reduction_gap_correct_shape` | 不能造（有信息量的那种） | `∃(Y,q,δm)` 被三条等式钉死，需 `mergeDissim` 在具体 `δ` 上的**求值**引理 | 无实例 |
| 4 | `BinaryConnectedEqualsSideGap` | 不能造 | 需把 `T.V` 当有限可枚举类型用（`treeP1` 的载体是内部构造），才能写出 `ℓ : T.V → Bool` | 无实例 |
| 5 | `greedy_gap_correct_shape` | 不能造 | `PD` 是实数和，`decide` 不适用；缺 `PD` 在 `T1234`/`star4Tree` 上的**值表** | 无实例 |
| 6 | `pdExchange_gap` | 不能造 | 同上（还需逐 `x` 比较 PD 增量） | 无实例 |
| 7 | `fourPointCharacterization_gap` | 不能造 | 非平凡实例要构造 `δ := Σ w_s·δ_s` 并证 (B1)/(B2)，= 本库登记的两个瓶颈 | 无实例 |
| 8 | `notIsDSplit_of_splitMetricSum_gap` | **原理性不能造** | `_holds` 以 `noWRealizer_exists_gap` 为前提 ⇒ 实例等价于证 (B2) 本身 | 无实例 |
| 9 | `canonicalSplitDecomposition_gap` | 不能造 | `_holds` 走 `dSplits` 基数下降，不产出可读分解；缺「在具体 `δ` 上求 `(F,c,δ₀)`」的计算层 | 无实例 |
| 10 | `noWRealizer_exists_gap` | 不能造 | 需算 `F.filter (bPairW …)` 为空，而 `bPairW` 取值依赖 `ℝ` ⇒ 缺可计算复刻 | 无实例 |
| 11 | `weakCompatibilityRealization_gap_weights` | 不能造 | 可计算复刻 `sepQ` 只做到 `n=4`，且未与注册形态接桥 | 无实例 |
| 12 | `variance_empFreq_gap` | **原理性不能造** | 缺「具体 MSC 频率表 ↔ `ind`」的桥（W36-C 已记；第五前提 `∫ ind = m.freq.p`） | 无实例 |
| 13 | `evansSpeed_general_gap` | 只能零信息特化 | 有信息量要字符正交性，而 `χ` 是两条公理的任意函数，与 `Mathlib.AddChar` 无桥 | 无实例 |
| 14 | `MultiLocusPosteriorConcentrationGap` | 能造但**成本 ≫ 收益** | 需 `Tendsto` 商 ＋ `exp` 衰减；且该条无假设已证成，实例只是把已证结论算一遍 | 无实例 |
| 15 | `quartetMeanEquidistributed_gap` | 不能造 | 需 `quartetDistFull` 在 `Fin 4` 的 9 个有序对上的值表（和为 48） | 无实例 |

★ 机械落点：13 条「无实例」的每条原因都写在 `scripts/check_vacuous.sh` 的 `noinst` 行里
（`bash scripts/check_vacuous.sh` 会把它们逐条打印出来），所以「无实例」不是一句免责声明，
而是**带原因的可复核判定**。

## 6 条「疑似自由槽」逐条结论（W39-4，2026-10-27）

> **范围**：`gap_ledger.py` 的 `VACUOUS` 白名单 6 键，与上表「疑似自由槽」6 行**逐个重合**。
> **本轮不改桶位**（改桶要老师批）：6 条现在的桶是 —— 5 条 `[已收口]`（`quarnetRules_level1_gap`、
> `level1QuartetSystem_gap`、`neighborNetAgglomeration_gap`、`bootstrap_confidence_gap`、
> `msc_split_probability_object_gap`）＋ 1 条 `[追溯]`（`canonicalSplitDecomposition_gap_correct_shape_legacy`）。
> 下列「建议」只是建议，**台账一行未动**；`bash scripts/check_vacuous.sh` 仍是它们的机械护栏（6/6 有依据）。

每条四问：**① 现在证的是什么　② 忠实形态长什么样　③ 建议（加强 / 保持登记 / 降级）　④ 要什么器材、量级**。

### 1. `quarnetRules_level1_gap`（`Phylo/QuarnetRules.lean:358`）→ 建议 **降级**

① 证的是：`∃ Qnet Net displayedBy 四个规则谓词 isTypeI`，使 (a) 四规则同时成立 ⟹ 该 `F` 被某个 `N` 展示、
(b) 存在一个「非展示」的 `consistent ∧ cyclative ∧ saturated` 系统。**这八件器材全是 `∃` 绑定的自由变量**，
取 `consistent = cyclative = saturated := (F = ∅)`、`displayedBy := ⊥`、`minimallyDense := ⊥` 即满足
（`_vacuous_holds` ＋ `_degenerate` 双见证）。所以它证的是「这个 `Prop` 恒真」，不是 Theorem 2。
② 忠实形态：把 `Qnet` 钉成**真的 quartet 载体**（`Quartet` 已有）、`displayedBy` 钉成 `Q(N)`（网络展示关系）、
四个谓词给**文献里的定义**（Buneman 1998 level-1 quarnet 规则），结论证「四规则 ⟹ 存在网络 N 使 Q(N) = F」。
③ **降级**（`[判定收档]`）。理由：登记形态零内容，而「已收口」会让读者以为 Theorem 2 在库内；降级不删东西 ——
`_vacuous_holds` 本身是有价值的机器证据（它证明该 Prop 是空的）。
④ 缺：网络载体（本库无 `PhyloNet`）＋ `Q(N)` 定义 ＋ level-1 判定。量级 **1500–2500 行 ＋ 1 个新模块**。

### 2. `level1QuartetSystem_gap`（`Phylo/QuarnetRules.lean:378`）→ 建议 **降级**

① 证的是：`∃ QuartetSystem multiplicity`，使每个 4-元集 `Y` 上 `m ∈ {1,2}`，且某处 `m = 2`。
`QuartetSystem` 是自由变量类型 ⇒ 取 `PUnit`、`m _ Y := if Y.card = 4 then 2 else 0` 即真
（唯一收口就是 `_vacuous_degenerate`，连 `_holds` 都没有）。**没有「level-1」**：
level-1 的真正内容是「5-元集上的相容性」，这里一个字都没有。
② 忠实形态：`QuartetSystem := Finset (Quartet (Fin n))`、`multiplicity Y := (Q.filter (·.on Y)).card`，
并证 **（D1）⟺ level-1**：每 4-元集至多 2 个、每 5-元集上选中的 quartet 两两相容。
③ **降级**（`[判定收档]`），与第 1 条同因。
④ 缺：`Quartet.on`（限制到子集）与 quartet 相容关系的基本引理。量级 **600–1000 行**（无网络层，比第 1 条小）。

### 3. `neighborNetAgglomeration_gap`（`Phylo/Algorithm/NeighborNet.lean:453`）→ 建议 **降级**

① 证的是：`∃ Step : (X→X→ℝ) → Finset (Split X) → Prop`，使每个 `Step d F` 都给「circular ＋ 每个叶在某个 split 一侧」，
且每个对称 `d` 都有 `F` 使 `Step d F`。**`Step` 与输入 `d` 无关** —— `_iff_star` 把整个命题压成
「每个 `X` 上存在星形族」，`d` 在残量里彻底消失。故它是 `_holds`（`NeighborNet.lean:3361`）一行零假设收口。
② 忠实形态：把 `Step` 从**关系**改成**算法函数** `agglomerate : (X→X→ℝ) → Finset (Split X) → Finset (Split X)`，
并证三条不变式：(i) 输出 circular；(ii) 逐步保持「cluster 是 partial order 的理想」；(iii) `d` 本身是 circular 距离时输出精确恢复（NN 的一致性）。
③ **降级**（`[判定收档]`）。这条最该降：它是唯一「名字像算法、内容是一行 `_holds`、且 `d` 被消去」的。
④ 缺：Neighbor-Net 凝聚本体（Bryant–Moulton 2004 §3）：split 相容/partial order 的计算、cluster 合并、循环性判定
（`Circular` 已有）。量级 **800–1500 行**，大头是「逐步保持 circularable」的不变量。

### 4. `canonicalSplitDecomposition_gap_correct_shape_legacy`（`BunemanIndexBridge.lean:728`）→ 建议 **保持登记（`_legacy`，已在 `[追溯]`）**

① 证的是：对任意对称 `δ`，`∃ F, c, δ₀`，`c > 0`、`δ₀` split-prime、`δ = δ₀ + Σ c_s δ_s`。
证明取 `F := univ`、`c ≡ M`（巨大常数）、`δ₀ := δ − M·Σδ_s` ⇒ `δ₀` 非对角**任意负** ⇒ split-prime 空真。
即「系数全压同一个巨数」的构造，与 BdD Thm 2 的**规范唯一性**无关。
② 忠实形态 = **已在库里的正名那条** `canonicalSplitDecomposition_gap`（`:1156`，收口 `_holds:4428`）：
`SplitPrimeFaithfulPartition δ₀` ＋ `δ₀` 非负 ＋ `δ₀` 对角 0 ＋ 分解，四要素齐全。W36-7b 已把旧形态打进 `[追溯]`。
③ **保持登记**。要做的只是 docstring 里点明「本形态的 `F, c` 与忠实形态不同」（已有类似措辞），**不动桶**。
④ 无缺口。量级 **0**（忠实形态已证）。

### 5. `bootstrap_confidence_gap`（`Phylo/Stat/Bootstrap.lean:1031`）→ 建议 **降级**

① 证的是：`∃ Ω TrueSplit p`，`p ∈ [0,1]`、`p(ω, TrueSplit ω) > 1/2`、且 `p > 1/2` 的 `s` 与 `TrueSplit ω` 相容。
取 `Ω := Empty` ⇒ 三条 `∀ω` **全空真** ⇒ `↔ True`（`_iff_true:1088`）。**这是 6 条里最彻底的空转**：
连 `Ω` 都不必非空。
② 忠实形态：把 `p` 钉成 `bootstrapSupport`（库内已有定义），要证的是
「重抽样支持度 `≥ 1−α` ⟹ 真树含 `s` 的概率 `≥ 1−α`」。⚠️ **这不是纯组合命题**：
它在统计上依赖「真树生成数据 ⟹ 重抽样树族以高概率含真 split」，需要数据生成模型 + 重抽样分布 + 渐近。
③ **降级**（`[判定收档]`）。理由：登记形态与 bootstrap 的置信语义之间**没有桥**，且忠实形态不是定理而是启发式；
库里应如实登记「只有支持度的定义」。另一条路是**加强成可证的条件命题**（把「真树含 s」挪进前提），但那样只剩定义重述。
④ 缺：统计层 —— `bootstrapSupport`（有）＋ 数据生成模型（`MSCFreq`/`SiteFreq` 有）＋ 重抽样分布
（`Resample`/`weightOf` 有，`multinomial_weight_count_gap` 已证）＋ 渐近（`EmpiricalConvergence` 有一部分）。
量级 **2000+ 行**，且**数学上需要额外假设**（bootstrap 一致性不是无条件定理）。

### 6. `msc_split_probability_object_gap`（`Phylo/Stat/SplitProbabilities.lean:552`）→ 建议 **降级**

① 证的是：`∀n≥3 ∀ε≥0`，`∃ σ Displays P`，使 (i) 平凡 split 上 `P = 1`、(ii) `Σ_r P s r = 2(2n−3)`、
(iii) `P ≥ (1/3)e^{−ε}` 的 split 被 `Displays`。见证 `σ := Unit`、`Displays := True`、
`P := ` 平凡取 1 ＋ 锚点取 `2n−6` ⇒ (ii) 是**恒等式** `2n + (2n−6) = 2(2n−3)`、(iii) 由 `Displays := True` 恒真。
② 忠实形态：`σ` 钉成基因树空间（`RankedTree n` / 拓扑空间）、`Displays` 钉成「基因树展示 split」、
`P s r` 钉成 **MSC 下的 split 概率**（Yang 2002 / Allman–Degnan–Rhodes 的 closed form），
并要求账目与 `P(triv) = 1` 是**从模型算出来的**，而不是压进 `P` 的定义。
③ **降级**（`[判定收档]`）。可信度高于第 1/2/3 条（账目本身是对的），高在「账目是 MSC 的真性质」，
但登记形态把它当定义用 ⇒ 仍然零内容。
④ 缺：把 `σ` 固定为 `RankedTree n` 并把 `P` 定义成 MSC 概率（可复用库内 `mscConcordant`、
`RankedGeneTree` 的计数、`card_trivial_splits_gap` 已证的部分），再证 `Σ = 2(2n−3)`。量级 **800–1200 行**。

### 汇总（**建议**，不动桶）

| # | 缺口 | 现桶 | 建议 | 若采纳，桶位变化 | 器材量级 |
|---|---|---|---|---|---|
| 1 | `quarnetRules_level1_gap` | 已收口 | 降级 | 已收口 43 → 42，判定收档 2 → 3 | 1500–2500 行 |
| 2 | `level1QuartetSystem_gap` | 已收口 | 降级 | （同上，若 1、2 都降则 43 → 41，判定收档 → 4） | 600–1000 行 |
| 3 | `neighborNetAgglomeration_gap` | 已收口 | 降级 | 再 −1 | 800–1500 行 |
| 4 | `canonicalSplitDecomposition_gap_correct_shape_legacy` | **追溯** | 保持（`_legacy`） | 不变 | 0 |
| 5 | `bootstrap_confidence_gap` | 已收口 | 降级 | 再 −1 | 2000+ 行 |
| 6 | `msc_split_probability_object_gap` | 已收口 | 降级 | 再 −1 | 800–1200 行 |

★ 若 5 条全降：`已收口 43 → 38`、`判定收档 2 → 7`，**合计仍 72**（`list_gaps.sh` 的口径 A/B 不受影响，
因为降级只换桶、不改名字 ⇒ **没有静默删债**）。注意 `已收口 38` 恰好等于「严格口径 = 43 − 5 条空转」
（见 W36 记录），所以这个建议其实是把口径**显式化**，不是新增判断。

---

## 复跑/维护

* 桶位：`bash scripts/list_gaps.sh B`
* **全表 44 行的归类 + 机械依据：`bash scripts/check_vacuous.sh`**（W39-3 起，44/44 全覆盖；
  它同时核对【已收口】条目数 43 ＋ 1 条 legacy = 44，条目数一变脚本就红）
* 已证伪源码标记：`bash scripts/check_refuted.sh`
* 本表的「用途证据 / 一行依据」两列是**人工审计结论**（证据是否「非退化」要人判），
  但**归类与机器依据**已由 `check_vacuous.sh` 机械核验 ⇒ 不是纯字符串匹配。
