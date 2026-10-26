# 已收口缺口的「非退化实例」覆盖率报告（W35 · item 9①）

> **来源**：外部审查 `lean4phylo_review.md` §A 第 3 条 —— `scripts/check_vacuous.sh` 只对 **7** 条
> （6 条 VACUOUS ＋ 1 条已修复的 `TreeMarkovFactorGap`）设了机械判据，其余「已收口」条目**没人管**。
> 本报告是对**全部 44 条「已收口」**的逐条核查，回答：**这条缺口除了「真值已定」，有没有被用在具体对象上？**
>
> **这不是判据改动**：`gap_ledger.py` / `list_gaps.sh` / `check_vacuous.sh` 的口径**一字未改**；
> 本报告是覆盖度审计，结论**不回写**台账桶位（桶位仍以 `bash scripts/list_gaps.sh B` 为准）。
>
> **实测日期**：2026-10-27（W35）。行号为该次实测，`W35-7a` 给部分 `def` 的 docstring 加了标记行，
> 故与旧文档里的行号可能差 1–3 行；**权威行号以 `bash scripts/list_gaps.sh` 的输出为准**。

## 方法与判定（三选一）

| 判定 | 含义 |
|---|---|
| **有非退化实例** | 库内另有定理把这个 gap 用在**具体对象**上（具体 `Fin 4` / 具体树 / 具体 `δ` / 具体数值；表内给 `文件:行`）；或闭命题且证明用了实质数学且已接到具体模型 |
| **无** | 既不是自由槽，也没有任何具体实例用途 —— 正规 `∀ … → 结论` 形态，但没人在具体对象上用它 |
| **疑似自由槽** | `def` 体内 `∃` 绑定的**数据**可任意取退化值使 Prop 恒真（表内写出该退化见证）；6 条已登记 VACUOUS 者标「已登记」 |

⚠️ **「含 `∃`」不等于自由槽**（本报告最重要的方法论结论）：

* `circularIndicatorFullRank_gap` 的 `∃ n f` 在**前件**里（结论是 `Function.Injective …`）⇒ 不是；
* `atteson_reduction_gap_correct_shape` 的 `∃ (Y : Type u) … (δm)` 绑定了**类型数据**，
  但三条取值等式把见证**钉死** ⇒ 不是；
* `neighborNetAgglomeration_gap` 的 `∃ Step` **无任何值约束**，且 `_iff_star` 把它与输入 `d` 双向消去 ⇒ **是**。

⇒ 按名字或「含 `∃`」分桶会把前两条误判成第三条。**故本报告是逐条读源码得出的，不是脚本自动分桶。**

## 汇总（44 条）

| 判定 | 条数 | 说明 |
|---|---|---|
| **有非退化实例** | **23** | 有具体的 `文件:行` 证据（多数是 `example` 或 `_fin4/_card_four` 一类的逐字实例） |
| **无** | **15** | **不是空转**：零假设收口、证明含真数学，只是库里没有具体对象实例或下游消费者 |
| **疑似自由槽** | **6** | 与 `gap_ledger.py` 的 `VACUOUS` 白名单**完全重合**（6/6）—— 这是两个独立口径互证 |

★ 回答派单的问题：「44 条里几条有非退化实例」= **23 条**；
「几条疑似空转」= **6 条**（全部已登记、且 `check_vacuous.sh` 有机械依据）；
剩下 **15 条**是「真证明、零实例」—— 建议（不改判据）在台账里单列一栏，而不是混进收口。

## 总表（44 条，`#` 与 `list_gaps.sh`【已收口】的打印顺序一致）

| # | 缺口名 | def 位置 | 收口定理 | 陈述形态 | 收口吃假设? | 非退化实例 / 用途证据 | 判定 | 一行依据 |
|---|---|---|---|---|---|---|---|---|
| 1 | `nniDistance_min_gap` | `Phylo/Algorithm/NNINeighborhood.lean:641` | `nniDistance_min_gap_proved:645` | 参数化谓词 | 零假设 | `tree_nniDist₁₂_eq_one:758`（`Fin 4` 具体 `tree₁/tree₂`，真实 1 步；比 `_nonempty:650` 的 0 步自反强） | 有非退化实例 | `n,S,S'` 都出现在结论里；`∃!k` 被 `NNIDist` 钉住，取不到恒真见证 |
| 2 | `circularIndicatorFullRank_gap` | `Phylo/Algorithm/NeighborNet.lean:435` | `circularIndicatorFullRank_gap_proved:1170` | 闭命题 | 零假设 | `alm_injective_of_three_le:2444`（`Fin n` 弧族 `Alm` 上用同一 §7 逆矩阵工具）；`Arc n` 模型 `arcSplit_isCyclicArc:2283` | 有非退化实例 | 证明是显式逆矩阵（`circularIndicator_injective:884`）；`∃n f` 在前件、结论不含它 |
| 3 | `neighborNetAgglomeration_gap` | `Phylo/Algorithm/NeighborNet.lean:452` | `neighborNetAgglomeration_gap_holds:3360` | 闭命题（含 ∃ 自由槽） | 零假设 | 残量 `neighborNetAgglomeration_gap_iff_star:3337`；库内退化见证 `example:1216`（`Step := (F = trivialSplitSet X)`） | 疑似自由槽（已登记 VACUOUS） | 取 `Step d F := (F = starSplits X h2)`，与 `d` 无关 ⇒ `d` 在 `_iff_star` 中整个消失 |
| 4 | `circularDistanceRealization_gap_corrected` | `Phylo/Algorithm/NeighborNet.lean:1300` | `circularDistanceRealization_gap_corrected_holds:3210` | 闭命题 | 零假设 | `circularWeights_realization_gap_fin_le_five:2000`（`X := Fin n`、`f := refl` 的 `n = 3,4,5` 特化）；`circularRealization_fin4:1603` | 有非退化实例 | `F,w` 须逐点实现 `d`；取 `F = ∅, w = 0` 只对零距离成立 |
| 5 | `circularWeights_realization_gap` | `Phylo/Algorithm/NeighborNet.lean:1672` | `circularWeights_realization_gap_proved:2976` | 参数化谓词（`n`） | 零假设 | `circularWeights_realization_gap_fin_le_five:2000` = 本 gap 在 `n = 3 ∧ 4 ∧ 5` 的逐字实例 | 有非退化实例 | `w` 被 `phyleticDist F w = d` 钉住；`n = 3,4,5` 已逐字实例化 |
| 6 | `atteson_lemma11_gap` | `Phylo/AttesonRadius.lean:850` | `atteson_lemma11_gap_holds:940` | 参数化谓词（`δ`） | 零假设（连 `PositiveDefinite` 都未用） | 无具体 `δ` 实例：`IsCherrySeparated` 全库无实例定理；`_holds` 无消费者 | 无 | `δmin` 仅受 `0 < δmin` 约束的数值松弛槽；无具体 `δ` 实例、无消费者 |
| 7 | `atteson_reduction_gap_correct_shape` | `Phylo/AttesonRadius.lean:1354` | `atteson_reduction_gap_correct_shape_proved:1370` | 闭命题 | 零假设 | 原形态在具体 `exDiss`（`Fin 4`、`θ = 1/2`）上被否：`atteson_reduction_gap_refuted:1144`；本形态无实例定理 | 无 | `∃Y,q,δm` 被三条取值等式钉死；无具体对象实例（原形态 `:1144` 已否） |
| 8 | `mnCorollary_gap` | `Phylo/ConsensusAxioms.lean:497` | `mnCorollary_gap_proof:800` | 闭命题 | 零假设 | 无具体 `C` 实例；`thresholdRule_mnSet:233` / `thresholdRule_isNTree:289` 只证正向，未碰本 gap | 无 | `t` 由 `C P = ThresholdRule k t P` 钉住；无具体 `C` 实例 |
| 9 | `QuartetBridgeGap` | `Phylo/FitchGeneral.lean:1149` | `QuartetBridgeGap_holds:1405` | 闭命题 | 零假设 | 见证是具体 7 顶点树 `quartetTree:1183`；逐 `σ` 计算 `fitchCostGen_quartet:1391` | 有非退化实例 | `∀σ` 等式把见证钉死（叶根树给 0 ≠ `Pattern.fitchCost 0`） |
| 10 | `pauplinFormula_gap` | `Phylo/PauplinFormula.lean:940` | `pauplinFormula_gap_of_isBinary:1106` | 参数化谓词（`T`） | 零假设（`IsBinary` 在 Prop 内） | 4 叶端到端 `BMELeastSquares.lean:327`（`15 = l(T)`；`pauplinLength_eq_bmeLength:759` 是 `rfl`） | 有非退化实例 | `l̂ = l` 经 `_of_correct_shape:1092` + `sideDoublingSum_eq_one_of_isBinary` 实质证明 |
| 11 | `pauplinEdgeCoeff_gap_correct_shape` | `Phylo/PauplinFormula.lean:1010` | `pauplinEdgeCoeff_gap_correct_shape_of_isBinary:1028` | 参数化谓词（`T`） | 零假设（`IsBinary` 在 Prop 内） | 4 叶逐边 `ex4S_normalization:1129`（真边归一化和 `= 2`） | 有非退化实例 | 量词收到 `e ∈ T.graph.edgeSet`（原形态 `not_edgeCoeff_forall_eq_two:976` 为假）后实质证成 |
| 12 | `BinaryConnectedEqualsSideGap` | `Phylo/PerfectPhylogeny.lean:483` | `BinaryConnectedEqualsSideGap_holds` `Connectivity.lean:322` | 闭命题 | 零假设 | 无：全库仅 def/收口/docstring，无具体 `T`/`A` 消费者；两半 `:217`/`:283` 亦抽象 | 无 | ∀T A 的桥/跨界边论证实质（`:304–:312`），但无具体 `T`/`A` 实例、无下游 |
| 13 | `MultiStatePairwiseInsufficiencyGap` | `Phylo/PerfectPhylogeny.lean:500` | `MultiStatePairwiseInsufficiencyGap_holds` `PerfectPhylogeny.lean:1333` | 闭命题 | 零假设（选见证 `fitchMeachamF3`） | `fitchMeachamF3` 具体矩阵 `:543`；两两可解 `:1313`、整体不可解 `:938` | 有非退化实例 | 见证矩阵钉为 `F₃`（`:543`）；否定半靠候选二元叶侧必相交（`:938`），取不到恒真见证 |
| 14 | `greedy_gap_correct_shape` | `Phylo/PhyloDiversity.lean:444` | `greedy_gap_correct_shape_proof` `PhyloDiversitySubtree.lean:689` | 参数化谓词（`T`） | 零假设（`T` 即 def 参数） | 无具体树：`PhyloDiversity.lean:404` 自认未构造 `Phylogram` 实例；消费仅泛型 `example` `Subtree:693` | 无 | `∃ prev next` 被 PD 极大性钉住、非自由槽；但无具体树实例、无下游 |
| 15 | `pdExchange_gap` | `Phylo/PhyloDiversity.lean:571` | `pdExchange_gap_proof` `PhyloDiversitySubtree.lean:684` | 参数化谓词（`T`） | 零假设（`T` 即 def 参数） | 消费仅 `greedy_gap_correct_shape_proof` `Subtree:690`（抽象 `T`）；无具体 `T`/`W`/`W'` | 无 | 加权交换不等式无 ∃ 槽，证明经 `HangOff` 不相交计数（`:685`）；无具体实例 |
| 16 | `quarnetRules_level1_gap` | `Phylo/QuarnetRules.lean:358` | `quarnetRules_level1_gap_holds` `:492`（另 `_degenerate:415`、`_iff_display:464`） | 闭命题（含 ∃ 自由槽） | 零假设（退化载体 PUnit） | `_iff_display:464` 把四谓词消去为 `∃F` 残量；`_degenerate:415` 取 `Qnet=Net=PUnit`、`displayedBy≡⊥` | 疑似自由槽（已登记 VACUOUS） | 取 `minimallyDense:=⊥` 使 (a) 空真、`displayedBy:=⊥` 配 `F={()}` 满足 (b)；与 quarnet 无关 |
| 17 | `level1QuartetSystem_gap` | `Phylo/QuarnetRules.lean:378` | `level1QuartetSystem_gap_degenerate` `:401`（唯一收口） | 闭命题（含 ∃ 自由槽） | 零假设（退化见证） | 唯一收口即 `_degenerate:401`；grep 无 `_holds`、无一般形态定理 | 疑似自由槽（已登记 VACUOUS） | 取 `QuartetSystem:=PUnit`、`multiplicity _ Y:=if card Y=4 then 2 else 0`，两合取项恒真 |
| 18 | `weakCompatibilityRealization_gap` | `Phylo/SplitWeak.lean:562` | `weakCompatibilityRealization_gap_holds` `SplitWeak.lean:2547` | 闭命题 | 零假设 | `_card_four:1893`（card=4）、`_card_five:1863`（card=5）为逐字数值实例；`w` 在结论消失（`:550`/`:1917`） | 有非退化实例 | `∃δ` 被 `IsDSplit↔F` 双向刻画钉住；card X=4/5 已逐字落地（`:1893`/`:1863`） |
| 19 | `fourPointCharacterization_gap` | `Phylo/SplitWeak.lean:637` | `fourPointCharacterization_gap_proof` `BunemanIndexBridge.lean:3299` | 闭命题 | 零假设 | 无具体 `F`/`δ` 消费者；证明 = `_reverse:2940` + `_of_noWRealizer:3037`，仅抽象 | 无 | `↔` 两侧为真刻画（`:3037` 起），无恒真见证；但库内无具体 `F`/`δ` 应用 |
| 20 | `fourPointOfSplitMetricSum_gap` | `Phylo/SplitWeak.lean:670` | `fourPointOfSplitMetricSum_gap_proof` `BunemanIndexBridge.lean:2910` | 闭命题 | 零假设 | `example:2405` 在具体 `cexF2`（`Fin 4`、`w≡1`）上证 `FourPointStd`；`:2911` 复用 `:2387` | 有非退化实例 | 三合取项由 `splitMetricSum_X_le_max:2319` 三次重标号（`:2387`）；`cexF2` 实例非平凡 |
| 21 | `notIsDSplit_of_splitMetricSum_gap` | `Phylo/SplitWeak.lean:689` | `notIsDSplit_of_splitMetricSum_gap_holds` `BunemanIndexBridge.lean:3291` | 闭命题 | 零假设 | 抽象消费：`_of_noWRealizer:3051`（`w≡1`）；无具体 `F`/`w` | 无 | 非成员 `¬IsDSplit` 由 (★′) `noWRealizer` 证成；仅作抽象前提，无具体实例 |
| 22 | `multinomial_weight_count_gap` | `Phylo/Stat/Bootstrap.lean:907` | `multinomial_weight_count_gap_proof` `Bootstrap.lean:924` | 闭命题 | 零假设 | `example` `:960`/`:967`/`:974`/`:981`/`:988`：`n=2,w=(2,0)` 等 5 个具体值 | 有非退化实例 | 轨道-稳定化子计数（`:926–:950`）；5 个具体 `(n,w)` 实例（`:960` 起） |
| 23 | `bootstrap_confidence_gap` | `Bootstrap.lean:1031` | `_holds` `Bootstrap.lean:1102`（另 `_iff_true:1088`） | 闭命题（含 ∃ 自由槽） | 零假设（`_holds` = `_iff_true.mpr trivial`） | 无；`exists_confidence_account_for:1112` 反证任意 `s`（含低支持度 `fourAB`）均可当真树 | 疑似自由槽（已登记 VACUOUS） | `Ω:=Empty` 令三条 `∀ω` 空真 ⇒ `↔True`；`Ω/TrueSplit/p` 与 `bootstrapSupport` 之间无桥 |
| 24 | `fourPointOfSplitMetricSum_gap_correct_shape` | `BunemanIndexBridge.lean:658` | `_proof` `:2385` | 参数化谓词 | 零假设（内层吃 `F`、`w`、两两相容、`0<w`） | 有：`example:2403` 取具体 `cexF2`（`Fin 4`、`w≡1`）证 `FourPointStd`；`:2907` 复用于注册形态收口 | 有非退化实例 | 三合取项由 `splitMetricSum_X_le_max`（`:2389`）三次重标号给出；`:2403` 为具体 `Fin 4` 实例 |
| 25 | `canonicalSplitDecomposition_gap_correct_shape` | `BunemanIndexBridge.lean:727` | `_holds` `BunemanIndexBridge.lean:883` | 参数化谓词（含 ∃ 自由槽） | 零假设（`intro α _ _ δ _`，连 `δ` 对称性都不用） | 无 | 疑似自由槽（已登记 VACUOUS） | 取 `F:=univ`、`c≡M=2S+1`、`δ₀:=δ−M·Σδ_s`（非对角任意负）⇒ `SplitPrimeStd` 恒真（`:783`） |
| 26 | `canonicalSplitDecomposition_gap_faithful_v2` | `BunemanIndexBridge.lean:1154` | `_holds` `BunemanIndexBridge.lean:4424` | 参数化谓词（含 ∃，已钉住） | 零假设（内层吃对称/对角 0/非负/三角 4 条） | 仅抽象：`:1780`、`:1796` 给结论类（任意 `F,c`）；无具体 `δ` | 无 | `δ₀` 被「非负+对角 0+划分版 split-prime」钉住；证明靠 `dSplits` 基数下降（`:4402`），无具体实例 |
| 27 | `noWRealizer_exists_gap` | `BunemanIndexBridge.lean:2543` | `_proof` `BunemanIndexBridge.lean:3280` | 参数化谓词（含 ∃，已钉住） | 零假设（证明连 `0<w` 都不用：`:3281` 传 `_hw`） | 仅抽象：`:3288`、`:3296` 作前提；无具体 `F`/四元组 | 无 | ∃ 四元组被 `Σ_{F.filter…} w = 0` 钉住；证明用 `laminar_sideNotMem` 链（`:3211`），无具体实例 |
| 28 | `weakCompatibilityRealization_gap_weights_v2` | `BunemanIndexBridge.lean:4852` | `_holds` `BunemanIndexQuartet.lean:274` | 参数化谓词 | 零假设（内层吃弱相容 + `0<w`） | 仅抽象：`:5267` 是多吃 `coeffFaithfulDecomposition` 的归约；无具体 `F/w` | 无 | `↔` 内的 ∃ 是成员刻画（非槽）；两合取项 = `core_holds` + `isolationIndex_eq_two_mul_weight` |
| 29 | `kolmogorov_extension_gap` | `EmpiricalConvergence.lean:314` | `_proved` `:322` | 参数化谓词（含 ∃，已钉住） | 零假设（吃 `[IsProbabilityMeasure μ₀]`） | 有：`:332`（`Ω₀:=Bool`、`coin`）、`:338` 边缘 `{true}=1/2`、`:344` 联合=边缘乘积 | 有非退化实例 | `∃μ` 被「坐标边缘 `=μ₀` ＋ `iIndepFun`」钉死；`:332–347` 在硬币测度上给具体数值 |
| 30 | `variance_empFreq_gap` | `EmpiricalConvergence.lean:379` | `_proved` `EmpiricalConvergence.lean:401` | 参数化谓词 | 零假设（内层吃 `h01/hint/hindep/hident/hmean`） | 无；`:485` 只证常值 `1/2` 可积 | 无 | 无 ∃；证明 = `variance_eq_integral`＋`variance_fun_sum'` 真内容，但无具体 `S/μ/q` 应用 |
| 31 | `evansSpeed_general_gap` | `HadamardTransform.lean:329` | `_proved` `:457` | 参数化谓词 | 零假设（内层吃 `χ0=1` 与乘法性） | 无模型实例；`:339` 仅证假设可满足（`ℤ`、`(−1)^a`） | 无 | 纯重指标恒等式（`:396`），无树/无 GMM；无具体 `G/π/f` 应用 |
| 32 | `TreeMarkovFactorGap` | `InvariantsRank.lean:367` | `_holds` `:375` | 参数化谓词（含 ∃，已钉住） | 零假设（内层吃 `IsTreeModelFreq P`） | 假设侧：`:311` 零张量实例、`:335` 具体 `deltaFreq`（秩 16）阴性对照；`:379` 消费收口 | 有非退化实例 | 全在 4 叶 `κ=4` 具体层：`:251` `gmmFreq` 为显式 `Fin 4` 矩阵；证明 = `gmmFreq_factorizable` |
| 33 | `MultiLocusPosteriorConcentrationGap` | `MSCBayes.lean:621` | `_holds` `:662` | 闭命题 | 零假设（内层吃 `hnn/hpos/hLpos/hdecay`；`_hsum` 未用） | 无：无任何具体 `ι/prior/perLocus` 被代入 | 无 | 无 ∃ 自由槽，证明 = 指数衰减＋`squeeze_zero'` 真内容；但无具体模型接线 |
| 34 | `rankedTree_card_gap` | `Phylo/Stat/RankedGeneTree.lean:683` | `rankedTree_card_gap_proved` @ `Phylo/Stat/CoalescentHistoryCount.lean:583` | 参数化谓词 | 零假设 | `RankedGeneTree.lean:471`（n=4→H₄）、`CoalescentHistoryCount.lean:600`（n=5→180） | 有非退化实例 | 无 ∃；一般 n 走合并史逐层归纳，n=4/5 有独立数值实例。 |
| 35 | `rankedFiberCount_gap` | `Phylo/Stat/RankedGeneTree.lean:850` | `rankedFiberCount_gap_holds` @ `Phylo/Stat/HookLength.lean:5108` | 参数化谓词 | 零假设 | `RankedGeneTree.lean:1136`（n=4 一般 f）、`:884`（n=3）；`:864` 纤维非空 | 有非退化实例 | 无 ∃；n≥2 由 reconstruct 满射＋LE 收口，n=4 纤维 1/2 有独立实例。 |
| 36 | `sd2012_eq4_uniform_rates_gap` | `Phylo/Stat/RankedGeneTree.lean:896` | `sd2012_eq4_uniform_rates_gap_proved` @ `Phylo/Stat/RankedGeneTree.lean:1030` | 参数化谓词 | 零假设 | `RankedGeneTree.lean:650`（m=2 独立实例）、`:1147-1150`（m=2 复算） | 有非退化实例 | 无 ∃；分母闭形式＋二项式定理实算，m=2 另有独立实例。 |
| 37 | `ranked4_probability_gap` | `Phylo/Stat/RankedGeneTree.lean:907` | `ranked4_probability_gap_proved` @ `Phylo/Stat/RankedGeneTree.lean:1055` | 参数化谓词 | 零假设 | `RankedGeneTree.lean:1153-1158`（t=1 实例）、`:1102`（2+16 纤维计数） | 有非退化实例 | p 被三式钉住、t 经 `mscConcordant t` 进入；c∈(1/3,1)，取 2 个 c/2、16 个 (1−c)/16，p=0 失败。 |
| 38 | `YHKClanLawGap` | `Phylo/Stat/ReciprocalMonophyly.lean:924` | `yhkClanLawGap_holds` @ `Phylo/Stat/RankedTreeClanLaw.lean:1166` | 参数化谓词 | 零假设 | `ReciprocalMonophyly.lean:1481`（n=4 整条）、`:737`（`clanProb 4 2 = 1/3`） | 有非退化实例 | RHS 取 1/3 等非 0/1 值，退化分布填不出；n=4 切片有显式见证。 |
| 39 | `TwoClanLawGap` | `Phylo/Stat/ReciprocalMonophyly.lean:985` | `twoClanLawGap_holds` @ `Phylo/Stat/ClanPairLaw.lean:3458` | 参数化谓词 | 零假设 | `ReciprocalMonophyly.lean:1759`（n=4 整条）、`:1562`（`qn 4 1 2 = 1/3`） | 有非退化实例 | RHS 取 1/3 等非 0/1 值；载体 `RankedTree n`＋`prob≡1/H n` 显式装配。 |
| 40 | `card_trivial_splits_gap` | `Phylo/Stat/SplitProbabilities.lean:407` | `card_trivial_splits_gap_holds` @ `Phylo/Stat/TrivialSplitCount.lean:160` | 参数化谓词 | 零假设 | `TrivialSplitCount.lean:199`（n=4→8）、`:193`（可计算代理 4→8） | 有非退化实例 | 无 ∃；`sideA`/`sideB` 双射实算，n=4 有独立实例 8。 |
| 41 | `msc_split_probability_object_gap` | `Phylo/Stat/SplitProbabilities.lean:552` | `msc_split_probability_object_gap_holds` @ `Phylo/Stat/SplitProbabilities.lean:586` | 参数化谓词（含 ∃ 自由槽） | 零假设 | 退化见证 `SplitProbabilities.lean:605-606`：`σ=Unit`、`Displays=True`、`P`＝平凡 1／锚点 `2n−6` | 疑似自由槽（已登记 VACUOUS） | 取 `σ=Unit`、`Displays=True`、`P` 压锚点即恒真；ε 只剩空转蕴含。 |
| 42 | `quartetMeanEquidistributed_gap` | `Phylo/Stat/TreeMetricDistribution.lean:663` | `quartetMeanEquidistributed_gap_holds` @ `Phylo/Stat/QuartetMeanEquidistributed.lean:225` | 参数化谓词 | 零假设 | 无（`:232` 是 `X=Fin 3` 退化支；`:244` 只核右端 48，未给 n=4 具体 𝒯 实例） | 无 | 无 ∃；证明是 6 侧×k 的实质双计数，但库内无 n≥4 具体 𝒯 上的实例/用途。 |
| 43 | `two_parent_trees_gap` | `Phylo/SupertreeLimits.lean:690` | `two_parent_trees_gap_holds` @ `Phylo/TwoParentTrees.lean:590` | 闭命题 | 零假设 | `TwoParentTrees.lean:578`（`treeP1`/`treeP2` 显式对＋②分类定理） | 有非退化实例 | 显式 T₁/T₂ 展示 prof，分类定理已证；正确形态见证非退化。 |
| 44 | `two_parent_trees_gap_correct_shape` | `Phylo/SupertreeLimits.lean:716` | `two_parent_trees_gap_correct_shape_holds` @ `Phylo/TwoParentTrees.lean:578` | 闭命题 | 零假设 | `TwoParentTrees.lean:578`（`treeP1`/`treeP2`）、`:586`（`sP2a∈T₂∖T₁`） | 有非退化实例 | ③ 直接排除 T₁=T₂；显式 split 系统与 σ 交换逐条 `decide`。 |

## 备注（合并 4 条泳道的发现，按重要性）

### 1. 「已收口」不蕴含「非空转」

`neighborNetAgglomeration_gap_holds`（`NeighborNet.lean:3360`）是一行**零假设**收口，而它正是空转那条。
⇒ `gap_ledger.py` 的「已收口」桶与 `VACUOUS` 集合**有交集**；这也是本报告存在的理由。

### 2. 口径偏高的两条（已收口但比名字弱）

* `atteson_lemma11_gap`（`AttesonRadius.lean:850`）：`δmin` 只是 `∃` 的**数值松弛**（除 `0 < δmin`
  外无约束），证得的是「每个非樱桃对都有 Q 更小的樱桃对」，**不含** Lemma 11 的 `3(n−4)·δmin` 间隙式；
  且它**无消费者**（`njCriterion_minimizer_is_cherry:480` 仍以 `hsep` 为假设）。
* `weakCompatibilityRealization_gap`（`SplitWeak.lean:562`）：`w` 只出现在**假设**里、不进结论
  （`SplitWeak.lean:550`/`:1917` 自认）⇒ 它证的是 BdD Thm 3 的 (1)；系数形态另在
  `weakCompatibilityRealization_gap_weights`（`BunemanIndexBridge.lean:3362`）登记。

### 3. 名字与实际形态不符（不影响判定，但会误导 reader）

* `pauplinFormula_gap` / `pauplinEdgeCoeff_gap_correct_shape` 的收口定理叫 `_of_isBinary`，但都是**零假设**
  （`IsBinary` 是 Prop 内部的蕴含前提，不是多吃进一个假设）。
* `QuartetBridgeGap` 名字无 `_gap` 后缀，且是**具体 `Fin 4` 断言**（不是一般 `n` 的桥）。
* `pdExchange_gap` / `fourPointOfSplitMetricSum_gap` 的具体实例是**匿名 `example`**，按命名定理统计会漏。

### 4. 台账引用可以更准的两处

* `nniDistance_min_gap` 的「非空真」引的是 `_nonempty:650`（`S = S'` 的 0 步自反**退化**见证）；
  真正非退化的实例是 `tree_nniDist₁₂_eq_one:758`（`Fin 4`、真实 1 步）。
* `variance_empFreq_gap` 的 docstring（`EmpiricalConvergence.lean:480–484`）称常值指示 `ind ≡ 1/2`
  使四条前提同时可满足 —— 但 `1/2 ∉ {{0,1}}` 违反前提 1；`:485` 的 `example` 只证常值**可积**。
  ⇒ 目前**没有**机器证据说它非空真（不影响它「已收口」，但「非空真」这句话要撤回或补真见证）。

### 5. `level1QuartetSystem_gap` 只有退化见证

全库 grep 无 `level1QuartetSystem_gap_holds`，唯一收口是 `_degenerate`（`QuarnetRules.lean:401`）。
⇒ item 8 的改名要写成 `_vacuous_degenerate`（不是 `_vacuous_holds`），台账后缀表需同时收两种。

### 6. 4 条已收口的 `def` docstring 仍写「未证 / 仍然开着」

`rankedFiberCount_gap`（`RankedGeneTree.lean:840`）、`quartetMeanEquidistributed_gap`
（`TreeMetricDistribution.lean:646`）、`two_parent_trees_gap`（`SupertreeLimits.lean:689`）、
`two_parent_trees_gap_correct_shape`（`:709`）—— 与台账「已收口」矛盾，属 docstring 漂移，
建议下一批统一订正（本批不动数学陈述，docstring 可改）。

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

## 复跑/维护

* 桶位：`bash scripts/list_gaps.sh B`
* 空转机械依据：`bash scripts/check_vacuous.sh`
* 已证伪源码标记：`bash scripts/check_refuted.sh`
* 本表是**人工审计快照**，不参与 CI 判定（避免把「谁的证据更硬」变成字符串匹配）。
