import Phylo

/-! # `W10Probe.lean` —— W10 全批（W10a–W10i ＋ 收口 ＋ 空洞性发现）的**反空真探针**（协调侧自写，**不登记进 `Phylo.lean`**）

目的：证明 `MSCProof` 里的构造**不是空真** —— 实例可居留、真树 quartet 概率**严格为正**、
一般 `X` 的取值引理**真的**能落地、`1/3` **真的是求和**。
本文件**不**属于库（放在仓库根，未登记），只作验收用。 -/

open Phylo.Stat.MSCProof

-- ① `MSCFreq` 可居留（非空真）
example : Nonempty (MSCFreq.{0, 0} (Fin 4)) := mscFreqFin4_nonempty

-- ② 真树 quartet 在该实例下概率**严格为正**（⇒ `majorizes` 的严格不等式**不是空真**）
example : 0 < (mscFreqFin4 1 one_pos).freq.p Finset.univ (by decide)
    ((mscFreqFin4 1 one_pos).q Finset.univ (by decide)) :=
  mscFreqFin4_freq_pos 1 one_pos

-- ③ `1/3` **是求和**（跳链均匀权重在拓扑类上的和），不是写定的常数
example : rootTopoProb = 1 / 3 := rootTopoProb_eq_third

-- ④ 一般 `X`：与真树一致的（有向）split **真的**拿到 `mscConcordant t / 2`
example (t : ℝ) (ht : 0 < t) (S : Finset (Fin 4)) (hS : S.card = 4) :
    (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS (qSplit S hS)
      = mscConcordant t / 2 := by
  show mscPOf t qSplit S hS (qSplit S hS) = mscConcordant t / 2
  exact mscPOf_of_eq (Or.inl rfl)

-- ⑤ 一般 `X`：**一致 split 的 `swap`** 也拿到 `mscConcordant t / 2`（无向性）
example (t : ℝ) (ht : 0 < t) (S : Finset (Fin 4)) (hS : S.card = 4) :
    (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS (qSplit S hS).swap
      = mscConcordant t / 2 := by
  show mscPOf t qSplit S hS (qSplit S hS).swap = mscConcordant t / 2
  exact mscPOf_of_eq (Or.inr rfl)

-- ⑥ 一般 `X`：不一致的 `2|2` 有向 split **真的**拿到 `mscDiscordant t / 2`，
--    且**严格小于**真树的 `mscConcordant t / 2`
example (t : ℝ) (ht : 0 < t) (S : Finset (Fin 4)) (hS : S.card = 4)
    (r : Split ↥S) (hr : r ≠ qSplit S hS) (hrs : r ≠ (qSplit S hS).swap)
    (h2 : r.sideA.card = 2) :
    (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS r = mscDiscordant t / 2 := by
  show mscPOf t qSplit S hS r = mscDiscordant t / 2
  exact mscPOf_of_ne_of_card (fun h => h.elim hr hrs) h2

-- ⑦ 一般 `X`：`1|3` 的 split **真的**拿到 `0`
example (t : ℝ) (ht : 0 < t) (S : Finset (Fin 4)) (hS : S.card = 4)
    (r : Split ↥S) (hr : r ≠ qSplit S hS) (hrs : r ≠ (qSplit S hS).swap)
    (h2 : r.sideA.card ≠ 2) :
    (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS r = 0 := by
  show mscPOf t qSplit S hS r = 0
  exact mscPOf_of_ne_of_not_card (fun h => h.elim hr hrs) h2

-- ⑧ 一般 `X` 上的 `majorizes` **可直接调用**（不是空 `∀`）
example (t : ℝ) (ht : 0 < t) :
    ∀ (S : Finset (Fin 4)) (hS : S.card = 4) (r : Split ↥S),
      r ≠ qSplit S hS → r ≠ (qSplit S hS).swap →
        (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS r
          < (mscQuartetFreqOf t ht.le qSplit qSplit_card).p S hS (qSplit S hS) :=
  mscQuartetFreqOf_majorizes t ht qSplit qSplit_card

/-! ## W10 后续模块的反空真探针（W10a/b/d ＋ 收口 ＋ **空洞性发现**） -/

-- ⑨ 跳链的 `PMF` 等价物**归一**（`Σ = 1`），不是空结构
example : (∑ P : Phylo.Stat.KingmanJumpChain.PartK 4 4,
    Phylo.Stat.KingmanJumpChain.jumpWeight 4 4 P) = 1 :=
  Phylo.Stat.KingmanJumpChain.jumpWeight_sum_eq_one 4 4 (by norm_num) (by norm_num)

-- ⑩ 逗留时间律 `sojournLaw 2` **是概率测度**，且 `P(τ₂ > 0) = 1`
example : Phylo.Stat.KingmanCoalescent.sojournLaw 2 (Set.Ioi 0) = 1 := by
  rw [Phylo.Stat.KingmanCoalescent.sojournLaw_Ioi (by norm_num) 0 le_rfl,
    Coalescent.survival_zero, ENNReal.ofReal_one]

-- ⑪ Theorem 1 的**具体实例**：跳链律 ⊗ 独立指数（`jumpMeasure` 是概率测度）
example : MeasureTheory.IsProbabilityMeasure (Phylo.Stat.KingmanLaw.jumpMeasure 4 4) :=
  Phylo.Stat.KingmanLaw.isProbabilityMeasure_jumpMeasure 4 4 (by norm_num) (by norm_num)

-- ⑫ M1 公式的**测度层**形式：两个测度项之和 = 1（真·概率划分）
example (t : ℝ) : (Phylo.Stat.KingmanCoalescent.sojournLaw 2 (Set.Iic t)).toReal
    + (Phylo.Stat.KingmanCoalescent.sojournLaw 2 (Set.Ioi t)).toReal = 1 :=
  Phylo.Stat.MSCMeasure.branch_partition t

-- ⑬ ★★★ **四处采样结构（修正后）都非空洞** —— 回归护栏。
--     它们**曾是空类型**（`emp` 不依赖真实律/模型，而 `converges` 却对所有模型断言 ⇒ 矛盾）；
--     2026-10-09 已把 `emp` 改为**依赖真实律/模型**，并给出显式居民（原「空性证明」随空结构一并删除）。
example : Nonempty (MSCSampling.{0, 0} (Fin 4)) := mscSampling_nonempty (Fin 4)
example : Nonempty (USTARSampling.{0, 0} (Fin 4)) := ustarSampling_nonempty (Fin 4)
example : Nonempty (CASTERSampling.{0} (Fin 4)) := casterSampling_nonempty (Fin 4)
example : Nonempty (SiteSampling.{0, 0} (Fin 4)) := siteSampling_nonempty (Fin 4)

-- ⑭ ★★★ **形状护栏**：`emp` **依赖真实律/模型**（若被改回「不依赖模型」，此处编译失败）
example (sm : MSCSampling.{0, 0} (Fin 4)) (m : MSCFreq (Fin 4)) :
    ℕ → QuartetFreq (Fin 4) := sm.emp m
example (sm : USTARSampling.{0, 0} (Fin 4)) (M : NJstData.{0, 0} (Fin 4)) :
    ℕ → NJ.Dissimilarity (Fin 4) := sm.emp M
example (sm : CASTERSampling.{0} (Fin 4)) (W : WeightTable (Fin 4)) :
    ℕ → WeightTable (Fin 4) := sm.emp W
example (sm : SiteSampling.{0, 0} (Fin 4)) (M : MSCSite (Fin 4)) :
    ℕ → SiteSupport (Fin 4) := sm.emp M

-- ⑮ ★★★ 修正后的树层谓词 `StatisticallyConsistent` **不是自动成立**的：
--     常值估计量在「存在不同构理论树」时失败（`not_statisticallyConsistent_const`）——
--     即「一致性」在修正后**有内容**，而非换个地方空洞。
example (T : Cladogram.{0, 0} (Fin 4)) (sm : MSCSampling.{0, 0} (Fin 4))
    (h : ∃ m : MSCFreq.{0, 0} (Fin 4), ¬ Nonempty (Iso T m.tree)) :
    ¬ StatisticallyConsistent (fun _ => T) sm :=
  not_statisticallyConsistent_const T sm h

/-! ## 本批最后四块的反空真护栏（一般 `n` 计数 · ADR2011 Lemma 4 · 根部 `1/3`） -/

-- ⑱ ★★★ **一般 `n` 的溯祖历史计数**（纯内核，不是枚举）
example : ((Phylo.Stat.RankedGeneTree.mergeHistories 5).card : ℝ)
    = Phylo.Stat.RankedGeneTree.H 5 :=
  Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_eq_H 5 (by norm_num)

-- ⑲ ★★★ **ADR2011 Lemma 4（主目标）**：任意两个无根拓扑的纤维相等
example (T T' : Phylo.Stat.FiveTaxonLemma4.UnrootedTopology5) :
    ((Phylo.Stat.RankedGeneTree.mergeHistories 5).filter
        (fun f => Phylo.Stat.FiveTaxonLemma4.topoOf 5 f = T.1)).card
      = ((Phylo.Stat.RankedGeneTree.mergeHistories 5).filter
        (fun f => Phylo.Stat.FiveTaxonLemma4.topoOf 5 f = T'.1)).card :=
  Phylo.Stat.FiveTaxonLemma4.lemma4_five T T'

-- ⑳ ★★★ Lemma 4 的**概率版**：每个无根拓扑 `P(T) = 1/15`
example (T : Phylo.Stat.FiveTaxonLemma4.UnrootedTopology5) :
    (∑ _f ∈ (Phylo.Stat.RankedGeneTree.mergeHistories 5).filter
        (fun f => Phylo.Stat.FiveTaxonLemma4.topoOf 5 f = T.1),
        (1 / Phylo.Stat.RankedGeneTree.H 5)) = 1 / 15 :=
  Phylo.Stat.FiveTaxonLemma4.lemma4_five_prob T

-- ㉑ ★★★ **根部 `1/3` 就是跳链在拓扑类上的质量**（**等式**）
example : Phylo.Stat.MSCProof.rootTopoProb
    = ∑ P ∈ (Finset.univ.filter (fun P : Phylo.Stat.KingmanJumpChain.PartK 4 3 =>
        ({0, 1} : Finset (Fin 4)) ∈ P.1.parts ∨ ({2, 3} : Finset (Fin 4)) ∈ P.1.parts)),
      Phylo.Stat.KingmanJumpChain.jumpWeight 4 3 P :=
  Phylo.Stat.RootJumpMass.rootTopoProb_eq_jumpMass

-- ㉒ ★★★ **M1 的完全测度层形式**：内枝用 `expMeasure`、根部用跳链质量（无实数层残留）
example (t : ℝ) (ht : 0 ≤ t) : Phylo.Stat.MSCProof.mscConcordant t
    = (Phylo.Stat.KingmanCoalescent.sojournLaw 2 (Set.Iic t)).toReal * 1
      + (Phylo.Stat.KingmanCoalescent.sojournLaw 2 (Set.Ioi t)).toReal
        * (∑ P ∈ Phylo.Stat.MSCMeasure.TopoClass3,
            Phylo.Stat.KingmanJumpChain.jumpWeight 4 3 P) :=
  Phylo.Stat.MSCMeasure.mscConcordant_eq_measure_jump ht

-- ㉓ ★★★ **ADR2011 公式的单调性**：枝越长 ⇒ 一致概率越高（比单射更强）
example (a b : ℝ) (h : a < b) :
    Phylo.Stat.MSCProof.mscConcordant a < Phylo.Stat.MSCProof.mscConcordant b :=
  Phylo.Stat.Identifiability.mscConcordant_strictMono h
