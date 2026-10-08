import Phylo

/-! # `W10Probe.lean` —— W10c（`MSCProof`）的**反空真探针**（协调侧自写，**不登记进 `Phylo.lean`**）

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
