#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W15a · 箱体先验下 `Ã` / `f̃` / `hint` 被积函数的**一致上界 1** 的数值复核。

★ 本件超出 W13 规格（beyond-spec）：把 CASTER 侧端到端从「确定物种树（Dirac）」
  推广到「一般物种树测度 `ρ` ＋ 叶长有界先验（箱体）」。

被复核的 Lean 结论（`Phylo/Stat/CASTERRateBoxAE.lean`，W15a）
------------------------------------------------------------
  `abs_Abar_le_one_of_box`   : 箱体上 `|Ã θ T' r| ≤ 1`
  `abs_fbar_le_one_of_box`   : 箱体上 `|f̃ θ| ≤ 1`
  `abs_hint_le_one`          : 箱体上 `|∑_{T'} τd θ T' · Ã θ T' T| ≤ 1`
  `deltaBox_le_fbar`         : 箱体上 `deltaBox lmax lx⁻ ≤ f̃ θ`（库内既有，W13b+c）

数值上「箱体」= 叶长 `∈ [0, lmax]`、内部枝长 `lx ≥ lx⁻ > 0`。

本脚本**逐字重实现**了库内的 JC69 权重链（行号取自正本 `b5bd6c6`）：
  `Phylo/JukesCantor.lean:151 e` · `:157 off` · `:187 trans` · `:206 kernel` · `:270 patternProb`
  `Phylo/Stat/CASTERWeights.lean:178 perm` · `:188 wJCBase` · `:199 wJCR`
  `Phylo/Stat/CASTERGeneTree.lean:183 canonLen` · `:207 geneScore` · `:515 jc69Amp`
⇒ 于是本脚本的 `geneScore` **不是**「另一个模型」，而是库内定义的数值镜像；
   [F1] 的**保真度自检**把它钉在库内的**定理**上
   （`patternProb` 全概率 `= 1`：`SiteWeightMeasurable.sum_patternProb`；
    以及 `jc69PropAData.clause_*` 的差分恒等式 `geneScore S l lx S − jc69Amp l lx = geneScore S l lx T'`）。

★ **只用标准库**（与 `scripts/msc/` 其余脚本一致；无 numpy 依赖）。

★ **诚实边界（不藏）**：本脚本复核的是 `geneScore`（`patternProb` 层）到 `Ã` 的**组合**
（凸组合 `w ≥ 0`、`∑ w = 1`；`τd ≥ 0`、`∑ τd = 1`），
**不是**对 `abs_geneScore_le_one` 本身的重新证明（那是库内已证的定理）。

★ **真正的失败路径（★G）**：所有判据都**可以**为假，且都在下面被**显式断言**：
  [F1] 保真度：`∑_σ patternProb = 1` 与 `clause_*` 恒等式（不成立 ⇒ 重实现错了 ⇒ FAIL）；
  [F2] 箱体上界 `|geneScore| / |Ã| / |f̃| / |hint| ≤ 1 + tol`（不成立 ⇒ 主结论可疑 ⇒ FAIL）；
  [F3] **反空洞**：箱体**外**必须能**找到** `|geneScore| > 1`（找不到 ⇒ 本脚本的「非负前提必需」
       这一取舍就**无法失败** ⇒ 假绿 ⇒ FAIL）—— 正是 W14a 教训要求的「判据本身必须能失败」；
  [F4] 下界一致：箱体上 `deltaBox lmax lx⁻ ≤ f̃`（与 W13b+c 的下界定理对拍）；
  [F5] `τd` 是概率权：`τd ≥ 0`、`∑ τd = 1`。
**失败注入自测**：`--inject`（把箱体采样故意换成**箱体外**采样，即注入「漏掉非负前提」这一真实 bug）
或 `--inject=amplify`（把幅度整体放大 8 倍）⇒ 必须**非零退出**且自报 `VERDICT: FAIL`。
"""
import itertools
import math
import random
import sys

# ---------------------------------------------------------------- §0 库内定义的数值镜像
TOPO = ("ab_cd", "ac_bd", "ad_bc")
PATS = list(itertools.product(range(4), repeat=4))          # 256 个模式，字典序
NPAT = len(PATS)
CODE = [((p[0] * 4 + p[1]) * 4 + p[2]) * 4 + p[3] for p in PATS]


def _swap(i, j, x):
    if x == i:
        return j
    if x == j:
        return i
    return x


def perm(T, i):
    """`CASTERWeights.perm`（:178）：`ac_bd → swap 1 2`；`ad_bc → (swap 1 2) ∘ (swap 1 3)`。"""
    if T == "ab_cd":
        return i
    if T == "ac_bd":
        return _swap(1, 2, i)
    return _swap(1, 2, _swap(1, 3, i))          # (swap 1 2) * (swap 1 3)


PERM = {T: [perm(T, i) for i in range(4)] for T in TOPO}


def e(a):
    """`JukesCantor.e`（:151）：`exp(-(4/3) a)`。"""
    return math.exp(-(4.0 / 3.0) * a)


def off(a):
    """`JukesCantor.off`（:157）。"""
    return 0.25 - 0.25 * e(a)


def kernel_mat(t):
    """`JukesCantor.kernel`（= `trans`，:187/:206）在 `t` 处的 4×4 矩阵。"""
    et = e(t)
    K = [[off(t)] * 4 for _ in range(4)]
    for s in range(4):
        K[s][s] += et
    return K


def pattern_probs(t):
    """`JukesCantor.patternProb`（:270）对**全部 256 个模式**求值（按 `CODE` 索引）。"""
    K0, K1, K2, K3, K4 = (kernel_mat(x) for x in t)
    res = [0.0] * NPAT
    for a in range(4):
        K0a, K1a = K0[a], K1[a]
        for b in range(4):
            K2ab, K3b, K4b = K2[a][b], K3[b], K4[b]
            for idx in range(NPAT):
                p = PATS[idx]
                res[idx] += K0a[p[0]] * K1a[p[1]] * K2ab * K3b[p[2]] * K4b[p[3]]
    return [0.25 * x for x in res]


def wjcr_vals(T):
    """`wJCBase`/`wJC`/`wJCR`（:188/:196/:199）：对全部 256 个 `σ` 的权重（按 `σ` 索引）。"""
    pr = PERM[T]
    out = []
    for p in PATS:
        b0, b1, b2, b3 = p[pr[0]], p[pr[1]], p[pr[2]], p[pr[3]]
        if b0 == b1 and b2 == b3 and b0 != b2:
            out.append(1.0)
        elif ((b0 == b1 and b2 != b3 and b2 != b0 and b3 != b0)
              or (b2 == b3 and b0 != b1 and b0 != b2 and b1 != b2)):
            out.append(-0.5)
        else:
            out.append(0.0)
    return out


WJCR = {T: wjcr_vals(T) for T in TOPO}


def canon_len(S, l, lx):
    """`CASTERGeneTree.canonLen`（:183）：`![l(perm S 0), l(perm S 1), lx, l(perm S 2), l(perm S 3)]`。"""
    p = PERM[S]
    return (l[p[0]], l[p[1]], lx, l[p[2]], l[p[3]])


def gene_scores(Sshape, l, lx):
    """`geneScore Sshape l lx T`（:207）对三个 `T` 一次算完（`patternProb` 只算一次）。"""
    pp = pattern_probs(canon_len(Sshape, l, lx))
    pr = PERM[Sshape]
    ppi = [pp[((p[pr[0]] * 4 + p[pr[1]]) * 4 + p[pr[2]]) * 4 + p[pr[3]]] for p in PATS]
    return {T: sum(w * x for w, x in zip(WJCR[T], ppi)) for T in TOPO}


def jc69_amp(l, lx):
    """`CASTERGeneTree.jc69Amp`（:515）：`(3/4)·∏_i e(l i)·(1 − e(lx))`。"""
    p = 1.0
    for i in range(4):
        p *= e(l[i])
    return 0.75 * p * (1.0 - e(lx))


def tau_d(deep, T):
    """`MSCKingman.Kingmanτd`（`MSCKingman.lean:137`）：深合并三拓扑各 `1/3`，否则点质量 `ab|cd`。"""
    if deep:
        return 1.0 / 3.0
    return 1.0 if T == "ab_cd" else 0.0


def scale_theta(model, theta, k):
    """`SiteRateMixture.scale`（`SiteRateMixture.lean:171`）：叶长 `r_k·ρ_k·l`、内枝长 `ρ_k·lx`。"""
    l = [model["r"][k][i] * model["rho"][k] * theta["leaf"][i] for i in range(4)]
    lx = model["rho"][k] * theta["lx"]
    return l, lx


def abar_all(model, theta, gain=1.0):
    """`SiteRateMixture.SiteRateModel.Abar`（:240）：`∑_k w_k · A(scale θ k) T' r`，对全部 `(T',r)`。"""
    acc = {Tp: {T: 0.0 for T in TOPO} for Tp in TOPO}
    for k in range(len(model["w"])):
        l, lx = scale_theta(model, theta, k)
        wk = model["w"][k]
        for Tp in TOPO:
            gs = gene_scores(Tp, l, lx)
            for T in TOPO:
                acc[Tp][T] += wk * gs[T]
    if gain != 1.0:
        for Tp in TOPO:
            for T in TOPO:
                acc[Tp][T] *= gain
    return acc


def fbar(model, theta):
    """`SiteRateMixture.SiteRateModel.fbar`（:244）：`∑_k w_k · f(scale θ k)`。"""
    tot = 0.0
    for k in range(len(model["w"])):
        l, lx = scale_theta(model, theta, k)
        tot += model["w"][k] * jc69_amp(l, lx)
    return tot


def hint_from_acc(theta, acc, T):
    """`CASTERRateBoxAE.abs_hint_le_one` 的被积函数：`∑_{T'} τd θ T' · Ã θ T' T`。"""
    return sum(tau_d(theta["deep"], Tp) * acc[Tp][T] for Tp in TOPO)


def amp_box(model, lmax, lx0):
    """`SiteRateMixture.ampBox`（:395）：`(3/4)·∏_i e(rU·ρU·lmax)·(1 − e(ρL·lx⁻))`。"""
    return 0.75 * (e(model["rU"] * model["rhoU"] * lmax) ** 4) * (1.0 - e(model["rhoL"] * lx0))


def delta_box(model, lmax, lx0):
    """`SiteRateMixture.deltaBox`（:401）：`wRef · ampBox`（`wRef` = 固定正权）。"""
    return model["wRef"] * amp_box(model, lmax, lx0)


# ---------------------------------------------------------------- §1 采样器
def sample_model(rng, K=3, rL=0.5, rU=3.0, rhoL=0.4, rhoU=2.5):
    """抽一个 `SiteRateModel` 的数值实例（界全部 `> 0`，与结构字段一一对应）。"""
    w = [rng.random() + 1e-6 for _ in range(K)]
    s = sum(w)
    w = [x / s for x in w]
    r = [[rng.uniform(rL, rU) for _ in range(4)] for _ in range(K)]
    rho = [rng.uniform(rhoL, rhoU) for _ in range(K)]
    return {"w": w, "r": r, "rho": rho, "wRef": w[0], "rU": rU, "rhoU": rhoU,
            "rhoL": rhoL, "rL": rL}


def sample_theta_box(rng, lmax, lx0, lxmax=4.0):
    """**箱体内**的 `θ`：叶长 `∈ [0, lmax]`、内枝长 `∈ [lx0, lxmax]`、`deep` 任取。"""
    return {"leaf": [rng.uniform(0.0, lmax) for _ in range(4)],
            "lx": rng.uniform(lx0, lxmax),
            "deep": rng.random() < 0.5}


def sample_theta_offbox(rng, lmax, _lx0):
    """**箱体外**的 `θ`（注入用）：允许**负**叶长与**负**内枝长（非负前提被违反）。"""
    return {"leaf": [rng.uniform(-lmax, lmax) for _ in range(4)],
            "lx": rng.uniform(-3.0, 0.0),
            "deep": rng.random() < 0.5}


# ---------------------------------------------------------------- §2 判据
def main(argv):
    inject = None
    for a in argv[1:]:
        if a == "--inject":
            inject = "offbox"
        elif a.startswith("--inject="):
            inject = a.split("=", 1)[1]
    tol = 1e-9
    failures = []
    rng = random.Random(20261012)
    lmax, lx0 = 1.3, 0.2
    n_model, n_theta = 30, 6

    print("=== W15a 箱体先验下的上界复核（Lean: Phylo/Stat/CASTERRateBoxAE.lean）")
    if inject:
        print("    ★★ 失败注入已开启：inject=%s（预期 ⇒ VERDICT: FAIL ＋ 非零退出）" % inject)
    print("    箱体参数：lmax = %s、lx- = %s；tol = %s；模型数 = %d，每模型 theta 数 = %d"
          % (lmax, lx0, tol, n_model, n_theta))

    # --- [F1] 保真度自检：与库内定理对拍
    print("\n[F1] 保真度（把数值镜像钉在库内定理上）")
    f1_summax, f1_clausemax = 0.0, 0.0
    for _ in range(40):
        t = tuple(rng.uniform(0.0, 2.0) for _ in range(5))
        f1_summax = max(f1_summax, abs(sum(pattern_probs(t)) - 1.0))
        l = [rng.uniform(0.0, 2.0) for _ in range(4)]
        lx = rng.uniform(0.0, 2.0)
        for S in TOPO:
            gs = gene_scores(S, l, lx)
            a = jc69_amp(l, lx)
            for T in TOPO:
                if T != S:
                    f1_clausemax = max(f1_clausemax, abs((gs[S] - a) - gs[T]))
    print("    max |sum_sigma patternProb - 1|                    = %.3e   （库内 sum_patternProb）" % f1_summax)
    print("    max |(geneScore S S - jc69Amp) - geneScore S T'|   = %.3e   （库内 clause_*）" % f1_clausemax)
    if not (f1_summax < 1e-9 and f1_clausemax < 1e-9):
        failures.append("[F1] 保真度失败：sum 偏差 %.3e、clause 偏差 %.3e" % (f1_summax, f1_clausemax))

    # --- [F5] τd 是概率权
    print("\n[F5] tau_d 是概率权（非负 ＋ 全概率 1）")
    f5_bad = 0
    for deep in (False, True):
        tot = sum(tau_d(deep, T) for T in TOPO)
        if abs(tot - 1.0) > 1e-15 or any(tau_d(deep, T) < 0.0 for T in TOPO):
            f5_bad += 1
    print("    deep=False/True 两情形：违例数 = %d" % f5_bad)
    if f5_bad:
        failures.append("[F5] tau_d 不是概率权（违例 %d）" % f5_bad)

    # --- [F2] 箱体上的一致上界
    print("\n[F2] 箱体内：|geneScore| / |Abar| / |fbar| / |hint| <= 1")
    max_gs = max_ab = max_fb = max_hint = 0.0
    sampler = sample_theta_offbox if inject == "offbox" else sample_theta_box
    gain = 8.0 if inject == "amplify" else 1.0
    for _ in range(n_model):
        model = sample_model(rng)
        for _ in range(n_theta):
            theta = sampler(rng, lmax, lx0)
            for k in range(len(model["w"])):
                l, lx = scale_theta(model, theta, k)
                for S in TOPO:
                    gs = gene_scores(S, l, lx)
                    max_gs = max(max_gs, max(abs(v) for v in gs.values()))
            acc = abar_all(model, theta, gain=gain)
            for Tp in TOPO:
                for T in TOPO:
                    max_ab = max(max_ab, abs(acc[Tp][T]))
            max_fb = max(max_fb, abs(gain * fbar(model, theta)))
            max_hint = max(max_hint, max(abs(hint_from_acc(theta, acc, T)) for T in TOPO))
    print("    max |geneScore| = %.6f" % max_gs)
    print("    max |Abar|      = %.6f      （Lean: abs_Abar_le_one_of_box）" % max_ab)
    print("    max |fbar|      = %.6f      （Lean: abs_fbar_le_one_of_box）" % max_fb)
    print("    max |hint|      = %.6f      （Lean: abs_hint_le_one）" % max_hint)
    for name, v in (("geneScore", max_gs), ("Abar", max_ab), ("fbar", max_fb), ("hint", max_hint)):
        if not (v <= 1.0 + tol):
            failures.append("[F2] 箱体上界失败：max |%s| = %.6f > 1" % (name, v))

    # --- [F3] 反空洞：箱体外必须能找到破界
    print("\n[F3] 反空洞：箱体**外**必须能找到 |geneScore| > 1（证明『枝长非负』不是装饰）")
    off_max = 0.0
    off_wit = (None, 0.0, None)
    for _ in range(n_model):
        model = sample_model(rng)
        for _ in range(n_theta):
            theta = sample_theta_offbox(rng, lmax, lx0)
            for k in range(len(model["w"])):
                l, lx = scale_theta(model, theta, k)
                for S in TOPO:
                    m = max(abs(v) for v in gene_scores(S, l, lx).values())
                    if m > off_max:
                        off_max, off_wit = m, ([round(x, 3) for x in theta["leaf"]], lx, S)
    print("    max |geneScore|（箱体外） = %.6f   <- 见证：lx = %.3f、leaf = %s"
          % (off_max, off_wit[1], off_wit[0]))
    if not (off_max > 1.0):
        failures.append("[F3] 反空洞失败：箱体外最大 |geneScore| = %.6f <= 1"
                        "（本脚本的取舍判据**无法失败** ⇒ 假绿）" % off_max)

    # --- [F4] 与库内下界定理对拍：deltaBox ≤ fbar（箱体上）
    print("\n[F4] 下界一致：箱体上 deltaBox lmax lx- <= fbar（库内 SiteRateMixture.deltaBox_le_fbar）")
    f4_viol = 0
    f4_min_gap = float("inf")
    f4_db = 0.0
    for _ in range(n_model):
        model = sample_model(rng)
        f4_db = delta_box(model, lmax, lx0)
        for _ in range(n_theta):
            theta = sample_theta_box(rng, lmax, lx0)
            gap = fbar(model, theta) - f4_db
            f4_min_gap = min(f4_min_gap, gap)
            if gap < -1e-12:
                f4_viol += 1
    print("    deltaBox（最后一模型）= %.6e；最小 gap（fbar - deltaBox）= %.3e；违例 = %d"
          % (f4_db, f4_min_gap, f4_viol))
    if f4_viol:
        failures.append("[F4] 下界对拍失败：违例 %d" % f4_viol)

    # --- 结论
    print()
    if failures:
        print("VERDICT: FAIL")
        for f in failures:
            print("  x %s" % f)
        return 1
    print("=> 箱体上 |geneScore|、|Abar|、|fbar|、|hint| 全部 <= 1（界不依赖 k / theta / 速率类别数）；")
    print("   箱体外确实存在 |geneScore| > 1 => Lean 里 abs_geneScore_le_one 的『枝长非负』前提**必需**，")
    print("   即 W15a 的箱体先验（叶长 ∈ [0,lmax] 且内枝长 >= lx- > 0）**不是装饰**。")
    print("VERDICT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
