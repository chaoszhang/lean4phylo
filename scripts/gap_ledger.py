#!/usr/bin/env python3
# ============================================================================
# gap_ledger.py —— 口径 B：缺口「六桶」收口台账（W25-B 重写，取代旧的机械四桶）
#
#  ★ 为什么要重写（W25 派单 B 的四条理由，逐条对应）：
#   (1) 旧判据只认 `_holds` / `_proof` ⇒ **10 条 `_proved` 收口被误记成 `[开放]`**；
#   (2) 旧判据不检查收口定理是否吃假设 ⇒ 条件收口混进「已收口」，也无法单列；
#   (3) 旧台账没有「已证伪」桶 ⇒ 12 条**已有形式化反例**的缺口一直挂在「开放 50」里；
#   (4) `_false` / `_refuted` / `not_*` 三种反例命名要统一识别。
#
#  ★ 判定规则（写死在此，不再漂移）：
#   一条「缺口」= 名字里含 gap/Gap **且** 用 `def` 落盘的声明（口径 A）。
#   对每个缺口 N，按下表**依次**判，命中即停：
#
#   | 顺序 | 桶 | 判据 |
#   | - | - | - |
#   | 1 | `[追溯]` | 名字以 `_legacy` 结尾（已证伪旧形态的追溯登记，W22 起） |
#   | 2 | `[判定收档]` | 在 `ARCHIVED_JUDGED` 白名单（老师明文认可"任务完成"；**无可证内容**） |
#   | 2′ | `[长期开放]` | 在 `LONGTERM_OPEN` 白名单（老师裁定"**Conjecture 不证**"；**有可证内容但不证**，2026-10-23 起） |
#   | 3 | `[已证伪]` | 库内存在 `not_N` / `N_refuted` / `N_false*` / `N_not_universal` |
#   | 4 | `[条件收口]` | 收口定理：(a) 比 `def` **多吃显式假设**，或 (b) 把 `def` 的某参数**特化** |
#   | 5 | `[已收口]` | 存在**无条件、无特化**的收口定理 |
#   | 6 | `[真开放]` | 其余（= **我们要证的**） |
#
#   ★ 收口定理的命名后缀（**按此顺序匹配，取第一条命中**）：
#     `_holds` → `_proved` → `_true` → `_of_isBinary` → `_proof`
#     （`_of_isBinary` 是为谓词式缺口准备的**无条件**变体，如
#      `pauplinFormula_gap_of_isBinary (T) : pauplinFormula_gap T`。）
#     ⚠️ 同族里还有**带假设**的变体（`pauplinFormula_gap_of_correct_shape (T) (h : …)`），
#     它们**不算收口** —— 脚本按下面的"假设判据"机械区分，不靠名字。
#
#   ★ 假设判据（老师 W25 B′-1 的原文口径）：
#     收口定理的**显式** `(…)` 绑定中，凡**名字不在 `def` 自己的绑定里**的，即为**假设**；
#     `{…}` 隐式绑定与 `[…]` 类型类绑定**一律不算假设**；量化变量 / 数据参数 / 类型类 / 数据约束不算。
#     ★ `section` 里 `variable (… )` 声明的名字（如 `ind`）**算 `def` 自己的绑定**
#       （Lean 会把它自动加进 `def` 的隐式参数表）。
#     例：`variance_empFreq_gap_proved (ind) (m) (μ) [IsProbabilityMeasure μ] (S) (hS : S.card = 4) (q)`
#     里 `(hS : S.card = 4)` 与 `(ind)` **都不算假设** —— 前者是 `def` 的参数，后者是 section 变量。
#     ★ 若本脚本判错，**以人工核对为准**（老师：★D 我的验证优先）；脚本对每条都会打印完整签名供核。
#
#   ★ 「特化判据」：收口定理的类型把 `def` 应用到**非变量实参**（如 `{p | Factorizable p}`、字面量）
#     ⇒ 只覆盖了一部分 `def` 的参数取值 ⇒ 记 `[条件收口]` 并写明「特化」。
#     （现有实例：`edgeInvariants_suffice_gap_correct_shape_holds` 把 `Model` 固定成因子分解点集。）
#
#   ★ 「已证伪」的三种**形态**（B′-2 要求写精确，不许笼统）：
#     `闭命题` ／ `全称闭包为假` ／ `某实例` ／ `谓词式（逐点为假）` ／ `谓词式（反例附加数据条件）`。
#     其中 12 条的形态经**人工逐条核对**（W25-B，见 FORM_OVERRIDE），脚本只做兜底推断。
#
#  ★ 诚实声明：本脚本只做**机械扫描 ＋ 一张人工核对表**，不判忠实性、不判卡点；
#    忠实性以各 `def` 的 docstring 与文献为准（口径 B 不管这件事）。
#
#  用法：cd lean4phylo && python3 scripts/gap_ledger.py
# ============================================================================
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PHYLO = os.path.join(ROOT, "Phylo")

# ===== 判定收档白名单（W24 新增；老师 2026-10-17 认可「任务完成」）=====
# 加入条件（三条全须满足）：
#   (a) 没有可证内容 —— 谓词式 或 已被判不忠实；
#   (b) 库内已有反空真见证；
#   (c) 老师明文认可「判定完成 / 任务完成」（不是 dsh 自己说了算）。
# 现值：rStarConsensus_gap —— (a) 谓词式 ＋ W19 判不忠实；(b) rStarConsensus_gap_strictSplits；
#       (c) W24 派单「A-10 任务完成，代码归档」。
ARCHIVED_JUDGED = ["rStarConsensus_gap", "bme_pauplin_identity_gap"]
# ★ 2026-10-23 老师裁定：`bme_pauplin_identity_gap`（原形态）**收档** —— 不再作为待证条目。
#   技术备注（协调侧镜像实测）：它其实**2 行就能条件收口**
#   （`_binary_holds` 给 `∃ T`，`_of_binary` 直接给本体，带 `2 ≤ |X|`）；
#   若将来要恢复，落成 `…_of_card` 即可，不需新数学。

# ★ 2026-10-23 老师裁定：**Conjecture 不证** ⇒ 单独一桶「[长期开放]」。
#   与 `[判定收档]` 的区别：收档 = **无可证内容**；长期开放 = **有可证内容，但我们决定不证**。
LONGTERM_OPEN = ["toricIdeal_generated_in_degree_le_four_gap"]

# ===== 已证伪条目的形态（W25-B 人工逐条核对 2026-10-19；脚本推断只作兜底）=====
FORM_OVERRIDE = {
    "nniDistance_exact_gap": "某实例（`4` 叶树、`∅` 分裂集、`{exS₀}`）＋ 另有 `_not_universal`",
    "circularDistanceRealization_gap": "某实例（`Fin 3`，反例族 `_false_at_fin3`）",
    "atteson_reduction_gap": "某实例（`X := Fin 4`）",
    "arrowTreeQuasiOrder_gap": "闭命题（`¬ gap.{u}`）",
    "greedyConsensus_gap": "闭命题（`¬ gap`）",
    "pauplinEdgeCoeff_gap": "谓词式（反例附加数据条件：binary `T` ＋ 边 `e ∉ graph`）",
    "greedy_gap": "谓词式（逐点为假：`∀ T, ¬ greedy_gap T`）",
    "canonicalSplitDecomposition_gap": "闭命题（`¬ gap.{0}`）",
    "edgeInvariants_suffice_gap": "全称闭包为假（`¬ ∀ U Model, …`）",
    "generalModelIdentifiability_gap": "全称闭包为假（`¬ ∀ Θ …,`）",
    "rfPoissonAsymptotic_gap": "闭命题（`¬ gap`）",
    "maxQuartetDistance_gap": "闭命题（`¬ gap`）",
    "ContinuousPriorPosteriorConsistencyGap":
        "全称闭包为假（`¬ gap.{0}`；反例：`prior = δ₀`、`lik ≡ 1`、真值 `1`）",
}

# ===== 收口定理「只有特化、没有全称」的条目（人工核对；W25-B）=====
# 现有唯一实例：`edgeInvariants_suffice_gap_correct_shape_holds` 把 `Model` 固定成
# `{p | Factorizable p}` —— 只覆盖「正确取法」这一族 `Model`，一般 `Model` **未覆盖**
# （docstring 自己写明：「修复形态在「`Model` = 因子分解点集」这一正确取法下是真的」）。
# ⇒ 记 `[条件收口]`，欠的是「一般 `Model` 全称版」（这不是 `(h : P)`，是**特化**，故单列说明）。
# ===== 「空转缺口」标注（W25 人工判定）=====
# 收口定理**存在且无假设**，但被证的 `Prop` **不承载它名字所指的数学内容** ——
# `def` 把本应是**常量/已定义对象**的规则做成了**存在量词绑定的自由变量**，
# 于是取退化数据即满足（例：`consistent := fun _ => True`、`minimallyDense := fun _ => False`）。
# ⇒ 机制上记 `[已收口]`（真值已定），但必须挂 ⚠：**真缺口要改命题才可陈述**。
VACUOUS = {
    "quarnetRules_level1_gap":
        "空转：四条规则（consistent/minimallyDense/cyclative/saturated）是存在量词绑定的自由变量，"
        "取退化数据即真；真缺口缺「允许环的网络载体 ＋ N|A 限制算子 ＋ quarnet 类型学」",
    "level1QuartetSystem_gap":
        "空转：`QuartetSystem`/`multiplicity` 同样被存在量词绑定；真缺口同 `quarnetRules_level1_gap`",
    "neighborNetAgglomeration_gap":
        "空转：`∃ Step` 是自由槽 ⇒ 输入 `d` 与算法都消失；残量 `_iff_star` 把它钉成「每个 X 上存在星形族」。"
        "真缺件四件：Cluster 载体 / 簇距离与极小化选择 / 约化式 / 反演展开（md:453–465 等）",
    "canonicalSplitDecomposition_gap_correct_shape":
        "空转：只需「∃ 某个分解」，取退化 δ₀ = δ − M·Σδ_s 即可（非对角任意负）。"
        "真 BdD Thm 2 还要求 ① 残差仍在 M(X)（δxx=0/非负/三角）② 系数 = 隔离指数 α_s ③ 唯一性",
    "bootstrap_confidence_gap":
        "空转（假设槽）：`∃ Ω TrueSplit p` 三个都是自由槽 —— 取 `Ω := Empty` 则三条 `∀ ω` 全空真 ⇒ `↔ True`（连一个 Split 都不需要）。"
        "真缺件三件：① `p` 与 `bootstrapSupport` 的桥（重抽样树族上的 pushforward）② 弱收敛（bootstrap→抽样分布）③ 估计量相容性",
    "msc_split_probability_object_gap":
        "空转（退化见证）：`σ := Unit`、`Displays := True`、`P r = if IsTrivialSplit r then 1 else if r = r₀ then 2n−6 else 0` "
        "即满足账目 `2n + (2n−6) = 2(2n−3)` ⇒ 对一切 `n ≥ 3` 为真（把 W12a 的 Python 复核 n≤10 升为全 n 定理）。"
        "真缺件：① 一般 n 的 `MSCTreeLaw n` ② 带枝长（>ε）的 binary 物种树载体 —— 补上可一次解锁 4 条缺口（含三条 clan 律）",
}

# ===== 「证伪只打在归约目标上」的条目（W26 人工判定）=====
# 情形：库内确实有 `_refuted` 定理，但它证的是 **`def` 的某个归约目标/全称闭包** 为假，
# **不是** `def` 本体为假（本体仍开放）。这类若机械记 [已证伪] 会**过度声称**。
PARTIAL_REFUTE = {
    "bme_pauplin_identity_gap":
        "证伪只打在**归约目标的全称闭包**上：`bme_pauplin_identity_gap_refuted : ∃ T, ¬ BmePauplinNormalization T`（`star4Tree`，"
        "4 叶星形中心度 4 ⇒ plane 和 = 3 ≠ 2）。`def bme_pauplin_identity_gap δ` 本体（`δ.FourPoint → δ.PositiveDefinite → ∃ …`）**仍开放**，"
        "故本行记 [真开放]，并另立二叉忠实形态 `bme_pauplin_identity_gap_binary`",
}

SPEC_OVERRIDE = {
    "edgeInvariants_suffice_gap_correct_shape":
        "特化：`Model` 固定为 `{p | Factorizable p}`（一般 `Model` 未覆盖）",
}

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|noncomputable\s+)*"
                     r"(theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.’]+)")
VAR_RE = re.compile(r"^variable\s+\{?(.*)$")
GAP_RE = re.compile(r"(gap|Gap)")


def strip_lean_comments(text):
    """★ W27 修：把 Lean 注释替换成等长空白（保留换行，行号不变）。

    起因（真实事故）：`Phylo/Stat/HookLength.lean` §21 的 docstring 里有个

    ```text
    theorem rankedFiberCount_gap_holds : rankedFiberCount_gap := by ...
    ```

    的「收尾装配草图」，旧版按行 grep 扫到这一行就把缺口误判成 `[已收口]`
    （台账一度报 真开放 6，实为 7）。注释里的声明**不是**声明。
    """
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0:
            if text.startswith("/-", i):
                depth = 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                if j < 0:
                    j = n
                out.append(" " * (j - i))
                i = j
                continue
            ch = text[i]
            if ch == '"':
                # 字符串字面量：整段跳过，避免把里面的 `--`/`/-` 当注释
                out.append(ch)
                i += 1
                while i < n:
                    c = text[i]
                    if c == "\\" and i + 1 < n:
                        out.append(text[i:i + 2])
                        i += 2
                        continue
                    out.append(c)
                    i += 1
                    if c == '"':
                        break
                continue
            out.append(ch)
            i += 1
        else:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def read_lines(path):
    with open(path, "rb") as f:
        raw = f.read().decode("utf-8").replace("\r\n", "\n")
    # 注释先抹成空白，再切行（行号与原文一一对应）
    return strip_lean_comments(raw).split("\n")


def cut_assign(text):
    """Cut at the first `:=` at paren/bracket depth 0."""
    depth = 0
    i = 0
    while i < len(text) - 1:
        c = text[i]
        if c in "({[⦃":
            depth += 1
        elif c in ")}]⦄":
            depth = max(0, depth - 1)
        elif depth == 0 and text[i:i + 2] == ":=":
            return text[:i]
        i += 1
    return text


def sig_of(lines, i):
    """i = 0-based index of the decl line; signature up to (excl.) a top-level `:=`."""
    buf = []
    for j in range(i, min(i + 60, len(lines))):
        buf.append(lines[j])
        joined = " ".join(buf)
        if cut_assign(joined) != joined:
            return cut_assign(joined)
    return cut_assign(" ".join(buf))


def parse_binders(sig, name):
    """Top-level binder groups after `name`; returns (binders, type_text)."""
    k = sig.find(name)
    if k < 0:
        return [], ""
    s = sig[k + len(name):]
    out = []
    i, n = 0, len(s)
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    stop = None
    while i < n:
        c = s[i]
        if c == ":":
            stop = i
            break
        if c in pairs:
            close = pairs[c]
            depth, j = 0, i
            while j < n:
                if s[j] == c:
                    depth += 1
                elif s[j] == close:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            text = s[i:j + 1]
            kind = {"{": "implicit", "⦃": "implicit", "[": "inst"}.get(c, "explicit")
            inner = s[i + 1:j]
            names = []
            if ":" in inner:
                left = inner.split(":", 1)[0]
                names = [t for t in re.split(r"[\s(){}]+", left) if t]
            out.append((kind, names, text))
            i = j + 1
        else:
            i += 1
    type_text = s[stop + 1:] if stop is not None else ""
    return out, type_text


def binder_names(binders):
    ns = set()
    for kind, names, _ in binders:
        for t in names:
            ns.add(t)
    return ns


def section_var_names(lines):
    """Names declared by `variable (…)` / `variable {…}` in this file (per-file, coarse but sound)."""
    names = set()
    for ln in lines:
        m = re.match(r"^\s*variable\b(.*)$", ln)
        if not m:
            continue
        body = m.group(1)
        for grp in re.findall(r"[\(\{⦃]([^)\}⦄]*)[\)\}⦄]", body):
            if ":" in grp:
                left = grp.split(":", 1)[0]
                for t in re.split(r"[\s]+", left):
                    if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", t):
                        names.add(t)
    return names


def scan_files():
    files = []
    for dirpath, _, fnames in os.walk(PHYLO):
        for fn in sorted(fnames):
            if fn.endswith(".lean"):
                files.append(os.path.join(dirpath, fn))
    files.sort()
    decls = []
    secvars = {}
    for p in files:
        lines = read_lines(p)
        rel = os.path.relpath(p, ROOT).replace(os.sep, "/")
        secvars[rel] = section_var_names(lines)
        for i, ln in enumerate(lines):
            m = DECL_RE.match(ln)
            if not m:
                continue
            decls.append((rel, i + 1, m.group(1), m.group(2), sig_of(lines, i)))
    return decls, secvars


def main():
    decls, secvars = scan_files()
    gaps = [d for d in decls if d[2] == "def" and GAP_RE.search(d[3])]
    gaps.sort(key=lambda d: (d[0], d[1]))

    by_short = {}
    for d in decls:
        if d[2] in ("theorem", "lemma"):
            by_short.setdefault(d[3].split(".")[-1], []).append(d)

    by_lower = {}
    for k, v in by_short.items():
        by_lower.setdefault(k.lower(), []).extend(v)

    def find(*names):
        # ★ 大小写不敏感（Lean 习惯：`def TreeMarkovFactorGap` 的收口定理常写成
        #   `treeMarkovFactorGap_holds`，首字母小写）—— 先精确匹配，再按小写匹配。
        for nm in names:
            hit = by_short.get(nm)
            if hit:
                return sorted(hit, key=lambda d: (d[0], d[1]))[0]
        for nm in names:
            hit = by_lower.get(nm.lower())
            if hit:
                return sorted(hit, key=lambda d: (d[0], d[1]))[0]
        return None

    CLOSURE_SUFFIXES = ["_holds", "_proved", "_true", "_of_isBinary", "_proof", "_degenerate"]
    buckets = {k: [] for k in ("refuted", "closed", "cond", "trace", "judged", "longterm", "open")}

    for (rel, ln, kind, name, sig) in gaps:
        if name.endswith("_legacy"):
            buckets["trace"].append((rel, ln, name, "名字以 `_legacy` 结尾 ⇒ 已证伪旧形态的追溯登记", None))
            continue
        if name in ARCHIVED_JUDGED:
            buckets["judged"].append((rel, ln, name, "在白名单 ARCHIVED_JUDGED 内（老师认可「任务完成」）", None))
            continue
        if name in LONGTERM_OPEN:
            buckets["longterm"].append((rel, ln, name,
                "在白名单 LONGTERM_OPEN 内（老师裁定「Conjecture 不证」：**有可证内容但不证**，不进派单）", None))
            continue

        # ---- 3) 已证伪 ----
        ref = find("not_" + name, name + "_refuted", name + "_false", name + "_not_universal")
        if ref is None:
            cands = [d for k, v in by_short.items() for d in v if k.startswith(name + "_false")]
            if cands:
                ref = sorted(cands, key=lambda d: (d[0], d[1]))[0]
        if ref is not None:
            if name in PARTIAL_REFUTE:
                buckets["open"].append((rel, ln, name, PARTIAL_REFUTE[name], None))
                continue
            form = FORM_OVERRIDE.get(name) or "形态待人工核 ⚠"
            buckets["refuted"].append((rel, ln, name, form, ref))
            continue

        # ---- 4/5) 收口 ----
        cl = None
        for suf in CLOSURE_SUFFIXES:
            cl = find(name + suf)
            if cl is not None:
                break
        if cl is None:
            buckets["open"].append((rel, ln, name, "", None))
            continue

        crel, cln, ckind, cname, csig = cl
        dbind, _ = parse_binders(sig, name)
        cbind, ctype = parse_binders(csig, cname)
        have = binder_names(dbind) | secvars.get(rel, set())
        extra = [t for (k, ns, txt) in cbind if k == "explicit" and any(n not in have for n in ns)
                 for t in [txt]]
        # 特化判据：类型里把 def 应用到**集合构造**（`{p | …}`）这类非变量实参。
        # （`(X := X)` / `.{0}` / 把 def 应用回自己的参数，都**不算**特化 —— 那些是恒等实例化。）
        spec = ""
        if re.search(r"\{[^{}]*\|", ctype):
            spec = "集合构造实参（如 `{p | Factorizable p}`）"
        if name in SPEC_OVERRIDE:
            spec = SPEC_OVERRIDE[name]
        if extra or spec:
            note = []
            if extra:
                note.append("多吃的假设：" + " ".join(extra))
            if spec:
                note.append("特化（%s）：`def` 的参数没有被全称覆盖" % spec)
            buckets["cond"].append((rel, ln, name, "；".join(note), cl))
        else:
            buckets["closed"].append((rel, ln, name, VACUOUS.get(name, ""), cl))

    total = sum(len(v) for v in buckets.values())
    names = [d[3] for d in gaps]
    uniq = len(set(names))
    dup = sorted({n for n in names if names.count(n) > 1})

    def show(tag, key):
        print("  【%s】%d 条" % (tag, len(buckets[key])))
        for (rel, ln, name, note, d) in buckets[key]:
            print("    %-52s %s:%d" % (name, rel, ln))
            if d is not None:
                drel, dln, dkind, dname, dsig = d
                print("      ↳ %s  %s:%d" % (dname, drel, dln))
                t = dsig.strip()
                print("        %s" % (t if len(t) <= 200 else t[:197] + "…"))
            if note:
                print("        · %s" % note)
        print("")

    print("=== 口径 B：七桶（已证伪 / 已收口 / 条件收口 / 追溯 / 判定收档 / 长期开放 / 真开放）===")
    show("已证伪", "refuted")
    show("已收口", "closed")
    show("条件收口", "cond")
    show("追溯", "trace")
    show("判定收档", "judged")
    show("长期开放", "longterm")
    show("真开放", "open")

    print("  口径 B 合计 = %d 行（%d 个不同名）" % (total, uniq))
    if dup:
        print("  ⚠️ 同名重复定义（**不去重**，故行数 > 名字数）：%s" % ", ".join(dup))
    print("  口径 B：真开放 = %d · 已收口 = %d · 条件收口 = %d · 已证伪 = %d · 追溯 = %d · 判定收档 = %d"
          " · 长期开放 = %d"
          % (len(buckets["open"]), len(buckets["closed"]), len(buckets["cond"]),
             len(buckets["refuted"]), len(buckets["trace"]), len(buckets["judged"]),
             len(buckets["longterm"])))
    print("  ✓ 七桶加总 = %d = 本脚本解析条数 %d（★ W28-D 起 `list_gaps.sh` 的口径 A 也先剥注释，"
          "故 A 的行数应与此处相等；旧版差异源自 docstring 里的幽灵声明）" % (total, len(gaps)))
    if total != len(gaps):
        print("  ✗ 加总不守恒！", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
