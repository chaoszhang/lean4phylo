#!/bin/bash
# ============================================================================
#  check_refuted.sh —— 「已证伪缺口」的**源码层标记**机械核（W35 任务 7a）
#
#  ★ 为什么需要这个脚本（外部审查 lean4phylo_review.md §A 第 1 条的原话）：
#    「21 条『已证伪』……至今仍以 `def … : Prop` 的形式躺在库里，旁边配一条 `¬ Gap` 定理。
#      读者 grep『缺口』时会把它们误当成待证目标。」
#    ⇒ 台账层（`list_gaps.sh` 的【已证伪】桶）已经清楚；缺的是**源码层**的可见性。
#      故：每条被证伪的 `def` 的 docstring **首部**必须带
#         ⚠️ **已证伪，非待证目标** —— 机器反例见 `<定理名>`（`<文件>:<行>`）
#      本脚本机器核这件事，缺一条就非零退出。
#
#  ★ 判据（与 `gap_ledger.py` 同源，但**不依赖桶位**）：
#    对每个「名字含 gap/Gap 且用 `def` 落盘」的声明 N，若库内存在反例定理
#         `not_N` / `N_refuted` / `N_false*` / `N_not_universal`
#    则 N 属「已证伪」，其 docstring 必须带标记，且**标记里点名的定理必须存在**
#    （且必须就是那条反例定理）。桶位变动（`_legacy` 追溯等）不影响本判据 ——
#    这是刻意的：标记要求跟「事实上有反例」绑定，不跟台账分桶绑定。
#
#  用法：  bash scripts/check_refuted.sh          # 核 21 条
#          bash scripts/check_refuted.sh -v       # 额外打印每条的反例定理位置
#  退出码：0 = 全部合规；1 = 有缺失（逐条列出）
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

VERBOSE=0
[ "${1:-}" = "-v" ] && VERBOSE=1

python3 - "$VERBOSE" <<'PY'
import os, re, sys

VERBOSE = sys.argv[1] == '1'
ROOT = '.'
PHYLO = 'Phylo'
MARK = '已证伪，非待证目标'
DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*'
                     r'(theorem|lemma|def|abbrev)\s+([A-Za-z0-9_.\']+)')
GAP_RE = re.compile(r'gap|Gap')

# ★ 与台账共用白名单：`PARTIAL_REFUTE`（反例只打在归约目标/全称闭包上，本体仍开放）、
#   `ARCHIVED_JUDGED`、`LONGTERM_OPEN` 的条目**不属**「已证伪」⇒ 本脚本**不要求**它们带标记
#   （否则会与七桶口径冲突：`bme_pauplin_identity_gap` 在台账里是 `[真开放]`＋人工说明）。
sys.path.insert(0, os.path.abspath('scripts'))
try:
    import gap_ledger as _L
    SKIP = set(_L.PARTIAL_REFUTE) | set(_L.ARCHIVED_JUDGED) | set(_L.LONGTERM_OPEN)
except Exception:
    SKIP = set()
    print('（提示：未能读取 gap_ledger.py 的白名单，按空集处理 —— 只多核，不放过）')

files = []
for dirpath, _, fnames in os.walk(PHYLO):
    for fn in sorted(fnames):
        if fn.endswith('.lean'):
            files.append(os.path.join(dirpath, fn))
files.sort()

decls = []            # (rel, line_no, kind, name)
texts = {}
for p in files:
    rel = p.replace(os.sep, '/')
    lines = open(p, encoding='utf-8', errors='replace').read().splitlines()
    texts[rel] = lines
    for i, ln in enumerate(lines):
        m = DECL_RE.match(ln)
        if m:
            decls.append((rel, i + 1, m.group(1), m.group(2)))

by_name = {}
for rel, ln, kind, name in decls:
    if kind in ('theorem', 'lemma'):
        by_name.setdefault(name.split('.')[-1], []).append((rel, ln))
by_lower = {}
for k, v in by_name.items():
    by_lower.setdefault(k.lower(), []).extend(v)

def find_refuter(n):
    """与 gap_ledger.py 同序：not_N / N_refuted / N_false / N_not_universal，然后 N_false* 前缀"""
    for cand in ('not_' + n, n + '_refuted', n + '_false', n + '_not_universal'):
        if cand in by_name:
            return cand, sorted(by_name[cand])[0]
        if cand.lower() in by_lower:
            return cand, sorted(by_lower[cand.lower()])[0]
    pref = [k for k in by_name if k.startswith(n + '_false')]
    if pref:
        k = sorted(pref)[0]
        return k, sorted(by_name[k])[0]
    return None, None

def docstring_range(rel, decl_line):
    """def 行上方最近的 `/-- … -/` 块（容错：跳过属性行 / `set_option … in`）"""
    lines = texts[rel]
    i = decl_line - 2
    end = None
    while i >= 0:
        s = lines[i]
        if end is None and s.strip().endswith('-/'):
            end = i
        if s.lstrip().startswith('/--'):
            return i, end if end is not None else i
        if end is not None and s.strip().startswith('/--'):
            return i, end
        i -= 1
        if decl_line - i > 160:
            break
    return None, None

rows, bad = [], []
for rel, ln, kind, name in decls:
    if kind != 'def' or not GAP_RE.search(name):
        continue
    short = name.split('.')[-1]
    if short in SKIP:
        continue
    thm, where = find_refuter(short)
    if thm is None:
        continue
    a, b = docstring_range(rel, ln)
    block = '\n'.join(texts[rel][a:b + 1]) if a is not None else ''
    ok = MARK in block
    named = thm.lower() in block.lower() if ok else False
    rows.append((short, rel, ln, thm, where, ok, named))
    if not ok:
        bad.append((short, rel, ln, thm, where, '缺少 ⚠️ 标记（docstring 首部）'))
    elif not named:
        bad.append((short, rel, ln, thm, where, '标记未点名反例定理 `%s`' % thm))

print('== 已证伪缺口的源码层标记核查（判据：存在反例定理 ⇒ docstring 必须带 ⚠️ 标记并点名它）==')
for short, rel, ln, thm, where, ok, named in rows:
    stat = '✓' if (ok and named) else '✗'
    print('%s %-50s %s:%d' % (stat, short, rel, ln))
    if VERBOSE:
        print('    ↳ 反例 %s @ %s:%d' % (thm, where[0], where[1]))
print()
print('合计 %d 条已证伪缺口 · 合规 %d · 缺标记/点错 %d' % (len(rows), len(rows) - len(bad), len(bad)))
if bad:
    print()
    for short, rel, ln, thm, where, why in bad:
        print('  ✗ %-50s %s:%d  → %s（反例 %s @ %s:%d）' % (short, rel, ln, why, thm, where[0], where[1]))
    print()
    print('VERDICT: ✗ 有 %d 条不合规 ⇒ 按 W35-7a：给 docstring 首部补标记' % len(bad))
    sys.exit(1)
print()
print('VERDICT: ✓ 全部合规')
PY
