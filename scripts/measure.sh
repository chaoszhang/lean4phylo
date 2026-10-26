#!/bin/bash
# ============================================================================
#  measure.sh —— README「规模」表所有数字的**可复跑**口径（W35 收进仓库）
#
#  ★ 为什么在仓库里：README 曾写 `bash .w34/measure.sh`，而 `.w34/` 是本机 worktree
#    （从不入库）⇒ 外部读者无法复现规模数字（外部审计 lean4phylo_audit.md §二 / review §B）。
#    本脚本与 README 表的口径**逐字一致**：剥注释后统计。
#
#  ★ 口径（与 README 同）：
#    · 模块数     = `Phylo/**` 的 `.lean` 文件数（须恒等于 `Phylo.lean` 的 `import Phylo.` 条数）
#    · 源行数     = `Phylo/**/*.lean` 的总行数（含 docstring/注释行 —— 与 README「Lean 源行数」一致）
#    · 顶层声明   = 剥注释后，行首（可带修饰符）为
#                   theorem/lemma/def/abbrev/structure/class/instance/inductive 的条数
#    · job 数     = 只能由 `lake build` 实测（本脚本不跑构建，故不打印）
#
#  用法：  bash scripts/measure.sh
#  依赖：  bash + python3（无第三方包）
# ============================================================================
set -u
cd "$(dirname "$0")/.." || exit 9

echo "=== 模块数（Phylo/**/*.lean）与 import 数 ==="
echo "modules=$(find Phylo -name '*.lean' | wc -l) imports=$(grep -c '^import Phylo\.' Phylo.lean) all_lean=$(find . -name '*.lean' | wc -l)"
echo "=== 源行数（Phylo/**/*.lean） ==="
find Phylo -name '*.lean' -print0 | xargs -0 wc -l | tail -1
echo "=== 声明数（剥注释后） ==="
python3 - <<'PY'
import re, pathlib
root = pathlib.Path('Phylo')
def strip(src):
    out=[]; i=0; n=len(src); depth=0
    while i<n:
        if depth==0 and src.startswith('--',i):
            j=src.find('\n',i); j=n if j<0 else j
            out.append(' '*(j-i)); i=j; continue
        if src.startswith('/-',i):
            depth+=1; out.append('  '); i+=2; continue
        if depth>0 and src.startswith('-/',i):
            depth-=1; out.append('  '); i+=2; continue
        out.append(' ' if depth>0 and src[i]!='\n' else src[i]); i+=1
    return ''.join(out)
pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
                 r'(theorem|lemma|def|abbrev|structure|class|instance|inductive)\b', re.M)
tot = 0
for f in sorted(root.rglob('*.lean')):
    tot += len(pat.findall(strip(f.read_text(encoding='utf-8', errors='replace'))))
print('decls =', tot)
PY
echo "=== 缺口台账（七桶） ==="
python3 scripts/gap_ledger.py 2>&1 | tail -2
echo "=== now $(date '+%Y-%m-%d %H:%M') ==="
