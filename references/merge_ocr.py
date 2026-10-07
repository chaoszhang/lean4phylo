"""把 ocr/ 里的逐页 OCR 文本按页合并成可读 Markdown。

用法：python merge_ocr.py <base> "<标题>" "<附注>"
兼容两种图像命名：<base>_pNN.png（渲染）与 <base>_pNN_M.jpg（内嵌图提取）。
"""
import collections
import glob
import os
import re
import sys

base, title, note = sys.argv[1], sys.argv[2], sys.argv[3]
files = glob.glob(f'ocr/{base}_p*_*.txt') + glob.glob(f'ocr/{base}_p*.txt')
files = sorted(set(files))
if not files:
    print(f'{base}: 无 OCR 文件!')
    sys.exit(1)

byp = collections.defaultdict(list)
for f in files:
    m = re.search(rf'{re.escape(base)}_p(\d+)(?:_(\d+))?\.txt$', f)
    if not m:
        continue
    byp[int(m.group(1))].append((int(m.group(2) or 0), f))

parts = [f'# {title}\n\n{note}\n\n---\n']
for pno in sorted(byp):
    chunks = []
    for _, f in sorted(byp[pno]):
        chunks.append(open(f, encoding='utf-8', errors='replace').read().strip())
    txt = '\n\n'.join(c for c in chunks if c)
    parts.append(f'\n## [第 {pno} 页]\n\n{txt}\n')

out = f'md/{base}.md'
with open(out, 'w', encoding='utf-8', newline='\n') as fh:
    fh.write('\n'.join(parts))
print(f'{out}: {os.path.getsize(out)} bytes, {len(byp)} 页')
