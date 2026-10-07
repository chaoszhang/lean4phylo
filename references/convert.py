import os, sys, re
from pdfminer.high_level import extract_text

# ⚠️ 防护：扫描件（无文本层）抽不出文字，直接写会【覆盖】已有的 OCR 结果。
# 若目标 .md 已存在且其大小远超本次抽取结果，则跳过（视作已有 OCR 内容）。
MIN_CHARS = 200

src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)

CID = {
    '88': '∑', '80': '∑', '89': '∏', '45': '−', '48': '′', '49': '″',
    '50': '‴', '65': 'α', '66': 'β', '71': 'γ', '72': 'δ', '101': 'ε',
    '122': 'λ', '109': 'μ', '112': 'π', '115': 'σ', '116': 'τ', '102': 'φ',
    '59': ';', '58': ':', '44': ',', '46': '.',
}


def fix(t):
    t = re.sub(r'\(cid:(\d+)\)', lambda m: CID.get(m.group(1), m.group(0)), t)
    t = t.replace('\ufb01', 'fi').replace('\ufb02', 'fl').replace('\u2019', "'")
    t = re.sub(r'[ \t]+\n', '\n', t)
    t = re.sub(r'\n{3,}', '\n\n', t)
    return t


skipped = []
for f in sorted(os.listdir(src)):
    if not f.lower().endswith('.pdf'):
        continue
    p = os.path.join(src, f)
    out = os.path.join(dst, f[:-4] + '.md')
    try:
        t = fix(extract_text(p))
    except Exception as e:
        t = f'[EXTRACT ERROR] {e}\n'
    # 扫描件防护：抽不出正文 + 目标已存在更大的内容 → 跳过，别覆盖 OCR 结果
    if len(t.strip()) < MIN_CHARS and os.path.exists(out) and os.path.getsize(out) > MIN_CHARS * 4:
        skipped.append(f)
        print(f'{f:70s} SKIP（扫描件，保留已存在的 OCR 文本）')
        continue
    with open(out, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(t)
    print(f'{f:70s} chars={len(t)}')

if skipped:
    print(f'\n⚠️ 跳过 {len(skipped)} 个扫描件（其 .md 为 OCR 产物，勿用本脚本覆盖）:')
    for s in skipped:
        print(f'   - {s}')
