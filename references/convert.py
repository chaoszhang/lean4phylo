import os, sys, re
from pdfminer.high_level import extract_text

src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
for f in sorted(os.listdir(src)):
    if not f.lower().endswith('.pdf'):
        continue
    p = os.path.join(src, f)
    try:
        t = extract_text(p)
    except Exception as e:
        t = f'[EXTRACT ERROR] {e}\n'
    t = t.replace('\r\n', '\n').replace('\r', '\n')
    # 折叠 >2 连续空行
    t = re.sub(r'\n{3,}', '\n\n', t)
    out = os.path.join(dst, f[:-4] + '.md')
    with open(out, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(t)
    print(f'{f:70s} chars={len(t)}')
