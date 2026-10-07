"""把 PDF 的每一页渲染成 PNG 图像。

**为什么用渲染而不是提取内嵌图像**：
PDF 里的内嵌图像可能是 1-bit CCITT、且位序/镜像可能被 pypdf 误解码 ——
实测 `BryantSteel1995*.pdf` 用 pypdf 提取出的图完全不可读（OCR 全页乱码），
而用 PDFium **渲染**同一页则清晰可辨。
⇒ **扫描件一律用本脚本**；`extract_img.py` 仅在渲染不可用时备用。

用法：
    python render_pages.py <pdf> <输出目录> [scale]
    # scale: 渲染倍率，2.0 ≈ 144dpi，3.0 ≈ 216dpi，4.0 ≈ 288dpi
    # 扫描件建议 3.0–4.0；内嵌图分辨率低时提高 scale 也无损（矢量渲染）

输出命名：<basename>_p01.png, <basename>_p02.png, ...
"""
import os
import sys

import pypdfium2 as pdfium

src, dst = sys.argv[1], sys.argv[2]
scale = float(sys.argv[3]) if len(sys.argv) > 3 else 3.0

os.makedirs(dst, exist_ok=True)
base = os.path.splitext(os.path.basename(src))[0]
doc = pdfium.PdfDocument(src)
n = 0
for i in range(len(doc)):
    try:
        img = doc[i].render(scale=scale).to_pil()
    except Exception as e:
        print(f'  p{i+1}: render error {e}')
        continue
    out = os.path.join(dst, f'{base}_p{i+1:02d}.png')
    img.save(out)
    n += 1
print(f'{base}: {len(doc)} pages rendered at scale={scale} -> {dst}/ ({n} files)')
