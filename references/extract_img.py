import os, sys
from pypdf import PdfReader
src, dst = sys.argv[1], sys.argv[2]
os.makedirs(dst, exist_ok=True)
r = PdfReader(src)
base = os.path.splitext(os.path.basename(src))[0]
n = 0
for i, p in enumerate(r.pages):
    try:
        imgs = list(p.images)
    except Exception as e:
        print(f'  page {i+1}: image error {e}'); continue
    for j, im in enumerate(imgs):
        ext = (im.name.rsplit('.', 1)[-1] if '.' in im.name else 'png').lower()
        if ext not in ('png','jpg','jpeg','tiff','bmp'): ext = 'png'
        fn = os.path.join(dst, f'{base}_p{i+1:02d}_{j}.{ext}')
        with open(fn, 'wb') as fh:
            fh.write(im.data)
        n += 1
    if not imgs:
        print(f'  page {i+1}: no embedded image')
print(f'{base}: {len(r.pages)} pages, {n} images extracted')
