import os, re, glob
# pdfminer 无法映射的常见 CFF 字形 → 正确字符
CID = {
 '88':'∑', '80':'∑', '89':'∏', '45':'−', '48':'′', '49':'″',
 '50':'‴', '65':'α', '66':'β', '71':'γ', '72':'δ', '101':'ε',
 '122':'λ', '109':'μ', '112':'π', '115':'σ', '116':'τ', '102':'φ',
 '59':';', '58':':', '44':',', '46':'.',
}
def fix(t):
    def rep(m):
        n = m.group(1)
        return CID.get(n, m.group(0))
    t = re.sub(r'\(cid:(\d+)\)', rep, t)
    t = t.replace('\ufb01','fi').replace('\ufb02','fl').replace('\u2019',"'")
    t = re.sub(r'[ \t]+\n', '\n', t)
    t = re.sub(r'\n{3,}', '\n\n', t)
    return t
for f in sorted(glob.glob('md/*.md')):
    t = open(f, encoding='utf-8', errors='replace').read()
    n = fix(t)
    if n != t:
        open(f,'w',encoding='utf-8',newline='\n').write(n)
        print(f'{os.path.basename(f):62s} 已修复')
