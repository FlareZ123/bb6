from pathlib import Path
import re

for p in Path("tree").glob("Box12E*S*.lean"):
    s = p.read_text()
    if "import PackedFinite" in s:
        continue
    s = "import PackedFinite\n" + s
    s, n = re.subn(r'treeCheck 200 externalCheck baseBox 7 \(fromCodes (\#\[[0-9,]+\])\) (tree\w+)', r'BB6.Agent48PackedFinite.fastTree 200 externalCheck baseBox 7 \1 \2', s)
    s, m = re.subn(r'treeCheck_sound 200 externalCheck \(externalCheck_sound 200\) baseBox 7 _ _ (check\w+) m hm hp', r'BB6.Agent48PackedFinite.fastTree_sound 200 externalCheck (externalCheck_sound 200) baseBox 7 _ _ (by rfl) \1 m hm hp', s)
    assert n == m and n > 0, (p, n, m)
    p.write_text(s)
