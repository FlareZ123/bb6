"""Switch generated child checks to the proven prefix-sharing checker.
The certificate assembly and expected original zipCheck theorem types remain
unchanged. Only the decision procedure used in the kernel proof changes.
"""
from pathlib import Path
import sys,re
raw=sys.argv[1]
root=Path(__file__).resolve().parent.parent/"agent10-tnf-multipump"
for i in range(24):
    f=root/f"Raw{raw}Kid{i:02}.lean"
    s=f.read_text()
    needle=r"(theorem check\d\d : zipCheck [^\n]+ = true := by) decide"
    s,count=re.subn(needle,r"\1\n  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]\n  decide",s)
    assert count==1,(f,count)
    f.write_text("import ZipPrefixAudit\n"+s)
