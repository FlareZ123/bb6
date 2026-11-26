from pathlib import Path
import lzma, hashlib
s=lzma.decompress(Path('Agent3PackedFast.lean.xz').read_bytes())
assert hashlib.sha256(s).hexdigest()=='28eaa75ca0e3c9c6d8bc7fc69c88c2c04fff24261c52cd4e33b33590583e0915'
Path('Agent3PackedFast.lean').write_bytes(s)
p=Path('emit_family.py')
p.write_text(p.read_text().replace('Agent3PackedAudit','Agent3PackedFast'))
