from pathlib import Path
import sys
p = Path(sys.argv[1])
s = p.read_text()
old = "(by rw [← h, hc.2])"
new = "(hc.2.symm.trans (congrArg decode h))"
assert s.count(old) == 3
p.write_text(s.replace(old, new))
