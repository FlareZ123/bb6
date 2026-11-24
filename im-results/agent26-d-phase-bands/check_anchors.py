"""Check the small phase anchors against the existing explicit macro engine."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "agent37-root-language-pilot"))
from macro_engine import Config, step

anchors = [(5, 10, 123501, "0111111"), (9, 10, 196699, ""),
           (15, 10, 276715, ""), (39, 9, 277451, "")]
early = []
for seed, count, n, suffix in anchors:
    c = Config(seed, "")
    for _ in range(count):
        early.append(c)
        label, cost, nxt = step(c)
        assert nxt is not None, (c, label)
        assert 8*c.n <= 3*nxt.n+23
        assert 3*(nxt.n+len(nxt.suffix)) <= 8*(c.n+len(c.suffix))+40
        c = nxt
    assert c == Config(n, suffix), (seed, c)
    print(seed, count, c)
assert len(early) == len(set(early)) == 39
assert max(c.n for c in early) < min(n for _, _, n, _ in anchors)
print("39 distinct early sections; all precede every anchor in unary length")
