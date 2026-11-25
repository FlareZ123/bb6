"""A candidate-only overlay. Exact table equality is still checked by the
generated proof and every listed wrapper must supply its kernel proof."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent

def partial_spec(block_far=False):
    spec=json.loads((ROOT/"partial_spec.json").read_text())
    if block_far:
        manifest=json.loads((ROOT.parent/"agent13-block-far/Raw110Candidates.json").read_text())
        for e in manifest:
            kid,j=e["kid"],e["j"]
            s=spec[str(kid)]
            assert j in s["miss"], (kid,j,"candidate not in baseline cut")
            name=f"Raw110B{kid:02d}L{j:03d}"
            extra=s.setdefault("extra",{})
            assert str(j) not in extra
            extra[str(j)]=dict(module=name,namespace=f"BB6.Agent13{name}",table=e["table"])
            s["miss"].remove(j)
    return spec
