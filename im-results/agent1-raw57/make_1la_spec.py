"""Assemble disjoint candidate partition; no verdict without the Lean audit."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def read(name):
    return json.loads((ROOT/name).read_text())

def spec():
    far=read("1la-far-frontier.json")
    ng=read("1la-ngram-frontier.json")
    wide=read("1la-wide-frontier.json")
    late=read("1la-late.json")
    rl=read("1la-rle-frontier.json")
    deep=read("1la-rle-deep.json")
    pattern=read("1la-pattern-frontier.json")
    bp=read("1la-branch-pump.json")
    s={k:far[k] for k in ("stats","bank","root")}
    s.update(bound=late["bound"],one=[],two=[],ngram={**ng["ngram"],**wide["hits"]},
        automata={i:v["params"] for f in (rl,deep) for i,v in f["hits"].items()},
        pattern_automata={i:v["params"] for i,v in pattern["hits"].items()},
        branch_pumps={i:v for i,v in bp.items() if v is not None},
        late=late["late"],expected_open=far["miss"])
    s["residual"]={str(i):t for i,t in pattern["miss"] if str(i) not in s["branch_pumps"]}
    parts=[set(s[k]) for k in ("ngram","automata","pattern_automata","branch_pumps","late","residual")]
    assert sum(map(len,parts))==len(set.union(*parts))
    assert set.union(*parts)=={str(i) for i,_ in far["miss"]}
    return s
