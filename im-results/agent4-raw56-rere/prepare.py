#!/usr/bin/env python3
"""Regenerate candidate certificates using original repository search and Lean emitters."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
S = json.loads((HERE / "spec.json").read_text())
AUTO = ROOT / "im-results/agent4-two-sided-automata"
FAR = ROOT / "im-results/agent19-raw40-cut/farbank.cpp"
CUT = ROOT / "im-results/agent7-raw49/cut.cpp"

def blob(path, expected):
    data = path.read_bytes()
    assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == expected, path

def main():
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    for path, digest in [
        (CUT,"88d5dfc4994f8bd203fe3f3def5ea90efda86037"),
        (FAR,"30cac1862b3b88d7ba596b359a9dc8503163593d"),
        (AUTO/"rlelearn.py","4fc0339941c0feca523aaef0a03151e64c4db68d"),
        (AUTO/"emit_automata.py","f1adf13d773570a98e70daffb49c40b0e33aec7b"),
        (AUTO/"TwoSidedAutomata.lean","c04bf81e19d55b3d028c714e628246a4b917f03c"),
    ]:
        blob(path,digest)
    for name, source in [("cut",CUT),("farbank",FAR)]:
        subprocess.run(["g++","-O3","-std=c++20",str(source),"-o",str(out/name)],check=True)
    stem=out/"RERB"
    subprocess.run([str(out/"cut"),S["parent"],str(S["cap"]),str(S["lookback"]),str(S["maxDepth"]),str(stem)],check=True)
    tree, opens, bank=[stem.with_suffix(x) for x in [".json",".open",".far"]]
    rows=opens.read_text().splitlines()
    assert len(rows)==len(set(rows))
    query="".join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(rows))
    with bank.open("wb") as f:
        subprocess.run([str(out/"farbank"),"5"],input=query.encode(),stdout=f,check=True)
    covered={int(i) for i,c in (x.split() for x in bank.read_text().splitlines())}
    assert all(0 <= i < len(rows) for i in covered)
    models={x["table"] for x in S["automata"]}
    assert models <= set(rows)
    assert not {s for i,s in enumerate(rows) if i not in covered}-models
    sys.path.insert(0,str(AUTO))
    from emit_automata import emit, run
    gen=out/"generated"
    gen.mkdir(exist_ok=True)
    fragments=["import TwoSidedAutomata","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace BB6.Agent4Raw56RERBAutomata","open BB6Coverage"]
    for i,model in enumerate(S["automata"]):
        p=model["table"].replace("_","")
        p=[p[j:j+3] for j in range(0,36,3)]
        cert=run(p,model["params"],model["params"])
        assert cert[0], model
        assert cert[1]==model["states"], (model,cert[1])
        fragments.append(emit(i,p,cert))
    fragments.append("end BB6.Agent4Raw56RERBAutomata")
    (gen/"Raw56RERBAutomata.lean").write_text("\n".join(fragments)+"\n")
    subprocess.run([sys.executable,str(HERE/"emit_rerb.py"),str(tree),str(opens),str(bank),str(gen)],check=True)
    manifest=gen/"manifest.json"
    modules=json.loads(manifest.read_text())
    manifest.write_text(json.dumps([["Raw56RERBAutomata",["TwoSidedAutomata"]]]+modules,indent=2)+"\n")
    for p in [tree,opens,bank,manifest]:
        print(p.name,hashlib.sha256(p.read_bytes()).hexdigest())

if __name__=="__main__":
    main()
