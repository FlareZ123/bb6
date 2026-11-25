"""Regenerate five fixed two-block growth witnesses and the final sparse invariant."""
import json
import sys
import tempfile
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent10-tnf-multipump"))
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
sys.path.insert(0, str(ROOT.parent / "agent47-raw111-cut"))
import multi
import generate_sweeps as one
from emit_sparse import emit

CASES = [
  [
    289,
    27,
    "011",
    "11",
    "0111",
    "111",
    ""
  ],
  [
    317,
    25,
    "011",
    "11",
    "0111",
    "111",
    ""
  ],
  [
    293,
    25,
    "011",
    "11",
    "0011",
    "011",
    ""
  ],
  [
    457,
    29,
    "011",
    "11",
    "0111",
    "0111",
    "0"
  ],
  [
    458,
    29,
    "011",
    "11",
    "0111",
    "0111",
    "0"
  ]
]

def main():
    spec = json.loads((ROOT / "spec-1RE.json").read_text())
    parts = ["import SweepPumping", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0", "set_option linter.unusedVariables false",
             "namespace BB6.Agent1Raw60REMulti", "open BB6Coverage BB6.Agent31Pump"]
    for i,t,pre,I,mid,J,suf in CASES:
        p = one.parse(spec["manual"][str(i)][2])
        w = multi.clean(multi.lit(pre)+multi.rep(I)+multi.lit(mid)+multi.rep(J)+multi.lit(suf))
        v = multi.clean(multi.lit(pre+I)+multi.rep(I)+multi.lit(mid+J)+multi.rep(J)+multi.lit(suf))
        st,tg = multi.C(0,w,()),multi.C(0,v,())
        ans = multi.pump(p,st,tg)
        assert ans is not None,i
        proof,info = multi.generate(i,p,(t,st,tg,ans))
        parts.append(proof)
        print(i,info)
    parts.append("end BB6.Agent1Raw60REMulti")
    (ROOT/"Raw60REMulti.lean").write_text("\n\n".join(parts)+"\n",encoding="utf-8")
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/"ngram"
        source=ROOT.parent/"agent47-raw111-cut/ngram_sparse.cpp"
        subprocess.run(["g++","-std=c++17","-O3",str(source),"-o",str(exe)],check=True)
        table=spec["manual"]["495"][2]
        output=subprocess.check_output([str(exe),"25"],input=f"495 {table}\n",text=True)
        ident,data=output.strip().split(maxsplit=1)
        assert ident=="495"
        emit(ROOT,495,table,data,width=25,module_name="Raw60RESparse",expected=(93002,102,13901))
    import generate
    generate.SPECS["1RE"]=spec
    generate.main("1RE")

if __name__=="__main__":
    main()
