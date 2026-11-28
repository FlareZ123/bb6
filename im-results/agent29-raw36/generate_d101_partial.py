"""Generate the source-checkable active-certificate subset for direct Raw36 D1=0LB."""
import base64, hashlib, json, lzma, subprocess, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
from active_cert import generate

PARENT="1RB---_1RC---_0RD---_0LD0LB_------_------"
DIGEST="ad90b7aa9a5268eb5b045e84ffab208cd3bcbbbdfb86a6724f32b5730a34d41c"
MISSING=[
"1RB1LB_1RC1LE_0RD0RF_0LD0LB_1LF---_0LA0RF",
"1RB1LE_1RC1RE_0RD0RB_0LD0LB_1LB1LF_---0LA",
"1RB1LF_1RC0RE_0RD1RA_0LD0LB_1LF---_0LA1LC",
"1RB1LF_1RC1LE_0RD0RE_0LD0LB_0LA0RE_1LB---",
"1RB1LF_1RC1LE_0RD1RB_0LD0LB_0LA0RC_1LB---",
"1RB1LF_1RC1LE_0RD1RB_0LD0LB_0LA0RE_1LB---",
"1RB1RE_1RC1LE_0RD0RB_0LD0LB_1RA0LF_---1LD",
]
def main(out):
    out=Path(out); out.mkdir(parents=True,exist_ok=True)
    got=json.loads(subprocess.check_output(["node",str(ROOT/"canonical_search.cjs"),PARENT,"4","tree"],text=True))
    keys=sorted(t.replace("_","") for t in got["opens"])
    assert len(keys)==len(set(keys))==320
    assert got["stats"]["score"]==450
    assert hashlib.sha256("\n".join(keys).encode()).hexdigest()==DIGEST
    fixture=json.loads(lzma.decompress(base64.b64decode((ROOT/"direct-01-partial.json.xz.b64").read_text())))
    assert fixture["bound"]==450 and fixture["digest"]==DIGEST and len(fixture["data"])==320
    records=[]; missing=[]
    for key,v in zip(keys,fixture["data"]):
        pretty="_".join(key[i:i+6] for i in range(0,36,6))
        if v is None: missing.append(pretty); continue
        assert v[0]=="a"
        records.append([pretty,*v[1:]])
    assert len(records)==313 and sorted(missing)==sorted(MISSING)
    modules=generate(records,out,"Raw36D101")
    report={"parent":PARENT,"bound":450,"open_count":320,"active_closed":313,
            "remaining":missing,"open_digest":DIGEST,"module_count":len(set(x[0] for x in modules.values()))}
    (out/"report.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,indent=2))
if __name__=="__main__":
    main(sys.argv[1])
