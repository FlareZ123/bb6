"""Generate the 445 archived non-FAR exact-key witnesses. Lean checks each.
Usage: python prepare_d100_bank.py BANK_DIRECTORY OUTPUT_DIRECTORY
BANK_DIRECTORY contains the extracted d100-{far,ngram,structured} artifacts.
"""
import json, sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent7-raw36-b1le'))
from stack_candidates import generate

b,out=map(Path,sys.argv[1:3])
out.mkdir(parents=True,exist_ok=True)
far={t.replace('_',''):v for t,v in json.loads((b/'d100-far/candidate.json').read_text())['fars']}
ng={t.replace('_',''):v for t,v in json.loads((b/'d100-ngram/ngram.json').read_text())}
st={t.replace('_',''):v for t,v in json.loads((b/'d100-structured/structured.json').read_text())}
assert len(far)==1773 and len(ng)==883 and len(st)==268
assert len(set(far)&set(ng))==706 and not set(st)&(set(far)|set(ng))
rows=sorted((t,v) for t,v in (ng|st).items() if t not in far)
assert len(rows)==445
m=generate(rows,out,stem='Raw36D100Bank',ns='BB6.Agent7Raw36D100Bank')
(out/'D100BankMap.json').write_text(json.dumps(m,sort_keys=True))
