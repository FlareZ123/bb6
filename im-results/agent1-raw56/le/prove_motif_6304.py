#!/usr/bin/env python3
"""Construct and independently source-check a transplanted 6304 motif witness.

Candidate found by applying the 6286 run-grammar stack quotient parameters
to a distinct one-hole Raw56 E0=0RA open leaf. Discovery is untrusted.
The unchanged FastBiDFA Lean kernel checker supplies the mathematical proof.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BIDFA=ROOT/'im-results/agent32-raw59'
TABLE='1RB---_1RC0RF_0RD1RC_1LD1LE_0RA0LE_1LD1LA'
EXPECTED=(3001,1059)
ID=6304

def main():
    out=Path(sys.argv[1])
    out.mkdir(parents=True,exist_ok=True)
    spec=json.loads((HERE/'motif_spec.json').read_text())
    base=next(row for row in spec if row['id']==6286)
    payload=[dict(id=ID,table=TABLE,params=base['params'],states=EXPECTED[0],edges=EXPECTED[1])]
    replay=subprocess.check_output(['node',str(HERE/'motif_replay.cjs')],input=json.dumps(payload).encode())
    witness=json.loads(replay)[0]
    assert (witness['states'],witness['edges'])==EXPECTED
    sys.path.insert(0,str(BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize
    d,P,S=minimize(TABLE,witness['dfa'])
    n=len(S)
    e=sum(map(len,P))+2
    assert n>0 and e>0
    module='Raw56LEMotif6304'
    text='\n'.join([
        'import FastBiDFA',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0',
        'namespace BB6.Agent1Raw56.LEMotif',
        'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
        emit(ID,TABLE,*d,[n,e]),
        'end BB6.Agent1Raw56.LEMotif',
        ''
    ])
    (out/(module+'.lean')).write_text(text)
    record=dict(id=ID,table=TABLE,source_id=6286,params=base['params'],
        pre_quotient=dict(states=EXPECTED[0],edges=EXPECTED[1]),
        quotient=dict(states=n,edges=e),
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        method='independently checked FastBiDFA source certificate',
        theorem='BB6.Agent1Raw56.LEMotif.M6304.never')
    (out/'6304-manifest.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps(record,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
