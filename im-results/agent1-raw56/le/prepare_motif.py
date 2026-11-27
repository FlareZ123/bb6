#!/usr/bin/env python3
"""Replay motif witnesses and emit source-checkable FastBiDFA leaf modules."""
import hashlib,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BIDFA=ROOT/'im-results/agent32-raw59'
OPEN_SHA='aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef'
def main():
    opens=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    assert hashlib.sha256(opens.read_bytes()).hexdigest()==OPEN_SHA
    rows=opens.read_text().splitlines()
    spec=json.loads((HERE/'motif_spec.json').read_text())
    selected=set(map(int,sys.argv[3:])) if len(sys.argv)>3 else {r['id'] for r in spec}
    spec=[r for r in spec if r['id'] in selected]
    assert {r['id'] for r in spec}==selected
    assert all(rows[r['id']]==r['table'] for r in spec)
    sys.path.insert(0,str(BIDFA));from emit_rungram import emit
    from motif_quotient import minimize
    results=json.loads(subprocess.check_output(['node',str(HERE/'motif_replay.cjs')],input=json.dumps(spec).encode()))
    by_id={s['id']:s for s in spec}
    for z in results:
        d,p,s=minimize(z['table'],z['dfa'])
        z=dict(z,dfa=d,states=len(s),edges=sum(map(len,p))+2)
        assert [z['states'],z['edges']]==by_id[z['id']]['quotient']
        i=z['id'];mod=f'Raw56LEMotif{i}'
        txt='\n'.join(['import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent1Raw56.LEMotif','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',emit(i,z['table'],*z['dfa'],[z['states'],z['edges']]),'end BB6.Agent1Raw56.LEMotif',''])
        (out/(mod+'.lean')).write_text(txt)
        print(i,z['states'],z['edges'],flush=True)
if __name__=='__main__':main()
