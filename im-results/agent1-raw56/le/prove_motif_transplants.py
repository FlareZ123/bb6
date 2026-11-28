#!/usr/bin/env python3
"""Reconstruct five new one-hole Raw56 nonhalting certificates from transplanted run grammars.

The candidate search reuses previously successful finite-stack normalization
parameters. Neither discovery nor quotient minimization is trusted: the
existing FastBiDFA Lean checker proves each never-halting assertion.
"""
import hashlib,json,subprocess,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
BIDFA=ROOT/'im-results/agent32-raw59'

# Literal canonical open-table indexes; original global open order pinned in
# triage_remaining.py. For each: table, parameter donor, full witness states/edges.
TARGETS={
  12323:('1RB0RF_1RC---_0RD1RA_1LD1LE_0RF0LE_1LB1RC',20388,9670,2136),
  21463:('1RB0RF_1RC0RE_0RD0RA_1LD1LE_1RB0LE_---0RD',2217,2953,1077),
  21805:('1RB---_1RC0LF_0RD0RF_1LD1LE_1RB0LE_1RA1RC',2217,12644,1739),
  21807:('1RB---_1RC1RB_0RD0RF_1LD1LE_1RB0LE_1RA1RC',20388,4917,1571),
  22621:('1RB1RF_1RC0RE_0RD0RA_1LD1LE_1RC0LE_---1RB',20388,9882,2041),
}

def main():
    out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    original=json.loads((HERE/'motif_spec.json').read_text())
    by_id={x['id']:x for x in original}
    payload=[dict(id=i,table=t,params=by_id[donor]['params'],states=n,edges=e)
             for i,(t,donor,n,e) in TARGETS.items()]
    print('replaying independent motif witness transplants',sorted(TARGETS),flush=True)
    replay=json.loads(subprocess.check_output(['node',str(HERE/'motif_replay.cjs')],
        input=json.dumps(payload).encode()))
    sys.path.insert(0,str(BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize
    rows=[]
    for z in replay:
        i=z['id'];table,donor,n,e=TARGETS[i]
        assert (z['states'],z['edges'])==(n,e) and z['table']==table
        d,P,S=minimize(table,z['dfa'])
        qn,qe=len(S),sum(map(len,P))+2
        assert qn>0 and qe>0 and qn<=n and qe<=e
        mod=f'Raw56LEMotif{i}'
        text='\n'.join([
            'import FastBiDFA','set_option maxRecDepth 100000',
            'set_option maxHeartbeats 0','namespace BB6.Agent1Raw56.LEMotif',
            'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
            emit(i,table,*d,[qn,qe]),'end BB6.Agent1Raw56.LEMotif',''])
        (out/(mod+'.lean')).write_text(text)
        record=dict(id=i,table=table,donor=donor,params=by_id[donor]['params'],
             full=[n,e],quotient=[qn,qe],
             module=mod,sha256=hashlib.sha256(text.encode()).hexdigest(),
             theorem=f'BB6.Agent1Raw56.LEMotif.M{i}.never')
        rows.append(record)
        print('candidate',i,'full',n,e,'quotient',qn,qe,flush=True)
    assert {r['id'] for r in rows}==set(TARGETS)
    (out/'transplants.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
