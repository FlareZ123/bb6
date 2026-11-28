#!/usr/bin/env python3
"""Original-source conditional Raw56 E0=0LF certificate: 2046 leaves to 1.

The sole unresolved canonical leaf is 3613, not incorrectly treated as
nonhalting. The original Lean canonicalCheck/canonicalSound validates all
other leaves at weighted bound 40000.
"""
import base64,gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
import prepare_le0ra_partial as p
H=Path(__file__).resolve().parent
ROOT=H.parents[2]
OFF=2765
COUNT=2046
BOUND=40000
PARENT='1RB---_1RC---_0RD---_1LD1LE_0LF0LE_------'
def main():
    out=Path(sys.argv[1]).resolve()
    out.mkdir(parents=True,exist_ok=True)
    raw=gzip.decompress(base64.b64decode((H/'inventory-79.json.gz.b64').read_text()))
    p.sha(raw,'869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f')
    inv=json.loads(raw)
    hard={i for i in inv['remaining'] if OFF<=i<OFF+COUNT}
    assert hard=={3613}
    late=[r for r in inv['late'] if OFF<=r[0]<OFF+COUNT]
    assert len(late)==6 and {r[0] for r in late}=={3624,3760,4173,4299,4300,4301}
    assert all((r[1]=='last' and r[2]<BOUND) or (r[1]=='cycle' and r[2]+r[3]<BOUND) for r in late)
    assert not any(OFF<=r[0]<OFF+COUNT for r in inv['sat'])
    extra={i:code for code,ds in inv['fmore'] for i in itertools.accumulate(ds)}
    abstract={i:params for params,ds in inv['abs'] for i in itertools.accumulate(ds)}
    for path,hash in [
      (p.CUT,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),
      (p.FAR,'30cac1862b3b88d7ba596b359a9dc8503163593d'),
      (p.DISC,'8fe2ac5d02e9809ea27904da010833e24b331ad9'),
      (p.BIDFA/'emit_rungram.py','e11a06c9daf6720ee537e6d2dea27daba20d6723'),
      (p.BIDFA/'FastBiDFA.lean','6d31e7e2f081eac524a9c7bb8bd33e55bc1dfd7f'),
      (H.parent/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a'),
    ]:p.pre.blob(path,hash)
    for name,path in [('cut',p.CUT),('farbank',p.FAR)]:
        subprocess.run(['g++','-std=c++20','-O3',str(path),'-o',str(out/name)],check=True)
    stem=out/'0LF'
    subprocess.run([str(out/'cut'),PARENT,'1000','32','6',str(stem)],check=True)
    tf,of,ff=(stem.with_suffix(ext) for ext in ('.json','.open','.far'))
    rows=of.read_text().splitlines()
    assert len(rows)==len(set(rows))==COUNT
    assert rows[3613-OFF]=='1RB---_1RC0RE_0RD0RF_1LD1LE_0LF0LE_1RA0LB'
    print('TREE_SHA256',hashlib.sha256(tf.read_bytes()).hexdigest(),flush=True)
    print('OPEN_SHA256',hashlib.sha256(of.read_bytes()).hexdigest(),flush=True)
    inp=''.join(f"{i} {tab.replace('_','')}\n" for i,tab in enumerate(rows)).encode()
    with ff.open('wb') as stream:
        subprocess.run([str(out/'farbank'),'5'],input=inp,stdout=stream,check=True)
    bf=stem.with_suffix('.bank')
    bf.write_bytes(ff.read_bytes()+''.join(
        f'{i-OFF} {c}\n' for i,c in sorted(extra.items()) if OFF<=i<OFF+COUNT).encode())
    bank={int(i):code for i,code in (line.split() for line in bf.read_text().splitlines())}
    assert len(bank)==1911
    gen=out/'0LFgen'
    gen.mkdir(exist_ok=True)
    sys.path.insert(0,str(p.BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize
    qs=[dict(id=i-OFF,table=rows[i-OFF],p=param)
        for i,param in sorted(abstract.items()) if OFF<=i<OFF+COUNT]
    assert len(qs)==128
    result=json.loads(subprocess.check_output(['node',str(H/'le_replay.cjs'),str(p.DISC)],
                             input=json.dumps(qs).encode()))
    proven={};mods=[]
    for z in result:
        i=z['id'];assert z['table']==rows[i] and i not in bank
        mod=f'Raw56LE0LFBiDFA{i}';ns=f'BB6.Agent1Raw56.LE0LFBiDFA{i}'
        d,g,states=minimize(z['table'],z['dfa'])
        assert len(states)<=z['states'] and sum(map(len,g))+2<=z['edges']
        text='\n'.join(['import FastBiDFA','set_option maxRecDepth 100000',
           'set_option maxHeartbeats 0','namespace '+ns,
           'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
           emit(i,z['table'],*d,[len(states),sum(map(len,g))+2]),'end '+ns,''])
        (gen/(mod+'.lean')).write_text(text)
        proven[i]=ns+f'.M{i}'
        mods.append(mod)
    lateproof={}
    for r in late:
        i=r[0]-OFF
        if r[1]=='last':
            lateproof[i]=f'.last {r[2]} ({r[3]//2},{str(bool(r[3]%2)).lower()})'
        else:
            lateproof[i]=f'.cycle {r[2]} {r[3]} {str(bool(r[4])).lower()} ({r[5]})'
    unresolved={3613-OFF}
    assert set(bank)|set(proven)|set(lateproof)|unresolved==set(range(COUNT))
    assert len(bank)+len(proven)+len(lateproof)+len(unresolved)==COUNT
    print('CLASSIFICATION',len(bank),len(proven),len(lateproof),len(unresolved),flush=True)
    p.PARENT=PARENT
    p.MOD='Raw56LE0LFPartial'
    p.NS='BB6.Agent1Raw56.LE0LFPartial'
    p.BOUND=BOUND
    maker=p.PartialEmitter(rows,json.loads(tf.read_text()),bank,proven,lateproof,unresolved,gen,mods)
    maker.write()
    print('MODULES',len(maker.manifest),flush=True)
if __name__=='__main__':main()
