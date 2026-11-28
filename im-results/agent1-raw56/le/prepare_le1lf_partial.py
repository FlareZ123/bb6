#!/usr/bin/env python3
"""Original-source conditional Raw56 E0=1LF certificate: 1307 leaves to 1.

The authentic E0=1LF child has two experiment-hard leaves in the frozen
inventory. Global leaf 17858 already has a periodic-stack fixed point; global
leaf 17557 remains explicitly unresolved. The original Lean canonical checker
is the proof boundary for every discharged leaf.
"""
import base64,gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
import prepare_le0ra_partial as p

H=Path(__file__).resolve().parent
ROOT=H.parents[2]
OFF=17498
COUNT=1307
BOUND=7014
PARENT='1RB---_1RC---_0RD---_1LD1LE_1LF0LE_------'
HARD={17557,17858}
MOTIF=17858
UNRESOLVED={17557}

def main():
    out=Path(sys.argv[1]).resolve()
    out.mkdir(parents=True,exist_ok=True)
    raw=gzip.decompress(base64.b64decode((H/'inventory-79.json.gz.b64').read_text()))
    p.sha(raw,'869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f')
    inv=json.loads(raw)
    assert {i for i in inv['remaining'] if OFF<=i<OFF+COUNT}==HARD

    late=[r for r in inv['late'] if OFF<=r[0]<OFF+COUNT]
    assert len(late)==5 and {r[0] for r in late}=={17529,17556,17747,18105,18407}
    assert all((r[1]=='last' and r[2]<BOUND) or
               (r[1]=='cycle' and r[2]+r[3]<BOUND) for r in late)
    assert not any(OFF<=r[0]<OFF+COUNT for r in inv['sat'])

    extra={i:code for code,ds in inv['fmore'] for i in itertools.accumulate(ds)}
    abstract={i:params for params,ds in inv['abs'] for i in itertools.accumulate(ds)}
    for path,h in [
      (p.CUT,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),
      (p.FAR,'30cac1862b3b88d7ba596b359a9dc8503163593d'),
      (p.DISC,'8fe2ac5d02e9809ea27904da010833e24b331ad9'),
      (p.BIDFA/'emit_rungram.py','e11a06c9daf6720ee537e6d2dea27daba20d6723'),
      (p.BIDFA/'FastBiDFA.lean','6d31e7e2f081eac524a9c7bb8bd33e55bc1dfd7f'),
      (H.parent/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a'),
    ]: p.pre.blob(path,h)

    for name,path in [('cut',p.CUT),('farbank',p.FAR)]:
        subprocess.run(['g++','-std=c++20','-O3',str(path),'-o',str(out/name)],check=True)

    stem=out/'1LF'
    subprocess.run([str(out/'cut'),PARENT,'1000','32','6',str(stem)],check=True)
    tf,of,ff=(stem.with_suffix(ext) for ext in ('.json','.open','.far'))
    rows=of.read_text().splitlines()
    assert len(rows)==len(set(rows))==COUNT
    assert rows[17557-OFF]=='1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---'
    assert rows[17858-OFF]=='1RB1RA_1RC0RA_0RD---_1LD1LE_1LF0LE_0RB1LE'
    print('TREE_SHA256',hashlib.sha256(tf.read_bytes()).hexdigest(),flush=True)
    print('OPEN_SHA256',hashlib.sha256(of.read_bytes()).hexdigest(),flush=True)

    inp=''.join(f"{i} {tab.replace('_','')}\n" for i,tab in enumerate(rows)).encode()
    with ff.open('wb') as stream:
        subprocess.run([str(out/'farbank'),'5'],input=inp,stdout=stream,check=True)
    bf=stem.with_suffix('.bank')
    bf.write_bytes(ff.read_bytes()+''.join(
        f'{i-OFF} {c}\n' for i,c in sorted(extra.items()) if OFF<=i<OFF+COUNT).encode())
    bank={int(i):code for i,code in (line.split() for line in bf.read_text().splitlines())}
    assert len(bank)==1145,len(bank)

    gen=out/'1LFgen'
    gen.mkdir(exist_ok=True)
    sys.path.insert(0,str(p.BIDFA))
    from emit_rungram import emit
    from motif_quotient import minimize

    qs=[dict(id=i-OFF,table=rows[i-OFF],p=param)
        for i,param in sorted(abstract.items()) if OFF<=i<OFF+COUNT]
    assert len(qs)==155,len(qs)
    result=json.loads(subprocess.check_output(
        ['node',str(H/'le_replay.cjs'),str(p.DISC)],input=json.dumps(qs).encode()))
    proven={};mods=[]
    for z in result:
        i=z['id']
        assert z['table']==rows[i] and i not in bank
        mod=f'Raw56LE1LFBiDFA{i}'
        ns=f'BB6.Agent1Raw56.LE1LFBiDFA{i}'
        d,g,states=minimize(z['table'],z['dfa'])
        assert len(states)<=z['states'] and sum(map(len,g))+2<=z['edges']
        text='\n'.join([
          'import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
          'namespace '+ns,
          'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',
          emit(i,z['table'],*d,[len(states),sum(map(len,g))+2]),
          'end '+ns,''])
        (gen/(mod+'.lean')).write_text(text)
        proven[i]=ns+f'.M{i}'
        mods.append(mod)

    fullopen=out/'global-le'
    subprocess.run([str(out/'cut'),'1RB---_1RC---_0RD---_1LD1LE_---0LE_------',
                    '1000','32','7',str(fullopen)],check=True)
    p.sha(fullopen.with_suffix('.open').read_bytes(),
          'aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef')
    subprocess.run([sys.executable,str(H/'prepare_motif.py'),
                    str(fullopen.with_suffix('.open')),str(gen),str(MOTIF)],check=True)
    proven[MOTIF-OFF]=f'BB6.Agent1Raw56.LEMotif.M{MOTIF}'
    motifmods=[f'Raw56LEMotif{MOTIF}']

    lateproof={}
    for r in late:
        i=r[0]-OFF
        if r[1]=='last':
            lateproof[i]=f'.last {r[2]} ({r[3]//2},{str(bool(r[3]%2)).lower()})'
        else:
            assert r[1]=='cycle'
            lateproof[i]=f'.cycle {r[2]} {r[3]} {str(bool(r[4])).lower()} ({r[5]})'

    unresolved={i-OFF for i in UNRESOLVED}
    assert set(bank)|set(proven)|set(lateproof)|unresolved==set(range(COUNT))
    assert len(bank)+len(proven)+len(lateproof)+len(unresolved)==COUNT
    print('CLASSIFICATION',len(bank),len(proven),len(lateproof),len(unresolved),flush=True)

    p.PARENT=PARENT
    p.NS='BB6.Agent1Raw56.LE1LFPartial'
    p.MOD='Raw56LE1LFPartial'
    p.BOUND=BOUND
    maker=p.PartialEmitter(rows,json.loads(tf.read_text()),bank,proven,lateproof,
                           unresolved,gen,mods+motifmods)
    maker.write()
    print('MODULES',len(maker.manifest),flush=True)

if __name__=='__main__':
    main()
