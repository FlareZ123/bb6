#!/usr/bin/env python3
"""Regenerate exact block certificates; isolate all block-only names at source.
Untrusted search parameters are checked by the original Lean invariants.
"""
import json,re,shutil,subprocess,sys,tempfile
from pathlib import Path

def emit_cases(repo,out,rows):
    repo,out=repo.resolve(),out.resolve()
    raw=repo/'im-results/agent32-raw59'
    block=repo/'im-results/agent13-block-far'
    sys.path[:0]=[str(block),str(raw)]
    from generate_multi import generate
    from emit_blockmask import emit
    out.mkdir(parents=True,exist_ok=True)
    widths={x['width'] for x in rows}
    if not widths:return []
    with tempfile.TemporaryDirectory() as d:
        t=Path(d)
        for m in ['BlockMacro','BlockMacro2','BlockFAR','BlockFAR2','RangeCheck','RangeCheck2','BlockFARBridge','BlockFARBridge2']:
            shutil.copy2(block/(m+'.lean'),t/(m+'.lean'))
        shutil.copy2(block/'specialize.py',t/'specialize.py')
        for m in ['MaskMap','MaskBlockFAR4']:
            shutil.copy2(raw/(m+'.lean'),t/(m+'.lean'))
        if any(w>=4 for w in widths):
            subprocess.run([sys.executable,str(t/'specialize.py'),*map(str,sorted(w for w in widths if w>=4))],check=True)
        roots=[]
        for x in rows:
            branch,i,code,w=x['branch'],x['id'],x['code'],x['width']
            name=f'Raw42{branch}Block{i}'
            suffix='' if w==3 else str(w)
            data=generate(code,t,width=w,cap=x['cap'],mod=x['mod'],runs=x['runs'],
                          name=name,minimize_left=True,offset=x['offset'],left_mode=x['left_mode'])
            if w in (2,3,4):
                emit(t,name,data,x['offset'])
                (t/(name+'Packed.lean')).unlink()
            ns=f'BB6BlockFAR{suffix}'
            (t/(name+'.lean')).write_text(f'''import {name}Proof
import BlockFARBridge{suffix}
namespace BB6.Agent32Raw42{branch}.Block.Leaf{i}
def table : BB6Coverage.PartialMachine := {ns}.partialTable {ns}.{name}.machine
theorem live (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) :
    BB6Coverage.NeverHalts m :=
  {ns}.transfer_never {ns}.{name}.machine m hm {ns}.{name}.never
#print axioms live
end BB6.Agent32Raw42{branch}.Block.Leaf{i}
''')
            roots.append(name)
        core={p.stem:'Raw42Iso'+p.stem for p in t.glob('*.lean') if not p.stem.startswith('Raw42')}
        for p in t.glob('*.lean'):
            s=p.read_text().replace('BB6BlockFAR','BB6Raw42BlockFAR').replace('BB6.Agent32MaskBiDFA','BB6.Agent32Raw42BlockMask')
            s=re.sub(r'^import (\w+)$',lambda m:'import '+core.get(m[1],m[1]),s,flags=re.M)
            q=out/(core.get(p.stem,p.stem)+'.lean')
            if q.exists():assert q.read_text()==s,q
            q.write_text(s)
        return roots

if __name__=='__main__':
    repo=Path(sys.argv[1]); out=Path(sys.argv[2])
    rows=json.loads((repo/'im-results/agent32-raw42/block42_witnesses.json').read_text())
    if len(sys.argv)>3:rows=[x for x in rows if x['branch']==sys.argv[3]]
    roots=emit_cases(repo,out,rows)
    print('ROOTS',*roots,flush=True)
