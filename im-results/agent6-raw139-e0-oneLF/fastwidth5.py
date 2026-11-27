"""Sparse decision-tree encoding of the same width-five certificate."""
import json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'im-results/agent48-raw139-f1-oneRA'),str(ROOT/'im-results/agent48-raw139-f1-oneLA')]
from blockcert import generate
from package import block_source as original_block_source

def trie(xs, default):
    # The index domain is extended to the next power of two with the
    # default value. Constant leaves need no additional index arithmetic.
    if not xs: return '.leaf '+default
    if all(x==xs[0] for x in xs) and (len(xs)&(len(xs)-1))==0:
        return '.leaf '+xs[0]
    if len(xs)==1:return '.leaf '+xs[0]
    return '.fork ('+trie(xs[::2],default)+') ('+trie(xs[1::2],default)+')'
def nat_trie(xs):return trie([str(x) for x in xs],'0')
def row_trie(xs):return trie([str(list(x)) for x in xs],'[]')

def emit(out, rec):
    i,t=rec['id'],rec['table']
    w,c,m,z,f,ph,*_=rec['block5']
    data=generate(t,w,c,m,z,f,event_limit=150000,phase=ph)
    assert data is not None,(i,rec)
    print('width5',i,'minimized',data['left_states'],data['right_nodes'],flush=True)
    s=original_block_source(i,t,data).replace('BB6.Agent48F1OneRABlocks','BB6.Agent6OneLFFastWidth5').replace('BB6BlockFAR.','BB6BlockFAR5.')
    if f:
        s=s.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
        s=s.replace('BB6BlockFAR5.transfer_never machine m (by simpa only [← same] using hm) forever','BB6Coverage.FAR.reflectNever m (BB6BlockFAR5.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
    # Retain the exact original machine/bridge, but replace the dense
    # Packed accessors and certificate type with independently checked
    # total binary-vector accessors.
    begin=s.index('def cert :')
    end=s.index('theorem row_0') if 'theorem row_0' in s else s.index('theorem valid :')
    d=data['left_states'];n=data['right_nodes']
    vals={
      'pushCodes':nat_trie(data['push']),
      'controlCodes':nat_trie(data['ctrl']),
      'auxiliaryCodes':nat_trie(data['aux']),
      'predecessorCodes':row_trie(data['pred']),
      'edgeCodes':row_trie(data['edges']),
      'zeroCodes':str(sum(1<<x for x in data['zero_states'])),
      'zeroNextCodes':nat_trie(data['zeroNext'])}
    s=s[:begin]+f'def cert : BB6.Agent6FastBlockFAR5.Data {d-1} {n-1} := {{\n  start := 0\n'+''.join(f'  {k} := {v}\n' for k,v in vals.items())+'}\n'+s[end:]
    # Separate data, bounded row groups and final semantic bridge. Every
    # group uses the same exact certificate constant; no row is omitted.
    name=f'OLFFastWidth{i}'
    ns=f'BB6.Agent6OneLFFastWidth5.H{i}'
    head='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
    d=data['left_states']
    start=s.index('theorem valid :') if 'theorem row_0' not in s else s.index('theorem row_0')
    (out/f'{name}Data.lean').write_text('import BlockFARBridge5\nimport FastThreeHoleAudit\nimport FastBlockFAR5\n'+head+s[:start]+f'end {ns}\n')
    # Each range is independently kernel-reduced; join using the generic
    # proven range lemma, not a second enumeration.
    chunks=[]
    for lo in range(0,d,4):
        ln=min(4,d-lo)
        mod=f'{name}Rows{lo:04d}'
        thm=f'rows{lo:04d}'
        (out/f'{mod}.lean').write_text(f'import {name}Data\n'+head+f'namespace {ns}\ntheorem {thm} : BB6.Agent6FastBlockFAR5.rangeCheck {d-1} (cert.rowsAt machine) {lo} {ln} = true := by decide +kernel\nend {ns}\n')
        chunks.append((mod,thm,lo,ln))
    while len(chunks)>1:
        nxt=[]
        for j in range(0,len(chunks),2):
            if j+1==len(chunks):nxt.append(chunks[j]);continue
            a,b=chunks[j:j+2]
            mod=f'{name}Join{a[2]:04d}_{a[3]+b[3]}'
            thm=f'joined{a[2]:04d}_{a[3]+b[3]}'
            assert a[2]+a[3]==b[2]
            (out/f'{mod}.lean').write_text(f'import {a[0]}\nimport {b[0]}\n'+head+f'namespace {ns}\ntheorem {thm} : BB6.Agent6FastBlockFAR5.rangeCheck {d-1} (cert.rowsAt machine) {a[2]} {a[3]+b[3]} = true :=\n  BB6.Agent6FastBlockFAR5.rangeCheck_join _ _ _ _ _ {a[1]} {b[1]}\nend {ns}\n')
            nxt.append((mod,thm,a[2],a[3]+b[3]))
        chunks=nxt
    mod,thm,_,_=chunks[0]
    tail=s[s.index('theorem forever :'):]
    (out/f'{name}.lean').write_text(f'import {mod}\n'+head+f'namespace {ns}\ntheorem rows_valid : cert.rowsCheck machine = true := BB6.Agent6FastBlockFAR5.rangeCheck_full _ _ {thm}\ntheorem valid : cert.Valid machine := ⟨by decide +kernel,by decide +kernel,rows_valid⟩\n'+tail)
if __name__=='__main__':
    out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    for r in json.loads(pathlib.Path(__file__).with_name('holdouts.json').read_text())['unresolved']:
        if 'block5' in r and (len(sys.argv)==2 or r['id']==int(sys.argv[2])):emit(out,r)
