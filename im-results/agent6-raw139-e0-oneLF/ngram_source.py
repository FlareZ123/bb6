"""Emit row-separated sparse n-gram certificates from saved witnesses."""
from functools import lru_cache
@lru_cache(None)
def trie(xs):
    if not xs:return '.empty'
    if xs==(0,):return '.leaf'
    return '(.branch '+trie(tuple(x//2 for x in xs if x%2==0))+' '+trie(tuple(x//2 for x in xs if x%2==1))+')'
def emit_ngram(out,j,p,r):
    _,k,n,raw=r
    i,k0,n0,L,R,S=raw.split()
    assert (int(k0),int(n0))==(k,n)
    M=1<<k
    rows=[[] for _ in range(12)]
    for a in map(int,S.rstrip(',').split(',')):rows[a//(M*M)].append(a%(M*M))
    assert sum(map(len,rows))==n
    def edges(s):
        return sorted(2*int(x)+b for x,m in (a.split(':') for a in s.rstrip(',').split(',')) for b in [0,1] if int(m)&(1<<b))
    ns=f'BB6.Agent6OneLFNGram.H{j}'
    base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent1NGram BB6.Agent47SparseNGram\n'
    name=f'OLFNGram{j}'
    o=['import SparseNGram','import OneLFZipHybrid',base,'def p : PartialMachine := fromCodes '+str(p)]
    for nm,xs in [('left',edges(L)),('right',edges(R))]+[(f'row{i}',row) for i,row in enumerate(rows)]:
        o.append(f'def {nm} : Trie := '+trie(tuple(sorted(xs))))
    o.append('def cert : BB6.Agent47SparseNGram.Cert := ⟨'+str(k-1)+',left,right,#['+','.join(f'row{i}' for i in range(12))+']⟩')
    o.append('end '+ns)
    (out/(name+'Data.lean')).write_text('\n'.join(o)+'\n')
    for i in range(12):
        a=str(bool(i%2)).lower()
        s=f'import {name}Data\n'+base+f'theorem checkRow{i} : (BB6.Agent47SparseNGram.row cert {i//2} {a}).all (fun j => BB6.Agent47SparseNGram.stateStepOK p cert {i//2} {a} (j/2^(cert.n+1)) (j%2^(cert.n+1))) = true := by decide +kernel\nend '+ns+'\n'
        (out/f'{name}Row{i:02}.lean').write_text(s)
    o=[f'import {name}Row{i:02}' for i in range(12)]+[base,'theorem checked : BB6.Agent47SparseNGram.check p cert = true := by','  apply BB6.Agent47SparseNGram.check_of_rows','  · decide','  · decide','  · decide','  · intro q a','    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a']+[f'    · exact checkRow{i}' for i in range(12)]+['theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := BB6.Agent47SparseNGram.never p cert checked m hm','#print axioms never','end '+ns]
    (out/(name+'.lean')).write_text('\n'.join(o)+'\n')
    trie.cache_clear()
