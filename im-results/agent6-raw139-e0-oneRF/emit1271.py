"""From repository root: python im-results/agent6-raw139-e0-oneRF/emit1271.py OUT.
Produces source-connected row modules for the locally kernel-checked 1271/5 certificate."""
from functools import lru_cache
from pathlib import Path
import subprocess,sys
ROOT=Path(__file__).resolve().parents[2]
outdir=Path(sys.argv[1]).resolve();outdir.mkdir(parents=True,exist_ok=True)
exe=outdir/'ngram_sparse'
subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'im-results/agent47-raw111-cut/ngram_sparse.cpp'),'-o',str(exe)],check=True)
p=[7,12,11,23,14,5,2,16,23,11,1,24]
table=''.join('---' if v==24 else str((v>>1)&1)+('R' if v&1 else 'L')+chr(65+(v>>2)) for v in p)
raw=subprocess.check_output([str(exe),'21'],input='1271 '+table+'\n',text=True)
i,k,n,L,R,S=raw.split();k=int(k);M=1<<k
assert (i,k,int(n))==('1271',21,13603)
rows=[[] for _ in range(12)]
for j in map(int,S.rstrip(',').split(',')):rows[j//(M*M)].append(j%(M*M))
assert sum(map(len,rows))==int(n)
def edges(s):
 return sorted(2*int(x)+b for x,m in (a.split(':') for a in s.rstrip(',').split(',')) for b in [0,1] if int(m)&(1<<b))
@lru_cache(None)
def trie(xs):
 if not xs:return '.empty'
 if xs==(0,):return '.leaf'
 return '(.branch '+trie(tuple(x//2 for x in xs if x%2==0))+' '+trie(tuple(x//2 for x in xs if x%2==1))+')'
ns='BB6.Agent6E0OneRF1271_5'
base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent1NGram BB6.Agent47SparseNGram\n'
out=['import SparseNGram','import Hybrid',base,'def p : PartialMachine := fromCodes '+str(p)]
for name,xs in [('left',edges(L)),('right',edges(R))]+[(f'row{i}',row) for i,row in enumerate(rows)]:out.append(f'def {name} : Trie := '+trie(tuple(sorted(xs))))
out.append('def cert : BB6.Agent47SparseNGram.Cert := ⟨20,left,right,#['+','.join(f'row{i}' for i in range(12))+']⟩')
out.append('end '+ns)
(outdir/'OneRF1271_5Data.lean').write_text('\n'.join(out)+'\n')
for i in range(12):
 a=str(bool(i%2)).lower();s=f'import OneRF1271_5Data\n'+base+f'theorem checkRow{i} : (BB6.Agent47SparseNGram.row cert {i//2} {a}).all (fun j => BB6.Agent47SparseNGram.stateStepOK p cert {i//2} {a} (j/2^(cert.n+1)) (j%2^(cert.n+1))) = true := by decide +kernel\nend '+ns+'\n'
 (outdir/f'OneRF1271_5Row{i:02}.lean').write_text(s)
out=[f'import OneRF1271_5Row{i:02}' for i in range(12)]+[base,'theorem checked : BB6.Agent47SparseNGram.check p cert = true := by','  apply BB6.Agent47SparseNGram.check_of_rows','  · decide','  · decide','  · decide','  · intro q a','    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a']+[f'    · exact checkRow{i}' for i in range(12)]+['theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := BB6.Agent47SparseNGram.never p cert checked m hm','#print axioms never','end '+ns]
(outdir/'OneRF1271_5.lean').write_text('\n'.join(out)+'\n')
