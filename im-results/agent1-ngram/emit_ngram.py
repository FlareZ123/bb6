"""Generate independently kernel-checkable local-window certificates.
Input tables: whitespace-separated ID and 36-character transition table.
Input certs: stdout of ngram.cpp. No trust in the search is required.
"""
from pathlib import Path
import argparse

def trie(xs):
    if not xs: return '.empty'
    if xs==[0]: return '.leaf'
    return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2==1])+')'

def emit(i,table,cert,proof=True):
    k,n,L,R,S=cert.split();k=int(k);M=1<<k
    rows=[[] for _ in range(12)]
    for j in map(int,S.rstrip(',').split(',')):rows[j//(M*M)].append(j%(M*M))
    assert sum(map(len,rows))==int(n)
    table=table.replace('_','')
    lines=['  | ('+str(j//2)+', '+str(bool(j%2)).lower()+') => '+('none' if a=='---' else f'some (some ⟨{str(a[0]=="1").lower()}, {str(a[1]=="R").lower()}, {ord(a[2])-65}⟩)') for j,a in enumerate([table[j:j+3] for j in range(0,36,3)])]
    edge=lambda s:hex(sum(int(x)<<(2*j) for j,x in enumerate(s)))
    return '\n'.join(['def p'+str(i)+' : PartialMachine := fun s => match s with']+lines+['  | _ => none','def c'+str(i)+' : Cert := ⟨'+str(k-1)+', '+edge(L)+', '+edge(R)+', #['+','.join(trie(r) for r in rows)+']⟩',f'theorem ok{i} : check p{i} c{i} = true := by decide',*([f'theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := never p{i} c{i} ok{i} m hm',f'#print axioms never{i}'] if proof else [f'#print axioms ok{i}'])])

def main():
    p=argparse.ArgumentParser()
    p.add_argument('tables',type=Path)
    p.add_argument('certificates',type=Path)
    p.add_argument('out',type=Path)
    p.add_argument('--namespace',default='BB6.Agent1NGram.Witnesses')
    p.add_argument('--limit',type=int)
    a=p.parse_args()
    tables=dict(l.split() for l in a.tables.read_text().splitlines())
    cases=[l.split(maxsplit=1) for l in a.certificates.read_text().splitlines()]
    if a.limit is not None: cases=cases[:a.limit]
    out=['import NGramCertificate','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {a.namespace}','open BB6Coverage BB6.Agent1NGram']
    for i,c in cases: out.append(emit(i,tables[i],c))
    out.append(f'end {a.namespace}')
    a.out.write_text('\n'.join(out)+'\n')

if __name__=='__main__': main()
