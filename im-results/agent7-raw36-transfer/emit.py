"""Exact-table-keyed FAR transfer; Python generator is untrusted, Lean checks masks."""
import base64, gzip, hashlib, json, sys
from pathlib import Path

D = Path(__file__).resolve().parent
def load():
    raw = gzip.decompress(base64.b64decode((D/'fixture.tsv.gz.b64').read_text()))
    assert hashlib.sha256(raw).hexdigest() == '3bf03c9c90c64837cdd930d4af71e0d30b67ee7c4f86b479f9a67308a2eac089'
    rows = [tuple(line.split()) for line in raw.decode().splitlines()]
    assert len(rows) == len(dict(rows)) == 350
    return rows

def masks(code,table):
    rev=int(code[0]); dfa=[int(x,36) for x in code[1:]]; n=len(dfa)//2; N=6*n+1; H=N-1; halt=1<<H
    P=table.replace('_',''); T=[0]*(2*N); T[H]=T[N+H]=halt; rules=[]
    assert len(P)==36 and len(dfa)==2*n and dfa[0]==0 and all(0<=x<n for x in dfa)
    for l in range(n):
        for q in range(6):
            for a in range(2):
                s=3*(2*q+a); dst=a*N+6*l+q
                if P[s]=='-': T[dst]=halt; continue
                w,r,k=int(P[s]),P[s+1]=='R',ord(P[s+2])-65
                if r!=rev: T[dst]=1<<(6*dfa[2*l+w]+k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if dfa[2*j+b]==l: rules.append((dst,b*N+6*j+k,w*N))
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z: z|=1<<j
            assert not z&1,(code,table)
            if old==z: break
        changed=False
        for dst,src,off in rules:
            v=T[dst]; bits=T[src]
            while bits:
                k=(bits&-bits).bit_length()-1; v|=T[off+k]; bits&=bits-1
            if v!=T[dst]: T[dst]=v; changed=True
        if not changed: return rev,n,dfa,T[:N],T[N:],z

def emit(rows, recovery, out):
    raw=Path(recovery).read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='a870b06b5b9b479aea4f17e841dba9b562f30354dd8b6b53218e4221bc01430d'
    data=json.loads(raw)['unresolvedTables']
    ix={x['table']:i for i,x in enumerate(data)}
    assert len(ix)==366 and set(dict(rows))<=set(ix)
    out=Path(out); out.mkdir(parents=True,exist_ok=True)
    head='import ThreeHoleAudit\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent7Raw36Transfer\nopen BB6Coverage BB6.Agent31ThreeHole\n'
    for j in range(0,len(rows),20):
        lines=[head]
        for table,code in rows[j:j+20]:
            idx=ix[table]; rev,n,dfa,t0,t1,z=masks(code,table)
            lines.append(f'def p{idx} : PartialMachine := fun s =>\n  match s.1.val,s.2 with\n')
            for k in range(12):
                a=table.replace('_','')[3*k:3*k+3]
                if a!='---': lines.append(f'  | {k//2},{str(bool(k%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)\n')
            lines.append('  | _,_ => none\n')
            lines.append(f'def c{idx} : FAR.Data {n} := ⟨0,{dfa},{t0},{t1},{z}⟩\n')
            lines.append(f'theorem never{idx} : ∀ m, compatible p{idx} m → NeverHalts m :=\n  farSound p{idx} {str(bool(rev)).lower()} c{idx} (by decide +kernel)\n#print axioms never{idx}\n')
        lines.append('end BB6.Agent7Raw36Transfer\n')
        (out/f'Raw36Transfer{j//20:02}.lean').write_text(''.join(lines))
    print('uncovered',*[x['table'] for x in data if x['table'] not in dict(rows)],sep='\n')

if __name__=='__main__':
    rows=load()
    if len(sys.argv)==1:
        print(*(' '.join(x) for x in rows),sep='\n')
    else:
        emit(rows,*sys.argv[1:])
