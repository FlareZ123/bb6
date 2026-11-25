"""Emit compact Lean stack-relation certificates from untrusted search."""
from rlelearn import check
import sys,json

def bit(b): return 'true' if b else 'false'
def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return f'(.branch {trie([x//2 for x in xs if x%2==0])} {trie([x//2 for x in xs if x%2==1])})'
def emit(i,p,cert):
    ok,n,edges,seen,D,T=cert
    assert ok
    def stack(d):
        E=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(edges[d][k]))+']' for k in range(len(T[d])))
        P=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{E}],#[{P}]⟩'
    rows=[]
    for q in range(6):
        for a in range(2):
            rows.append(trie(sorted(r+len(T[1])*l for qq,aa,l,r in seen if (qq,aa)==(q,a))))
    def move(t):
        return 'none' if t=='---' else f'some (some ⟨{bit(t[0]=="1")},{bit(t[1]=="R")},{ord(t[2])-65}⟩)'
    cases='\n'.join(f'  | ({q},{bit(a)}) => {move(p[2*q+a])}' for q in range(6) for a in range(2))
    return f'''namespace M{i}
def table : PartialMachine := fun s => match s with
{cases}
  | _ => none
def cert : BB6.Agent4Automata.Cert := ⟨{stack(0)}, {stack(1)}, #[{','.join(rows)}]⟩
theorem checked : BB6.Agent4Automata.check table cert = true := by decide
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent4Automata.never table cert checked m hm
#print axioms never
end M{i}
'''
def run(p,paramsL,paramsR,limit=150000):
    return check(p,paramsL,paramsR,limit)
if __name__=='__main__':
    i,p,ns,params=sys.argv[1:5];p=p.replace('_','');p=tuple(p[j:j+3] for j in range(0,len(p),3));params=json.loads(params)
    cert=run(p,params,params)
    print('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage\n'+emit(i,p,cert)+'\nend '+ns)
