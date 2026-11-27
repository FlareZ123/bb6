"""Replay asymmetric RLE parameters through Agent4's sound stack checker.
Discovery is untrusted. Rows are checked independently to bound elaboration.
"""
import sys,json
from pathlib import Path
from rlelearn import check
from quotient import compress

def bit(b): return 'true' if b else 'false'
def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return f'(.branch {trie([x//2 for x in xs if x%2==0])} {trie([x//2 for x in xs if x%2==1])})'
A='BB6.Agent4Automata'
def emit(i,s,L,R,expected):
    p=tuple(s[j:j+3] for j in range(0,len(s),3));initial=check(p,L,R);assert initial[0] and initial[1]==expected;ok,n,E,S,D,T=compress(p,initial);print(i,expected,"->",n,file=sys.stderr)
    def stack(d):
        edges=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(E[d][k]))+']' for k in range(len(T[d])))
        push=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{edges}],#[{push}]⟩'
    rows=[trie(sorted(r+len(T[1])*l for qq,aa,l,r in S if (qq,aa)==(q,a))) for q in range(6) for a in range(2)]
    def move(t):return 'none' if t=='---' else f'some (some ⟨{bit(t[0]=="1")},{bit(t[1]=="R")},{ord(t[2])-65}⟩)'
    cases='\n'.join(f'  | ({q},{bit(a)}) => {move(p[2*q+a])}' for q in range(6) for a in range(2))
    body=f'''namespace M{i}
def table : PartialMachine := fun s => match s with
{cases}
  | _ => none
def cert : {A}.Cert := ⟨{stack(0)}, {stack(1)}, #[{','.join(rows)}]⟩
'''
    names=[]
    for q in range(6):
        for a in range(2):
            name=f'checked_row_{q}_{a}';names.append(name)
            body+=f'''theorem {name} :
  ({A}.row cert ({q} : Fin 6) {bit(a)}).all
    (fun i => {A}.stateStepOK table cert ({q} : Fin 6) {bit(a)}
      (i / cert.right.edges.size) (i % cert.right.edges.size)) = true := by decide
'''
    body+=f'''theorem left_nonempty : decide (0 < cert.left.edges.size) = true := by decide
theorem right_nonempty : decide (0 < cert.right.edges.size) = true := by decide
theorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide
theorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide
theorem start_state : {A}.stateOK cert 0 false 0 0 = true := by decide
theorem rows_checked :
  (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a =>
    ({A}.row cert q a).all
      (fun i => {A}.stateStepOK table cert q a
        (i / cert.right.edges.size) (i % cert.right.edges.size)))) = true := by
  simp [BB6.Agent1NGram.bits, List.finRange, {', '.join(names)}]
theorem checked : {A}.check table cert = true := by
  unfold {A}.check
  rw [left_nonempty, right_nonempty, left_seed, right_seed, start_state, rows_checked] <;> rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  {A}.never table cert checked m hm
#print axioms never
end M{i}
'''
    return body
if __name__=='__main__':
    inp,ns,out=sys.argv[1:];spec=[json.loads(l) for l in Path(inp).read_text().splitlines() if l.strip()]
    Path(out).write_text('import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen BB6Coverage\n'+'\n'.join(emit(*e) for e in spec)+'\nend '+ns+'\n')
