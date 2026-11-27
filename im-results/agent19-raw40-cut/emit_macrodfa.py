"""Reproduce the A-return boundary certificate for Raw40/A0LB/1RE leaf 198."""
from collections import defaultdict
from pathlib import Path
import sys
from macrodfa import discover, Bits
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent32-raw59'))
from emit_rungram import arr, trie, bs

def emit(table,v,fuel,namespace):
    out=['import Raw40MacroDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {namespace}','open BB6Coverage BB6.Agent1NGram BB6.Agent32FastBiDFA','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    p=table.replace('_','')
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':out.append(f'  | {j//2},{bs(j%2)} => some (some ⟨{bs(m[0]=="1")},{bs(m[1]=="R")},{ord(m[2])-65}⟩)')
    out.append('  | _,_ => none')
    for name,d,es in zip(['leftGraph','rightGraph'],v['dfa'],v['incoming']):
        pred=arr('['+','.join(f'({bs(b)},{y})' for b,y in e)+']' for e in es)
        out.append(f'def {name} : Graph := ⟨{arr(map(str,d))},{pred}⟩')
    rs=defaultdict(set)
    for a,l,r in v['roots']:rs[a,l].add(r)
    for a in range(2):out.append(f'def row{a} : Array Trie := '+arr(trie(rs[a,l]) for l in range(len(v['dfa'][0])//2)))
    out.append('def cert : BB6.Agent32FastBiDFA.Cert := ⟨leftGraph,rightGraph,#[row0,row1,#[],#[],#[],#[],#[],#[],#[],#[],#[],#[]]⟩')
    out.extend([f'theorem rowFalse : BB6.Agent19MacroDFA.rowCheck table cert {fuel} false = true := by decide',f'theorem rowTrue : BB6.Agent19MacroDFA.rowCheck table cert {fuel} true = true := by decide',f'theorem checked : BB6.Agent19MacroDFA.check table cert {fuel} = true := by', '  simp only [BB6.Agent19MacroDFA.check,Bool.and_eq_true]', '  exact ⟨⟨⟨⟨by decide,by decide⟩,by decide⟩,rowFalse⟩,rowTrue⟩',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent19MacroDFA.never table cert {fuel} checked m hm','#print axioms never',f'end {namespace}'])
    return '\n'.join(out)+'\n'

if __name__=='__main__':
    t='1RB0LB1RC1RE0RD0RE1LD1LA0RA0LF---0LD'
    v=discover(t,Bits,13,13,stop=0,fuel=8,cap=150000)
    assert (v['states'],v['contexts'],v['edges'])==(1350,10298,999)
    (ROOT/'Raw40A0LB198.lean').write_text(emit(t,v,8,'BB6.Agent19Raw40.A0LB198'))
