import json,pathlib
def trie(xs):
    if not xs:return '.empty'
    if xs=={0}:return '.leaf'
    return '(.branch '+trie({x//2 for x in xs if x%2==0})+' '+trie({x//2 for x in xs if x%2==1})+')'
def partial(t):
    row=[]
    for i,v in enumerate(t):
        a='none' if v<0 else 'some none' if v==0 else f'some (some ⟨{str((v-1)//2%2==1).lower()}, {str((v-1)%2==1).lower()}, {(v-1)//4}⟩)'
        row.append(f'| ({i//2}, {str(i%2==1).lower()}) => {a}')
    return 'fun s => match s with\n  '+'\n  '.join(row)+'\n  | _ => none'
def stack(c,i):
    edges='#['+','.join('['+','.join(f'({str(b==1).lower()},{j})' for b,j in es)+']' for es in c['edges'][i])+']'
    pushes='#['+','.join(f'({a},{b})' for a,b in c['pushes'][i])+']'
    return f'⟨{edges}, {pushes}⟩'
def emit(i,t,c):
    r=len(c['edges'][1]);ss=[set() for _ in range(12)]
    for q,l,j in c['states']:ss[q].add(j+r*l)
    cert=f'⟨{stack(c,0)}, {stack(c,1)}, #['+','.join(trie(s) for s in ss)+']⟩'
    return f'''import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box17.Cert{i}
open BB6Coverage BB6.Agent4Automata
def p : PartialMachine := {partial(t)}
def c : Cert := {cert}
theorem checked : check p c = true := by decide
theorem nonhalt (m : Machine) (h : compatible p m) : NeverHalts m := never p c checked m h
#print axioms nonhalt
end BB6.Agent13.Box17.Cert{i}
'''
def main():
    dst=pathlib.Path('certlean');dst.mkdir(exist_ok=True)
    for i,(t,c) in enumerate(json.load(open('compressed.json'))):
        p=dst/f'Box17Cert{i:03}.lean';p.write_text(emit(i,t,c));print(i,len(c['states']),p.stat().st_size)
if __name__=='__main__':main()
