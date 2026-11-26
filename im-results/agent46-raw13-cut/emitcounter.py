"""Convert untrusted JSON counter certificates into Lean checked definitions."""
import json,sys

def bits(s): return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def word(w):
    if isinstance(w,str): return f'(.lit {bits(w)})'
    return f'(.periodic {bits(w[0])} {bits(w[1])} {word(w[2])})'
def op(o):
    d,lp,rp,I,O,L,R,k=o
    return f'.{"left" if d=="L" else "right"} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {word(L)} {word(R)} {k}'
def macro(m):
    ops=[v for o in m['ops'] for v in (['.step']*o if isinstance(o,int) else [op(o)])]
    return '⟨['+',\n    '.join(ops)+f'],{m["a"]},{m["b"]}⟩'
def emit(fixtures,branch):
    ns='BB6Coverage.Agent31Pump.Auto.Counter.Raw13Branch'+branch
    out=['import Agent46CounterCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage Agent31Pump Auto Counter']
    for i,f in enumerate(fixtures):
        t=f['table'];out.append(f'def p{i} : PartialMachine := fun s => match s.1.val,s.2 with')
        for j in range(12):
            x=t[3*j:3*j+3]; v='none' if x=='---' else f'some (some ⟨{str(x[0]=="1").lower()},{str(x[1]=="R").lower()},{ord(x[2])-65}⟩)'
            out.append(f'  | {j//2},{str(bool(j%2)).lower()} => {v}')
        out.append('  | _,_ => none')
        q,*shape=f['shape']; sh='⟨'+','.join([str(q)]+[bits(s) for s in shape])+'⟩'
        out.append(f'def c{i} : Cert := ⟨{sh},{f["entry"]},{bits(f["seed"])},'+',\n  '.join(map(macro,f['macros']))+'⟩')
        out.append(f'theorem checked{i} : check p{i} c{i} = true := by decide')
        out.append(f'theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := never p{i} c{i} checked{i} m hm')
        out.append(f'#print axioms never{i}')
    out.append(f'end {ns}')
    return '\n'.join(out)+'\n'
if __name__=='__main__':
    print(emit(json.load(open(sys.argv[1])),sys.argv[2]),end='')
