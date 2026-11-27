"""Emit two-parameter nonlinear sweep fixtures."""
from emitauto import machine,bits
from pathlib import Path

def word2(w):
    if isinstance(w,str):
        return f'(.lit {bits(w)})'
    return f'(.periodic {bits(w[0])} {bits(w[1])} {str(bool(w[2])).lower()} {word2(w[3])})'

def ops2(os):
    a=[]
    for o in os:
        if isinstance(o,int):
            a.append(f'List.replicate {o} .step')
        else:
            a.append(f'[.{"right" if o[0]=="R" else "left"} '+' '.join(bits(x) for x in o[1:5])+' '+word2(o[5])+' '+word2(o[6])+' '+str(bool(o[7])).lower()+' '+str(o[8])+']')
    return '('+' ++\n    '.join(a)+')'

def macro2(m):
    return f'⟨{ops2(m["ops"])},{m["a"]},{m["b"]},{m["c"]}⟩'

def emit_unary(d,output,ns):
    name='BB6Coverage.Agent31Pump.Auto2.UnarySweep.'+ns
    s=['import Agent46UnarySweepCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+name,'open BB6Coverage Agent31Pump Auto2 UnarySweep',machine(0,d['table']).replace('def p0 ', 'def p ',1)]
    for k,f in [('move','move'),('finish','end')]:
        s.append(f'def {k} (b : Bool) : Macro := if b then {macro2(d["macros"][f+"1"])} else {macro2(d["macros"][f+"0"])}')
    s.extend([f'def cert : UnarySweep.Cert := ⟨{bits(d["left"])},{d["entry"]},{d["seed"]},move,finish⟩','theorem checked : Checked p cert := by constructor <;> decide','theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := UnarySweep.never p cert checked m hm','#print axioms never','end '+name,''])
    Path(output).write_text('\n'.join(s))
