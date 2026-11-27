"""Compact source emitter for exact symbolic-growth fixtures."""
from emitauto import machine,bits
from pathlib import Path

def word(w):
    if isinstance(w,str):
        return '(.lit '+bits(w)+')'
    return '(.periodic '+bits(w[0])+' '+bits(w[1])+' '+word(w[2])+')'

def cfg(z):
    return f'⟨{z[0]},{word(z[1])},{word(z[2])}⟩'

def ops(os):
    parts=[]
    for o in os:
        if isinstance(o,int):
            parts.append(f'List.replicate {o} .step')
        else:
            parts.append(f'[.{"right" if o[0]=="R" else "left"} '+' '.join(bits(x) for x in o[1:5])+' '+word(o[5])+' '+word(o[6])+' '+str(o[7])+']')
    return '('+' ++\n    '.join(parts)+')'

def emit_growth(fixtures,output,ns):
    namespace='BB6Coverage.Agent31Pump.Auto.'+ns
    s=['import Agent46AutoPump','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+namespace,'open BB6Coverage Agent31Pump Auto']
    for i,d in enumerate(fixtures):
        s.extend([f'\n/-- {d["table"]} -/',machine(i,d['table']),
                  f'def c{i} : Cert := ⟨{d["entry"]},{cfg(d["family"])},{d["inc"]},{ops(d["ops"])},{d["a"]},{d["b"]}⟩',
                  f'theorem checked{i} : check p{i} c{i} = true := by decide',
                  f'theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := check_never p{i} c{i} checked{i} m hm',
                  f'#print axioms never{i}'])
    Path(output).write_text('\n'.join(s+['end '+namespace,'']))
