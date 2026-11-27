"""Emit exact binary-counter proof fixtures for either tape orientation."""
from emitGrowthBank import ops,word
from emitauto import machine,bits
from pathlib import Path

def emit_counter(fixtures,output,ns,side):
    counter='CounterLeft' if side=='L' else 'Counter'
    namespace='BB6Coverage.Agent31Pump.Auto.'+counter+'.'+ns
    imp='Agent46CounterLeftCheck' if side=='L' else 'Agent46CounterCheck'
    s=['import '+imp,'set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+namespace,'open BB6Coverage Agent31Pump Auto '+counter]
    for i,d in enumerate(fixtures):
        assert d['side']==side
        q,*words=d['shape']
        shape='⟨'+','.join([str(q),*(bits(w) for w in words)])+'⟩'
        ms=[f'⟨{ops(m["ops"])},{m["a"]},{m["b"]}⟩' for m in d['macros']]
        s.extend([machine(i,d['table']),
          f'def c{i} : Cert := ⟨{shape},{d["entry"]},{bits(d["seed"])},'+','.join(ms)+'⟩',
          f'theorem checked{i} : check p{i} c{i} = true := by decide',
          f'theorem never{i} (m : Machine) (hm : compatible p{i} m) : NeverHalts m := {counter}.never p{i} c{i} checked{i} m hm',
          f'#print axioms never{i}'])
    Path(output).write_text('\n'.join(s+['end '+namespace,'']))
