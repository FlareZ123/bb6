"""Generate exact finite-radix and movable-marker proof modules from fixtures."""
from emitGrowthBank import ops
from emitauto import machine, bits
from pathlib import Path

def macro(m):
    return f'⟨{ops(m["ops"])},{m["a"]},{m["b"]}⟩'

def fn(name,words):
    return f'def {name} : Fin {len(words)} → List Bool := fun i => match i.val with\n'+''.join(f'  | {i} => {bits(w)}\n' for i,w in enumerate(words[:-1]))+'  | _ => '+bits(words[-1])

def fns(name,macros):
    return f'def {name} : Fin {len(macros)} → Macro := fun i => match i.val with\n'+''.join(f'  | {i} => {macro(m)}\n' for i,m in enumerate(macros[:-1]))+'  | _ => '+macro(macros[-1])

def emit_fixture(d,output,ns,kind):
    namespace='BB6Coverage.Agent31Pump.Auto.'+kind+'.'+ns
    s=['import Agent46'+kind+'Check','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+namespace,'open BB6Coverage Agent31Pump Auto Counter '+kind,machine(0,d['table']).replace('def p0 ', 'def p ',1)]
    if kind=='Radix':
        k=len(d['digits'])-1
        s.extend([fn('digit',d['digits']),f'def terminal (b : Bool) : List Bool := if b then {bits(d["terms"][1])} else {bits(d["terms"][0])}',
            f'def shape : Radix.Shape {k} := ⟨{d["q"]},{bits(d["left"])},digit,terminal,{d["ext"]}⟩',
            fns('nz',d['nz']),fns('ns',d['ns']),
            f'def tz (b : Bool) : Macro := if b then {macro(d["tz"][1])} else {macro(d["tz"][0])}',
            f'def ts (b : Bool) : Macro := if b then {macro(d["ts"][1])} else {macro(d["ts"][0])}',
            f'def cert : Radix.Cert {k} := ⟨shape,{d["entry"]},{d["seed"]},{str(d["top"]).lower()},nz,ns,tz,ts⟩'])
    elif kind=='Marker':
        s.extend([fn('free',d['free']),fn('mark',d['mark']),f'def shape : Marker.Shape := ⟨{d["q"]},{bits(d["left"])},free,mark,{bits(d["terminal"])}⟩'])
        for k,name in [('f','free'),('m','mark')]:
            for x in 'ZS':
                s.append(fns(name+x,[d['macros'][f'{k}{i}{x}'] for i in range(3)]))
        for name in ['moveZ','moveS','overZ','overS']:
            s.append(f'def {name} : Macro := '+macro(d['macros'][name]))
        s.append(f'def cert : Marker.Cert := ⟨shape,{d["entry"]},freeZ,freeS,markZ,markS,moveZ,moveS,overZ,overS⟩')
    elif kind in ('Terminal','PrefixTerminal'):
        k=len(d['digits'])-1
        t=len(d['terms'])-1
        s.extend([fn('digit',d['digits']),fn('terminal',d['terms']),
            f'def next : Fin {t+1} → Fin {t+1} := fun i => match i.val with\n'+''.join(f'  | {i} => {x}\n' for i,x in enumerate(d['nexts'][:-1]))+'  | _ => '+str(d['nexts'][-1]),
            f'def ext : Fin {t+1} → List (Fin {k+1}) := fun i => match i.val with\n'+''.join(f'  | {i} => {x}\n' for i,x in enumerate(d['exts'][:-1]))+'  | _ => '+str(d['exts'][-1]),
            f'def shape : {kind}.Shape {k} {t} := ⟨{d["q"]},{bits(d["left"])},'+(bits(d["pre"])+',' if kind=='PrefixTerminal' else '')+'digit,terminal,next,ext⟩',
            fns('nz',d['nz']),fns('ns',d['ns']),fns('tz',d['tz']),fns('ts',d['ts']),
            f'def cert : {kind}.Cert {k} {t} := ⟨shape,{d["entry"]},{d["seed"]},{d["top"]},nz,ns,tz,ts⟩'])
    elif kind=='SweepMarker':
        s.extend([fn('free',d['free']),f'def shape : SweepMarker.Shape := ⟨{d["q"]},{bits(d["left"])},free,{bits(d["mark"])},{bits(d["sentinel"])},{bits(d["unmarked"])}⟩',
            fns('normalZ',[d['macros'][f'd{i}Z'] for i in range(3)]),
            fns('normalS',[d['macros'][f'd{i}S'] for i in range(3)])])
        for name in ['moveZ','moveS','endZ','endS','overZ','overS']:
            s.append(f'def {name} : Macro := '+macro(d['macros'][name]))
        s.append(f'def cert : SweepMarker.Cert := ⟨shape,{d["entry"]},normalZ,normalS,moveZ,moveS,endZ,endS,overZ,overS⟩')
    else:
        raise ValueError(kind)
    s.extend([f'theorem checked : {kind}.Checked p cert := by constructor <;> decide',
        f'theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := {kind}.never p cert checked m hm',
        '#print axioms never','end '+namespace,''])
    Path(output).write_text('\n'.join(s))
