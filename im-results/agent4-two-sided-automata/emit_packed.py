"""Emit separately kernel-checkable sparse row chunks and a bitmap invariant.

Example: python emit_packed.py 203 1RB0LE_1RC1RA_0RD---_1LD1RE_1LF0RA_1RC0LF BB6.Agent4Raw58LEChunk '[7,6,1]' /tmp/raw58-packed
"""
import argparse
import json
from pathlib import Path
from emit_automata import bit
from quotient import compress
from rlelearn import check

A = 'BB6.Agent4PackedAutomata'
OPTS = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'


def emit(i, p, cert, namespace, output, prefix=None, chunk_size=64):
    if chunk_size <= 0:
        raise ValueError('chunk size must be positive')
    ok,n,edges,seen,D,T=cert
    assert ok
    output.mkdir(parents=True, exist_ok=True)
    prefix=prefix or f'PackedM{i}'
    ns=f'{namespace}.M{i}'
    start=f'namespace {ns}\nopen BB6Coverage\n'
    end=f'\nend {ns}\n'
    def write(name, imports, body):
        (output/(name+'.lean')).write_text(''.join(f'import {m}\n' for m in imports)+OPTS+start+body+end)
    def stack(d):
        E=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(edges[d][k]))+']' for k in range(len(T[d])))
        P=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{E}],#[{P}]⟩'
    def move(t):
        return 'none' if t=='---' else f'some (some ⟨{bit(t[0]=="1")},{bit(t[1]=="R")},{ord(t[2])-65}⟩)'
    cases='\n'.join(f'  | ({q},{bit(a)}) => {move(p[2*q+a])}' for q in range(6) for a in range(2))
    source=f'def table : PartialMachine := fun s => match s with\n{cases}\n  | _ => none\n'
    rows=[]; row_modules=[]; row_names=[]
    for q in range(6):
        for a in range(2):
            xs=sorted(r+len(T[1])*l for qq,aa,l,r in seen if (qq,aa)==(q,a))
            mask=sum(1<<x for x in xs)
            names=[]
            for k in range(0,len(xs),chunk_size):
                name=f'chunk_{q}_{a}_{k//chunk_size}'
                names.append(name)
                source+=f'def {name} : List Nat := [{",".join(map(str,xs[k:k+chunk_size]))}]\n'
            chunks='['+','.join(names)+']'
            rows.append(f'⟨{chunks},{hex(mask)}⟩')
            args=f'table cert ({q} : Fin 6) {bit(a)}'
            steps=[f'theorem check_{name} : {A}.indicesCheck {args} {name} = true := by decide' for name in names]
            row_name=f'checked_row_{q}_{a}'
            steps.append(f'theorem {row_name} : {A}.rowCheck {args} = true := by\n  unfold {A}.rowCheck\n  have hvalid : ({A}.row cert ({q} : Fin 6) {bit(a)}).valid = true := by decide\n  rw [hvalid]\n  change (true && {chunks}.all ({A}.indicesCheck {args})) = true\n  simp only [List.all_cons, List.all_nil, Bool.and_self'+''.join(',check_'+name for name in names)+']')
            mod=f'{prefix}Row{q}{a}'
            row_modules.append(mod); row_names.append(row_name)
            write(mod,[prefix+'Data'],'\n'.join(steps))
    source+=f'def cert : {A}.Cert := ⟨{stack(0)}, {stack(1)}, #[{",".join(rows)}]⟩\n'
    write(prefix+'Data',['PackedStackAutomata'],source)
    final=f"""theorem left_nonempty : decide (0 < cert.left.edges.size) = true := by decide
theorem right_nonempty : decide (0 < cert.right.edges.size) = true := by decide
theorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide
theorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide
theorem start_state : {A}.stateOK cert 0 false 0 0 = true := by decide
theorem rows_checked :
  (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a =>
    {A}.rowCheck table cert q a)) = true := by
  simp [BB6.Agent1NGram.bits, List.finRange, {', '.join(row_names)}]
theorem checked : {A}.check table cert = true := by
  unfold {A}.check
  rw [left_nonempty, right_nonempty, left_seed, right_seed, start_state, rows_checked] <;> rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  {A}.never table cert checked m hm
#print axioms checked
#print axioms never"""
    write(prefix+'Proof',row_modules,final)
    return output/(prefix+'Proof.lean')


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('index',type=int)
    ap.add_argument('table')
    ap.add_argument('namespace')
    ap.add_argument('params')
    ap.add_argument('output',type=Path)
    args=ap.parse_args()
    raw=args.table.replace('_','')
    p=tuple(raw[j:j+3] for j in range(0,len(raw),3))
    params=json.loads(args.params)
    print(emit(args.index,p,compress(p,check(p,params,params)),args.namespace,args.output))
