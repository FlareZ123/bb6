from gen_auto import quotient,validate,parse,bit,mv
from collections import defaultdict
from pathlib import Path
import json,sys,group,block

def radix(xs):
    if not xs:return '.empty'
    if list(xs)==[0]:return f'(.leaf {xs[0]})'
    return f'(.branch {radix({i//2:v for i,v in xs.items() if i%2==0})} {radix({i//2:v for i,v in xs.items() if i%2==1})})'

def emit(ids,ps,result,module=None):
    edges,seen,D,T=quotient(*result)
    for p in ps:validate(p,edges,seen,D,T)
    n=[len(x) for x in T]
    module=module or f'Agent2RCSparseGroup{ids[0]}'
    ns='BB6.'+module
    txt=f'import SparseTwoSided\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6.Agent2SparseTwoSided\n'
    for i,p in zip(ids,ps):
        txt+=f'def table{i} : PartialMachine := fun s => match s.1.val,s.2 with\n'+''.join(f'  | {j//2},{bit(j%2)} => some (some {mv(m)})\n' for j,m in enumerate(p) if m!='---')+'  | _,_ => none\n'
    def stack(d):
        E=radix({k:'['+','.join(f'({bit(b)},{j})' for b,j in sorted(edges[d][k]))+']' for k in range(n[d]) if edges[d][k]})
        P=radix({k:f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(n[d]) if D[d].get((k,0),0) or D[d].get((k,1),0)})
        return f'⟨{n[d]}, {E}, {P}⟩'
    rows=[defaultdict(set) for _ in range(12)]
    for q,a,l,r in seen:rows[2*q+a][l].add(r)
    txt+=f'def cert : Cert := ⟨{stack(0)}, {stack(1)}, #[{",".join(radix({l:radix({r:"true" for r in rs}) for l,rs in x.items()}) for x in rows)}]⟩\n'
    for j in range(12):
        q,a=divmod(j,2);reps={}
        for i,p in zip(ids,ps):
            name=f'row_{j}_{i}'
            expr=f'rowCheck table{i} cert ({q}:Fin 6) {bit(a)} = true'
            if p[j] in reps:
                rep=reps[p[j]]
                proof=f"(row_congr (p:=table{i}) (p':=table{rep}) (c:=cert) (q:={q}) (a:={bit(a)}) (by rfl)).trans row_{j}_{rep}"
            else:
                reps[p[j]]=i;proof='by decide'
            txt+=f'theorem {name} : {expr} := {proof}\n'
    txt+='theorem left_nonempty : decide (0 < cert.left.size) = true := by decide\ntheorem right_nonempty : decide (0 < cert.right.size) = true := by decide\ntheorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide\ntheorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide\ntheorem start_state : stateOK cert 0 false 0 0 = true := by decide\n'
    for i in ids:
        names=','.join(f'row_{j}_{i}' for j in range(12))
        txt+=f'theorem rows_checked{i} : (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a => rowCheck table{i} cert q a)) = true := by\n  simp [BB6.Agent1NGram.bits,List.finRange,{names}]\ntheorem checked{i} : check table{i} cert = true := by\n  unfold check\n  rw [left_nonempty,right_nonempty,left_seed,right_seed,start_state,rows_checked{i}] <;> rfl\ntheorem never{i} (m : Machine) (hm : compatible table{i} m) : NeverHalts m := BB6.Agent2SparseTwoSided.never table{i} cert checked{i} m hm\n#print axioms never{i}\n'
    txt+=f'end {ns}\n';Path(f'core/{module}.lean').write_text(txt)
    return module,len(seen),n,len(txt)

if __name__=='__main__':
    rows=open('rc.open').read().splitlines()
    args=[x for x in sys.argv[1:] if x!="--replace"]
    for ids,a,mod in json.load(open('maskgroups.json')):
        if args and str(ids[0]) not in args:continue
        ps=[parse(rows[i]) for i in ids]
        res=block.run(ps[0],a,150000) if ids==[70] else group.run(ps,a,150000)
        assert res
        print(ids,emit(ids,ps,res,mod if "--replace" in sys.argv else None),flush=True)
