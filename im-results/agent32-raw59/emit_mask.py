"""Sparse-map bitset emitter for the original source nonhalting interface."""
from collections import defaultdict

def emit_data(root,name,table,D,E,S):
    checker='BB6.Agent32MaskBiDFA'
    ns=f'BB6.Agent32AsymNGram.{name}'
    def arr(v):return '#['+','.join(map(str,v))+']'
    def bo(b):return str(bool(b)).lower()
    def tree(items):
        items=list(items)
        if not items:return '.empty'
        if len(items)==1 and items[0][0]==0:return f'(.leaf {items[0][1]})'
        return '(.branch '+tree((i//2,v) for i,v in items if not i%2)+' '+tree((i//2,v) for i,v in items if i%2)+')'
    p=['def table : PartialMachine := fun s => match s.1.val,s.2 with']
    T=table.replace('_','')
    for j in range(12):
        m=T[3*j:3*j+3]
        v='none' if m=='---' else f'some (some ⟨{bo(m[0]=="1")},{bo(m[1]=="R")},{ord(m[2])-65}⟩)'
        p.append(f'  | {j//2},{bo(j%2)} => {v}')
    p.append('  | _,_ => none')
    for nm,d,e in zip(['leftGraph','rightGraph'],D,E):
        delta=tree((i,str(x)) for i,x in enumerate(d) if x)
        inc=tree((i,'['+','.join(f'({bo(b)},{j})' for b,j in sorted(e[i]))+']') for i in range(len(d)//2) if e[i])
        p.append(f'def {nm} : {checker}.Graph := ⟨{delta},{inc}⟩')
    rel=defaultdict(set)
    for s,l,r in S:rel[s,l].add(r)
    for s in range(12):
        row=tree((l,'⟨'+str(sum(1<<x for x in rel[s,l]))+', ['+','.join(map(str,sorted(rel[s,l])))+']⟩') for l in range(len(D[0])//2) if rel[s,l])
        p.append(f'def row{s} : {checker}.Map {checker}.Cell := '+row)
    p.append(f'def cert : {checker}.Cert := ⟨leftGraph,rightGraph,'+arr(f'row{s}' for s in range(12))+'⟩')
    proofs=[f'theorem row{s:02}_checked : {checker}.rowCheck table cert {s//2} {bo(s%2)} = true := by decide +kernel' for s in range(12)]
    proofs += [f'theorem allRows (q : Fin 6) (a : Bool) : {checker}.rowCheck table cert q a = true := by','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases a',*(f'  · exact row{s:02}_checked' for s in range(12)),f'theorem checked : {checker}.check table cert = true :=',f'  {checker}.check_of_rows (by decide) (by decide) (by decide) allRows',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  {checker}.never table cert checked m hm','#print axioms never']
    path=root/(name+'.lean')
    path.write_text('\n'.join(['import MaskBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',f'namespace {ns}','open BB6Coverage BB6.Agent1NGram',*p,*proofs,f'end {ns}','']))
    return name


def emit(root,name,record):
    from quotient_search import witness
    table,D=record['table'],record['dfa']
    E,n,S=witness(table,D)
    assert E is not None and n==record['states']
    assert sum(len(v) for e in E for v in e.values())==record['edges']
    return emit_data(root,name,table,D,E,S)
