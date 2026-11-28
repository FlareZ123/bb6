from pathlib import Path

def patch(source,target):
 s=Path(source).read_text()
 s=s.replace("NS='BB6.Agent4Raw56.'+TAG; MOD='Raw56'+TAG","NS='BB6.Agent4Raw56LB.'+TAG; MOD='Raw56LB'+TAG")
 s=s.replace('PARENT=f"1RB---_1RC---_0RD---_1LD1LE_{E0}1RE_------"','PARENT="1RB---_1RC---_0RD---_1LD1LE_---1LB_------"')
 s=s.replace("emit(MOD+'Base',['Raw40Nores']+AUTOS,base)","emit(MOD+'Base',['Raw40Nores'],base)\nused=set()")
 s=s.replace("return f'.proven {PROVEN[s]}.table {PROVEN[s]}.never' if s in PROVEN else far(bank[i],p)","if s in PROVEN:\n            mod,ns=PROVEN[s];used.add(mod)\n            return f'.proven {ns}.table {ns}.never'\n        return far(bank[i],p)")
 s=s.replace("if current_name:emit(current_name,[MOD+'Base'],current)","if current_name:emit(current_name,[MOD+'Base']+sorted(used),current)\n    used.clear()")
 s=s.replace("def gen(t,p,cut):\n    if cut==6 or t[0]!='split':",'''respaths={}
def paths(t,cut):
    if t[0]=='unresolved':return [()]
    if t[0]!='split':return []
    n,s,kids=t[1:];return [((s,i),)+a for q in range(6) if q<=cut for w in range(2) for r in range(2) for i in [12*w+6*r+q] for a in paths(kids[i],max(cut,q+1))]
def rlist(name,ps):
    rr=[]
    for pa in ps:
        m='p'+name
        for s,i in pa:m=f'refine ({m}) {slot(s)} (some {mv(i)})'
        rr.append(f'([{",".join(mv(i) for s,i in pa)}],{m})')
    return '['+','.join(rr)+']'
def gen(t,p,cut):
    if t[0]=='unresolved':return '.unresolved'
    if (cut==6 and not paths(t,cut)) or t[0]!='split':''')
 s=s.replace("    return lines+[ck.rstrip(),f'''theorem c{name}",'''    if respaths.get(name):
        ids=[12*w+6*r+q for q in range(6) if q<=cut for w in range(2) for r in range(2)]
        terms=[f'List.map (fun e => ({mv(i)} :: e.1,e.2)) (canonicalResiduals p{names[i]} {max(cut,i%6+1)} t{names[i]})' for i in ids]
        nr=f'theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = {rlist(name,respaths[name])} := by\\n  change ('+' ++ '.join(terms+['[]'])+') = _\\n  simp only ['+','.join('nr'+names[i] for i in ids)+',List.map_nil,List.map_cons,List.nil_append,List.append_nil,List.cons_append]'
    return lines+[ck.rstrip(),f\'''theorem c{name}''')
 s=s.replace("    lines.append(f'abbrev p{name} := {expr}')\n    if size(t)<=96:","    lines.append(f'abbrev p{name} := {expr}')\n    ps=paths(t,cut);respaths[name]=ps\n    if t[0]=='unresolved':\n        lines.extend([f'def t{name} : PartialAudit := .unresolved',f'theorem c{name} : canonicalCheck {BOUND} p{name} {cut} t{name} = true := rfl',f'theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = {rlist(name,ps)} := rfl']);return\n    if size(t)<=96 and not ps:")
 s=s.replace("    sz=size(t)\n", "    sz=size(t)\n    respaths[name]=paths(t,cut)\n")
 s=s.replace("end=['abbrev ptop := p']+combine('top',n,s,cut,names)+[f'''theorem all_quotient :", "respaths['top']=paths(tree,cut)\nend=['abbrev ptop := p']+combine('top',n,s,cut,names)+[f'''theorem all_quotient :")
 start=s.index("[f'''theorem all_quotient :")
 stop=s.index("\nemit(MOD+'All'",start)
 s=s[:start]+'''[f\'''def residuals : List (List Move × PartialMachine) := {rlist('top',respaths['top'])}
theorem exact_residuals : canonicalResiduals p {cut} ttop = residuals := nrtop
theorem partial_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m ∨ ∃ e, e ∈ residuals ∧ TNFQuotientCompatible e.snd m := by
  intro m hm
  rw [← exact_residuals]
  exact canonicalSound {BOUND} p {cut} ttop (by decide) supported root nohalt ctop m hm
#print axioms partial_quotient\''']'''+s[stop:]
 assert 'def residuals' in s and 'respaths' in s
 Path(target).write_text(s)
