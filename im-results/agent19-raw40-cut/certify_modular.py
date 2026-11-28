#!/usr/bin/env python3
"""Produce independent bounded-size Lean audit modules and compositional nores proofs.
Usage is certify_canonical.py's six arguments, plus optional module-size limit.
Uses exactly the same canonical checker, certificates and generated branch semantics.
"""
import os,sys
from pathlib import Path
root=Path(__file__).resolve().parent
src=(root/'certify_canonical.py').read_text()
depth=os.environ.get('RAW40_MAX_REC_DEPTH')
if depth:
    assert depth.isdigit() and 100000 <= int(depth) <= 10000000
    needle='set_option maxRecDepth 100000'
    assert src.count(needle)==1
    src=src.replace(needle,f'set_option maxRecDepth {depth}')
anchor="imports='import CanonicalPartial\\n' if"
assert anchor in src
src=src.replace(anchor,"imports='import Raw40Nores\\n' if")
anchor="base=imports+head+f'-- {show(parent)}"
assert anchor in src
src=src.replace(anchor,"imports+=''.join('import '+m+'\\n' for m in os.environ.get('RAW40_PROOF_IMPORTS','').split())\n"+anchor)
# A source-proved accelerated first-hole certificate must be checked without
# evaluating its huge primitive prefix. Isolate its exact leaf, and transport
# the accepted check across finite table equality. All enclosing split nodes
# still use the original canonical checker and nores theorem.
if os.environ.get('RAW40_ACCELERATED_LAST_JSON') or os.environ.get('RAW40_ACCELERATED_SPLIT_JSON'):
    anchor="def gen_shard(t,p,cut,name,expr,lines):"
    assert anchor in src
    src=src.replace(anchor,'''accelerated=json.loads(os.environ.get('RAW40_ACCELERATED_LAST_JSON') or '{}')
accelerated_splits=json.loads(os.environ.get('RAW40_ACCELERATED_SPLIT_JSON') or '{}')
split_names={}
def contains_accelerated(t,p):
    if t[0]=='open': return t[1] in accelerated
    if t[0]!='split':return False
    if show(p) in accelerated_splits:return True
    _,n,s,kids=t
    return any(contains_accelerated(k,p[:s]+[move(i)]+p[s+1:]) for i,k in enumerate(kids))

def gen_shard(t,p,cut,name,expr,lines):''')
    anchor="    if size(t)<=threshold:"
    assert anchor in src
    src=src.replace(anchor,"    if (t[0]!='split' or size(t)<=threshold) and (t[0]!='split' or not contains_accelerated(t,p)):")
    anchor="    lines.append(f'abbrev p{name} := {expr}')"
    assert anchor in src
    src=src.replace(anchor,"    if t[0]=='split' and show(p) in accelerated_splits:split_names[name]=accelerated_splits[show(p)]\n"+anchor)
    anchor="        lines.append(f'theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by decide +kernel')"
    assert anchor in src
    src=src.replace(anchor,'''        if t[0]=='open' and t[1] in accelerated:
            ns=accelerated[t[1]]
            assert t[1] in late
            lines.append(f"""theorem peq{name} : p{name} = {ns}.table := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by
  rw [peq{name}]
  exact {ns}.checked {cut}""")
        else:
            lines.append(f'theorem c{name} : canonicalCheck {B} p{name} {cut} t{name} = true := by decide +kernel')''')
    anchor="    proof=f'''theorem ck{name}"
    assert anchor in src
    src=src.replace(anchor,'''    if name in split_names:
        ns=split_names[name]
        xs[-1]=f"""theorem q{name} : zipQueryOK {B} p{name} {n} {slot(s)} = true := by
  have eq : p{name} = {ns}.table := by
    funext s
    rcases s with ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
  rw [eq]
  exact {ns}.query_ok"""
'''+anchor)
anchor="        return\n    assert t[0]=='split';n,s,children=t[1:];names=[]"
assert anchor in src
src=src.replace(anchor,"        if t[0]!='alias':lines.append(f'theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by decide +kernel')\n"+anchor)
anchor="    return xs\nn,s,children=tree[1:]"
assert anchor in src
src=src.replace(anchor,'''    nr=f"""theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by
  unfold t{name}
  apply noresSplit
  intro m h
  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""
    for q in range(6):
        for w in range(2):
            for r in range(2):
                nr+='  · '+(f'exact nr{names[12*w+6*r+q]}' if q<=cut else f'change {q} ≤ {cut} at h; omega')+'\\n'
    xs.append(nr.rstrip())
    return xs
n,s,children=tree[1:]''')
a=src.index('n,s,children=tree[1:]');b=src.index("end+=f'''",a)
body='''moduleLimit=int(sys.argv[7]) if len(sys.argv)>7 else 600
manifest=[];current=None;curSize=0;curLines=[];counter=0

def nextName():
    global counter
    counter+=1
    return f'{mod}Part{counter:03}'

def emit(module,imports,lines):
    deps=sorted(set(imports))
    (output/f'{module}.lean').write_text(''.join(f'import {x}\\n' for x in deps)+head+'\\n'.join(lines)+foot)
    manifest.append([module,deps])

def flush():
    global current,curSize,curLines
    if current:
        emit(current,[mod+'Base'],curLines)
        current=None;curSize=0;curLines=[]

def visit(t,p,cut,name,expr):
    global current,curSize,curLines
    sz=size(t)
    if os.environ.get('RAW40_ACCELERATED_SPLIT_JSON') and t[0]=='split' and show(p) in accelerated_splits:split_names[name]=accelerated_splits[show(p)]
    if sz<=moduleLimit:
        if current and curSize+sz>moduleLimit:flush()
        if current is None:current=nextName()
        gen_shard(t,p,cut,name,expr,curLines);curSize+=sz
        return current
    assert t[0]=='split'
    n,s,children=t[1:];names=[];imports=[]
    for i,k in enumerate(children):
        nm=f'{name}_{i:02}';names.append(nm)
        imports.append(visit(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1),nm,f'refine ({expr}) {slot(s)} (some {mv(i)})'))
    flush();module=nextName()
    emit(module,imports,[f'abbrev p{name} := {expr}']+combine(name,n,s,cut,names))
    return module
n,s,children=tree[1:]
manifest.append([mod+'Base',[]]);imports=[]
for i,k in enumerate(children):
    q=parent[:s]+[move(i)]+parent[s+1:]
    imports.append(visit(k,q,max(cut,i%6+1),str(i),f'refine p {slot(s)} (some {mv(i)})'))
flush()
assert next(it,None) is None
end=''.join(f'import {x}\\n' for x in sorted(set(imports)))+head+'abbrev ptop := p\\n'+'\\n'.join(combine('top',n,s,cut,[str(i) for i in range(24)]))
manifest.append([mod+'All',sorted(set(imports))])
(output/'manifest.json').write_text(json.dumps(manifest))
'''
src=src[:a]+body+src[b:]
src=src.replace('theorem nores : canonicalResiduals p {cut} ttop = [] := by decide +kernel','theorem nores : canonicalResiduals p {cut} ttop = [] := nrtop')
os.environ['RAW40_STANDALONE']='1'
exec(compile(src,str(root/'certify_canonical.py'),'exec'),{'__file__':str(root/'certify_canonical.py'),'__name__':'__main__'})
