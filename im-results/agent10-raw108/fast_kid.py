"""Modular kernel checks for Raw108's three remaining first-move shards.

Keep the original root audit and all witness terms; only the proof evaluation
and module boundaries change. Every concrete-table substitution is checked by
original-source tableOK_sound, so parsing errors cannot prove a wrong table.
"""
import re

DECL = re.compile(r"(?m)^def (kid\d+(?:_part\d+)?) : Audit := ")
NAME = re.compile(r"\bkid\d+(?:_part\d+)?\b")
CHECK = re.compile(r"(?m)^(theorem \w+ : zipCheck \d+ )(.+?)( \(?kid\d+(?:_part\d+)?\)? = true := by) rfl$")
PROVEN = re.compile(r"\.proven\s+([\w.]+)\.table\s+\1\.never")
MOVE = r"⟨(true|false),(true|false),([0-5])⟩"
REFINE = re.compile(r"\(([0-5]),(true|false)\) \(some " + MOVE + r"\)")
CHILD = re.compile(r"\bchild " + MOVE)
IMPORT = re.compile(r"(?m)^import (\w+)[ \t]*\n")
PARENT = "1RB---_1RC{action}_0RD---_1LD1RE_---1LB_------"


def move_code(w,r,q):
    return ('1' if w=='true' else '0')+('R' if r=='true' else 'L')+chr(65+int(q))


def compact_table(expr, action):
    cells = re.findall(r"...", PARENT.format(action=action).replace('_',''))
    m = CHILD.search(expr)
    assert m, expr
    slot = {'0LA':1, '0LB':8}[action]
    assert cells[slot]=='---', (cells,slot)
    cells[slot] = move_code(*m.groups())
    assert expr.count('refine ') == len(REFINE.findall(expr)), expr
    for q,b,w,r,z in REFINE.findall(expr):
        i = 2*int(q)+(b=='true')
        assert cells[i]=='---', (expr,i,cells)
        cells[i] = move_code(w,r,z)
    rows = []
    for i,t in enumerate(cells):
        if t=='---': continue
        rows.append(f"  | ({i//2},{str(bool(i%2)).lower()}) => some (some ⟨{str(t[0]=='1').lower()},{str(t[1]=='R').lower()},{ord(t[2])-65}⟩)")
    return "fun s =>\n  match s with\n"+"\n".join(rows)+"\n  | _ => none\n"


def optimize(block, name, action):
    eq = 'long' if action=='0LB' else 'ordinary'
    prefix = 'BB6.Agent10Raw108FastCheck.'+eq
    m = CHECK.search(block)
    if m:
        table = name+'_compact'
        literal = compact_table(m[2], action)
        proof = m[1]+m[2]+m[3]+f"\n  have he : {m[2]} = {table} := tableOK_sound _ _ (by decide)\n  rw [he, ← {prefix}Check_eq]\n  decide +kernel"
        return f"def {table} : PartialMachine := {literal}\n"+block[:m.start()]+proof+block[m.end():]
    # Join proofs use exactly the same child checks; accelerate only the query.
    old = '  refine ⟨by rfl, allMoves_of _ ?_⟩'
    assert block.count(old)==1, name
    return block.replace(old,f"  refine ⟨?_, allMoves_of _ ?_⟩\n  · rw [← {prefix}Query_eq]\n    decide +kernel\n  ·",1).replace('  ·\n  intro mv','  · intro mv',1).replace('\n  rcases mv','\n    rcases mv',1).replace('\n  have hq','\n    have hq',1).replace('\n  rcases hq','\n    rcases hq',1).replace('\n  all_goals','\n    all_goals',1).replace('\n  · exact','\n    · exact')


def modularize(path, action, providers, max_nodes=100):
    source = path.read_text()
    matches = list(DECL.finditer(source))
    assert matches, path
    header = source[:matches[0].start()]
    suffix_start = source.rfind('\nend ')
    assert suffix_start > matches[-1].start(), path
    footer = source[suffix_start:]
    body = source[:suffix_start]
    blocks = [(m[1],body[m.start():matches[i+1].start() if i+1<len(matches) else len(body)]) for i,m in enumerate(matches)]
    assert len({name for name,_ in blocks})==len(blocks)
    base = [m for m in IMPORT.findall(header) if m.endswith('Base')]
    assert len(base)==1, base
    common_header = IMPORT.sub('',header)
    helper = 'Raw108FastCheckLong' if action=='0LB' else 'Raw108FastCheck'
    groups=[]; group=[]; cost=0
    for name,block in blocks:
        n=max(1,len(re.findall(r'\.(?:cycle|last|far|proven|split)\b',block)))
        if group and cost+n>max_nodes:
            groups.append(group);group=[];cost=0
        group.append((name,block));cost+=n
    if group: groups.append(group)
    owner={}
    for idx,group in enumerate(groups):
        mod=path.stem+f'Unit{idx:03}' if idx+1<len(groups) else path.stem
        dependencies=set(); witnesses=set(); local=set()
        for name,block in group:
            for ref in NAME.findall(block):
                if ref==name or ref in local: continue
                assert ref in owner,(path,ref,name)
                dependencies.add(owner[ref])
            for ns in PROVEN.findall(block):
                choices=providers.get(ns,set())
                assert len(choices)==1,(path,ns,choices)
                witnesses.update(choices)
            local.add(name)
            owner[name]=mod
        imports=sorted(set(base)|{helper}|dependencies|witnesses)
        text=''.join('import '+m+'\n' for m in imports)+common_header
        text+='\n'.join(optimize(b,n,action) for n,b in group)+footer
        path.with_name(mod+'.lean').write_text(text)
    return len(groups)
