"""Extend the original Family emitter using all discovered leaf certificates.
Run on the extracted family archive before replay-family.sh.
The proof generator is untrusted; all emitted certificates are kernel-checked.
"""
from pathlib import Path
import sys
w=Path(sys.argv[1])
p=w/'emit_family.py'
s=p.read_text()
def rep(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
rep('import sys,json','import sys,json\nfrom generate_multi import generate as generate_block')
rep("assert all(p['kind']=='stack' for p in params.values())","assert all(p['kind'] in ('stack','block','hole','cycle','late') for p in params.values())")
rep('indices=sorted(params);ids={i:j for j,i in enumerate(indices)}','indices=sorted(i for i,z in params.items() if z["kind"] in ("stack","block","late"));ids={i:j for j,i in enumerate(indices)}')
rep("""    s='import FamilyCore\\nimport TwoSidedAutomata\\n'+header
    for i in indices[j:j+12]:
        z=params[i];p=list(map(rlecode,rows[i]));c=check(p,z['left'],z['right'],150000,tuple(z['types']))
        assert c[0],(v,i,z,c[1]);s+=emit(i,p,c)
    (out/(mod+'.lean')).write_text(s+end)""","""    imports=['FamilyCore','TwoSidedAutomata','BlockFARBridge','MirrorTransport']
    body=''
    for i in indices[j:j+12]:
        z=params[i];p=list(map(rlecode,rows[i]));kind=z['kind']
        if kind=='stack':
            c=check(p,z['left'],z['right'],150000,tuple(z['types']))
            assert c[0],(v,i,z,c[1]);body+=emit(i,p,c)
        elif kind=='block':
            width,cap,md,runs,flip,offset,mode=z['params']
            assert width in (1,2) and offset==0
            nm=f'A49F{v}B{i}'
            generate_block(''.join(p),out,width=width,cap=cap,mod=md,runs=runs,flip=flip,name=nm,left_mode=mode)
            imports.append(nm+'Proof')
            ns=f'BB6BlockFAR{width}.{nm}'
            tab=f'{ns}.machine'
            run=f'{ns}.never'
            if flip:
                tab=f'(BB6BlockFAR.mirrorTable {ns}.machine)'
                run=f'(BB6BlockFAR.never_of_mirror {tab} (by simpa only [BB6BlockFAR.mirrorTable_involutive] using {ns}.never))'
            codes=','.join(str(x if x>=0 else 25) for x in rows[i])
            body+=f'''namespace M{i}
def table : PartialMachine := fromCodes #[{codes}]
theorem same : partialEq table (BB6BlockFAR.partialTable {tab}) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR.transfer_never {tab} m (by rwa [← partialEq_sound same]) {run}
#print axioms never
end M{i}
'''
        else:
            assert kind=='late' and v==7 and i==1093
            imports.append('FamilyLateSource')
            codes=','.join(str(x if x>=0 else 25) for x in rows[i])
            body+=f'''namespace M{i}
def table : PartialMachine := fromCodes #[{codes}]
theorem same : partialEq table BB6.Agent49FamilyLateSource.p = true := by decide +kernel
theorem decided (m : Machine) (hm : compatible table m) : DecidedBelow {B} m :=
  BB6.Agent49FamilyLateSource.all_completions m (by rwa [← partialEq_sound same])
#print axioms decided
end M{i}
'''
    s=''.join(f'import {a}\\n' for a in dict.fromkeys(imports))+header+body
    (out/(mod+'.lean')).write_text(s+end)""")
rep("f'⟨M{i}.table, fun m hm => Or.inl (M{i}.never m hm)⟩' for i in indices","(f'⟨M{i}.table, M{i}.decided⟩' if params[i]['kind']=='late' else f'⟨M{i}.table, fun m hm => Or.inl (M{i}.never m hm)⟩') for i in indices")
rep("""    if k=='O':return f'(.leaf (.ngram {ngram[z[0]]}))' if z[0] in ngram else f'(.leaf (.external {ids[z[0]]}))'""","""    if k=='O':
        i=z[0]
        if i in ngram:return f'(.leaf (.ngram {ngram[i]}))'
        p=params[i]
        if p['kind']=='hole':
            assert rows[i].count(-1)==1 and 0 not in rows[i] and rows[i][p['slot']]==-1
            return f"(.leaf (.last {slot(p['slot'])} {p['step']}))"
        if p['kind']=='cycle':
            return f"(.leaf (.ray {str(p['right']).lower()} {p['entry']} {p['period']} {p['budget']}))"
        return f'(.leaf (.external {ids[i]}))'""")
p.write_text(s)
