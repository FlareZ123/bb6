"""Emit balanced-tree BiDFA certificates with independent subtree proofs."""
from bidfa_emit import witness, boolstr

def emit(i,table,dl,dr):
    es,states=witness(table,dl,dr)
    assert len(dl)//2<=64 and len(dr)//2<=64
    out=[f'namespace M{i}', 'def table : PartialMachine := fun s =>', '  match s.1.val,s.2 with']
    p=table.replace('_','')
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':out.append(f'  | {j//2},{boolstr(j%2)} => some (some ⟨{boolstr(m[0]=="1")},{boolstr(m[1]=="R")},{ord(m[2])-65}⟩)')
    out.append('  | _,_ => none')
    def tree(lo,hi):
        if lo==hi:return '.empty'
        mid=(lo+hi)//2
        l,r=tree(lo,mid),tree(mid+1,hi)
        q,a,x,y=states[mid]
        return f'(.node {l} ⟨{q},{boolstr(a)},{x},{y}⟩ {r})'
    def make(lo,hi):
        if lo==hi:return '.empty'
        name=f't{lo}_{hi}'
        if hi-lo<=8: out.append(f'def {name} : Tree := {tree(lo,hi)}')
        else:
            mid=(lo+hi)//2;l,r=make(lo,mid),make(mid+1,hi)
            q,a,x,y=states[mid];out.append(f'def {name} : Tree := .node {l} ⟨{q},{boolstr(a)},{x},{y}⟩ {r}')
        return name
    root=make(0,len(states))
    out.append('def cert : TreeCert := ⟨'+str(dl)+','+str(dr)+',')
    for e in es:out.append('  ['+','.join(f'⟨{a},{boolstr(b)},{c}⟩' for a,b,c in e)+'],')
    out.append(f'  {root}⟩')
    def blocks(lo,hi):
        if lo==hi:return '(by rfl)'
        name=f't{lo}_{hi}';thm=f'check{lo}_{hi}'
        if hi-lo<=8:
            out.append(f'theorem {thm} : {name}.all (stepOK table cert) = true := by decide')
        else:
            mid=(lo+hi)//2;l,r=blocks(lo,mid),blocks(mid+1,hi)
            q,a,x,y=states[mid];out.append(f'theorem node{mid} : stepOK table cert ⟨{q},{boolstr(a)},{x},{y}⟩ = true := by decide')
            out.append(f'theorem {thm} : {name}.all (stepOK table cert) = true := Tree.all_node node{mid} {l} {r}')
        return thm
    checked=blocks(0,len(states))
    out.extend([f'theorem checked : cert.states.all (stepOK table cert) = true := {checked}',
      'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent16BiDFA.TreeCheck.never table cert (by decide) (by decide) (by decide) checked m hm',
      '#print axioms never',f'end M{i}'])
    return '\n'.join(out),len(states),sum(map(len,es))

# Stable open.txt indices, full transition tables, deterministic DFA transitions,
# number of reached abstract states and number of stack edges.
EXAMPLES=[
    (1648, '1RB0RA_1RC0RF_0RD0RC_1LD1RE_1LA0LE_0RC---', '014230bc576d918i57a091608ife30g0jh4230a0', '0132d7405h0600f8a9a9b0gc00e0gcb00600', 622, 57),
    (2202, '1RB0RA_1RC1RF_0RD0RC_1LD1RE_1LA0LE_1LC---', '01423jcd576ea1983j57b0a16098gf3lh0ki4200b000', '0132f84k57060000i9babacejd0000ghjd00ce0600', 686, 64),
    (2874, '1RB---_1RC1LE_0RD0RF_1LD1RE_1LB0LE_1RA0RF', '01423000a5i607800906b0jcld0ef00g0h0ea5k0jcamnham', '013298405g7632010da00b0c98ehf00b0c0i0h', 436, 61),
    (5666, '1RB---_1RC1LE_0RD1RA_1LD1RE_1RF0LE_1LB0RF', '01423000569a4708005600', '013200485600079a00000b9a', 71, 28),
]
if __name__=='__main__':
    import sys
    selected={int(x) for x in sys.argv[1:]} or {i for i,*_ in EXAMPLES}
    assert selected <= {i for i,*_ in EXAMPLES}
    print('import TreeBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent16BiDFA.Raw118Tree\nopen BB6Coverage Agent16BiDFA Agent16BiDFA.TreeCheck')
    for i,p,l,r,n,e in EXAMPLES:
        if i in selected:
            code,nn,ee=emit(i,p,[int(x,36) for x in l],[int(x,36) for x in r]);assert (nn,ee)==(n,e);print(code)
    print('end BB6Coverage.Agent16BiDFA.Raw118Tree')
