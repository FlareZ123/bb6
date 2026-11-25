from pathlib import Path
import phase as p
import make_ra422

MACHINES={
424:'1RB0LF_1RC---_0RD0LD_1LD1RE_0RA1LE_0LA1LF',
425:'1RB0LF_1RC---_0RD0RA_1LD1RE_0RA1LE_0LA1LF',
427:'1RB0LF_1RC---_0RD---_1LD1RE_0RA1LE_0LA1RA',
435:'1RB0LF_1RC0RF_0RD---_1LD1RE_0RA1LE_0LA1RD',
439:'1RB0LF_1RC1LF_0RD---_1LD1RE_0RA1LE_0LA1RD',
440:'1RB0LF_1RC1RA_0RD---_1LD1RE_0RA1LE_0LA1RD',
441:'1RB0LF_1RC1RB_0RD---_1LD1RE_0RA1LE_0LA1RD',
442:'1RB0LF_1RC1RD_0RD---_1LD1RE_0RA1LE_0LA1RD',
443:'1RB0LF_1RC1RE_0RD---_1LD1RE_0RA1LE_0LA1RD',
}

def spec(idx):
    if idx in (424,425):
        def make(r,b,k=0):
            sfx=('100000' if r==0 else '1000'+'1'*r+'0')+'1'*b
            return p.c_right(5,('100'*(1+k),False),('100','n'),('100'+sfx,False))
        states={f'P{r}{b}':make(r,b) for r in range(4) for b in range(4)}
        edges={f'P{r}{b}':(f'P{(r-1)%4}{(b-1)%4 if r==1 else b}',make((r-1)%4,(b-1)%4 if r==1 else b,int(r!=0)),(int(r!=0),)) for r in range(4) for b in range(4)}
        return states,edges,('n',),81 if idx==424 else 75,'P03',(0,)
    if idx==427:
        def make(b,k=0): return p.c_right(4,('1'*(2+k),False),('1','n'),('111110'+'1'*b,False))
        return {f'P{b}':make(b) for b in range(4)},{f'P{b}':(f'P{(b-1)%4}',make((b-1)%4,3),(3,)) for b in range(4)},('n',),67,'P3',(0,)
    if idx==435:
        def make(r,k=0,m=0):return p.c_right(4,('11'+'00001'*(1+k),False),('00001','n'),(['000000','00001110','0000100110'][r]+'1'*(1+m),False),('1','m'))
        return {f'P{r}':make(r) for r in range(3)},{f'P{r}':(f'P{(r+1)%3}',make((r+1)%3,int(r==2),int(r==2)),(int(r==2),int(r==2))) for r in range(3)},('n','m'),161,'P0',(0,1)
    if idx==442:
        sf=['100111','00100111','10111','0010111','1111','001111','111','00111','11','0011']
        def make(j,k=0):return p.c_right(4,('11'+'00001'*(1+k),False),('00001','n'),(sf[j],False))
        return {f'P{i}':make(i) for i in range(10)},{f'P{i}':(f'P{(i+1)%10}',make((i+1)%10,int(i%2==1)),(int(i%2==1),)) for i in range(10)},('n',),69,'P0',(0,)
    if idx==441:
        def make(r,k=0,m=0):return p.c_right(4,('11'+'00001'*(1+k),False),('00001','n'),(('0000' if r=='A' else '00')+'1'*((7 if r=='A' else 6)+m),False),('1','m'))
        return {r:make(r) for r in ('A','B')},{'A':('B',make('B',1),(1,0)), 'B':('A',make('A',0,2),(0,2))},('n','m'),145,'A',(0,0)
    def make(r,b,k=0):return p.c_right(4,('11'+'00001'*(1+k),False),('00001','n'),(('0000' if r=='A' else '00')+'1'*b,False))
    mx=5 if idx==440 else 3
    states={f'{r}{b}':make(r,b) for r in ('A','B') for b in range(1,mx+1) if r!='A' or b!=1}
    edges={}
    for r in ('A','B'):
        for b in range(1,mx+1):
            if r=='A' and b==1:continue
            if r=='A':rn,bn,k='B',b-1,1
            elif b==1:rn,bn,k=('A',5,0) if idx==440 else ('B',3,1)
            else:rn,bn,k='A',b,0
            edges[f'{r}{b}']=(f'{rn}{bn}',make(rn,bn,k),(k,))
    return states,edges,('n',),{439:145,440:137,443:141}[idx], 'A5' if idx==440 else 'B3', (0,) if idx==440 else (1,)

def generate(idx):
    states,edges,variables,entry,initial,initialargs=spec(idx)
    m=p.parse(MACHINES[idx]);v=' '.join(variables);args=v;defs=[];proofs=[];cases=[]
    for key, start in states.items():
        dest,target,incr=edges[key];ans=p.pump(m,start,target)
        assert ans, (idx,key)
        code,cost=p.generate_phase('Step'+key,m,start,target,ans,variables)
        defs.append(f'def cfg{key} ({v} : Nat) : Z0 := {p.cfg(start)}')
        proofs.append(code)
        arg2=' '.join(f'({x}+{d})' if d else x for x,d in zip(variables,incr))
        cases.append(f'  | {key} {args} =>\n    refine ⟨{cost},cfg{dest} {arg2},by omega,?_,Good.{dest} {arg2}⟩\n    simpa only [cfg{key},cfg{dest},rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Step{key}.advance {args}')
    init=' '.join(map(str,initialargs))
    out=[f'namespace M{idx}',p.tab(m),*defs,*proofs,'inductive Good : Z0 → Prop where',*[f'  | {key} ({v} : Nat) : Good (cfg{key} {args})' for key in states],f'theorem closed (c : Z0) (h : Good c) : ∃ t d, 0 < t ∧ run0 table t c = some d ∧ Good d := by\n  cases h with\n'+'\n'.join(cases),f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (cfg{initial} {init}) := by rfl',f'def initial : {{z // Good z}} := ⟨cfg{initial} {init},Good.{initial} {init}⟩']
    out.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table (fun n => (phaseOrbit table Good closed initial n).val) {entry}\n    (fun n => phaseTime table Good closed (phaseOrbit table Good closed initial n))\n    entry (fun n => phaseTime_pos table Good closed _)\n    (phaseOrbit_step table Good closed initial) m hm')
    out.append(f'#print axioms closed\n#print axioms entry\n#print axioms never\nend M{idx}')
    return '\n\n'.join(out)

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);ap.add_argument('--index',type=int,action='append');a=ap.parse_args()
    hdr='import PhaseClosure\nopen BB6Coverage BB6Coverage.Agent31Pump\nset_option maxRecDepth 40000\nset_option maxHeartbeats 4000000\nnamespace BB6Coverage.Agent3RA'
    a.output.write_text(hdr+'\n\n'+'\n\n'.join(make_ra422.generate() if i==422 else generate(i) for i in (a.index or [422,*MACHINES]))+'\nend BB6Coverage.Agent3RA\n')
