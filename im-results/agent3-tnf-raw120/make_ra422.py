from pathlib import Path
import phase as p
TABLE='1RB0LF_1RC1RA_0RD---_1LD1RE_0RA1LE_0LA1LA'

def generate():
    machine=p.parse(TABLE);out=['namespace M422',p.tab(machine)]
    def E(b):return p.c_right(4,('111111',False),('1','m'),('0'+'1'*b,False))
    def A0(b,a=2):return p.c_right(0,('00'+'1'*a,False),('1','m'),('0'+'1'*b,False))
    def A(b,n=0,a=1):return p.c_right(0,('10'*(1+n),False),('10','n'),('00'+'1'*a,False),('1','m'),('0'+'1'*b,False))
    def B(b,n=0):return p.c_right(0,('10'*(1+n),False),('10','n'),('0000'+'1'*b,False))
    states={};edges={}
    for b in range(4):
        states.update({f'E{b}':(E(b),'m'),f'Z{b}':(A0(b),'m'),f'A{b}':(A(b),'n m'),f'B{b}':(B(b),'n')})
        edges[f'E{b}']=(E(b),A0(b,5),('m',),f'cfgZ{b} (m+3)',f'Good.Z{b} (m+3)',f'cfgE{b},cfgZ{b}')
        edges[f'Z{b}']=(A0(b),p.c_right(0,('10001',False),('1','m'),('0'+'1'*b,False)),('m',),f'cfgA{b} 0 m',f'Good.A{b} 0 m',f'cfgZ{b},cfgA{b}')
        edges[f'A{b}S']=(A(b,a=2),A(b,n=1),('n','m'),f'cfgA{b} (n+1) m',f'Good.A{b} (n+1) m',f'cfgA{b}')
        bn=(b-1)%4
        edges[f'A{b}0']=(p.c_right(0,('10',False),('10','n'),('0010'+'1'*b,False)),B(bn,n=1),('n',),f'cfgB{bn} (n+1)',f'Good.B{bn} (n+1)',f'cfgA{b},cfgB{bn}')
        edges[f'B{b}']=(B(b),p.c_right(4,('111111',False),('11','n'),('0'+'1'*b,False)),('n',),f'cfgE{b} (2*n)',f'Good.E{b} (2*n)',f'cfgB{b},cfgE{b},pair_rep')
    out.append('theorem pair_rep (n : Nat) : rep [true] (2*n) = rep [true,true] n := by\n  induction n with\n  | zero => rfl\n  | succ n ih =>\n    rw [show 2*(n+1)=2*n+2 by omega]\n    simp only [rep,List.cons_append,List.nil_append,ih]')
    out.extend(f'def cfg{k} ({v} : Nat) : Z0 := {p.cfg(c)}' for k,(c,v) in states.items())
    costs={}
    for k,(st,tg,vs,*_) in edges.items():
        a=p.pump(machine,st,tg);assert a,k
        code,cost=p.generate_phase('Step'+k,machine,st,tg,a,vs);out.append(code);costs[k]=cost
    out.append('inductive Good : Z0 → Prop where\n'+'\n'.join(f'  | {k} ({v} : Nat) : Good (cfg{k} {v})' for k,(c,v) in states.items()))
    lines=['theorem closed (c : Z0) (h : Good c) : ∃ t d, 0 < t ∧ run0 table t c = some d ∧ Good d := by','  cases h with']
    def proof(k,indent):
        st,tg,vs,dest,good,simp=edges[k];a=' '.join(vs)
        return [' '*indent+f'refine ⟨{costs[k]},{dest},by omega,?_,{good}⟩',' '*indent+f'simpa only [{simp},rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Step{k}.advance {a}']
    for k,(c,v) in states.items():
        lines.append(f'  | {k} {v} =>')
        if k.startswith('A'):
            lines+=['    cases m with','    | zero =>']+proof(k+'0',6)+['    | succ m =>']+proof(k+'S',6)
        else:lines+=proof(k,4)
    out.append('\n'.join(lines));out.append('theorem entry : run0 table 88 ⟨0,[],[]⟩ = some (cfgE3 4) := by rfl');out.append('def initial : {z // Good z} := ⟨cfgE3 4,Good.E3 4⟩')
    out.append('theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table (fun n => (phaseOrbit table Good closed initial n).val) 88\n    (fun n => phaseTime table Good closed (phaseOrbit table Good closed initial n))\n    entry (fun n => phaseTime_pos table Good closed _)\n    (phaseOrbit_step table Good closed initial) m hm\n#print axioms never')
    out.append('#print axioms closed\n#print axioms entry\nend M422');return '\n\n'.join(out)
