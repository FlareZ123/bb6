"""Proof generation for the two RC nested-sweep leaves.

Finite traces propose local equations; Lean checks every equation,
including arbitrary repetition counts and untouched suffixes.
"""
import multi as m
from macro import generate_macro, bits, tab

CASES = {
    1633: ('00', 2, 4, 6, 4,
           [(5,2),(5,4),(3,8),(3,10),(2,13),(2,15)],
           [56,60,60,64,89,93,74], [4,4,8,8,12,12,12],
           [[(2,7,63),(5,0,52),(3,4,44),(3,6,48),(2,9,65),(2,11,69)],
            [(5,0,52),(5,2,56),(3,6,52),(3,8,56),(2,11,77),(2,13,81)]], [50,62]),
    1639: ('', 3, 6, 8, 6,
           [(8,2),(8,4),(6,8),(6,10),(3,16),(3,18),(3,19),(3,21)],
           [94,98,94,98,106,110,151,155,136], [4,4,8,8,12,12,16,16,16],
           [[(3,8,68),(3,11,101),(6,2,70),(6,4,74),(3,10,70),(3,12,74),(3,13,103),(3,15,107)],
            [(3,11,101),(8,0,90),(6,4,78),(6,6,82),(3,12,82),(3,14,86),(3,15,119),(3,17,123)],
            [(8,0,90),(8,2,94),(6,6,86),(6,8,90),(3,14,94),(3,16,98),(3,17,135),(3,19,139)]], [88,104,120]),
    1928: ('00', 1, 2, 4, 3,
           [(2,4),(2,6),(1,9),(1,11)], [24,28,41,45,34], [4,4,8,8,8],
           [[(2,2,20),(2,4,24),(1,7,33),(1,9,37)]], [26]),
    1934: ('', 2, 3, 6, 5,
           [(5,2),(5,4),(2,10),(2,12),(2,13),(2,15)], [46,50,46,50,75,79,68], [4,4,8,8,12,12,12],
           [[(5,0,42),(5,2,46),(2,8,38),(2,10,42),(2,11,63),(2,13,67)]], [56]),
}
SIMP = 'config,ones_add,pair_ones,ones,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil'

def generate_nested(idx,p):
    prefix, mn, base, limit, grow, dest, a, b, small, smallcost = CASES[idx]
    L,R,C=m.lit,m.rep,m.C
    out=[f'namespace M{idx}',tab(p)]
    for j in range(limit+1):
        st=C(0,(),m.clean(L(prefix+'10'*base)+R('10')+L('1'*j)+(R('X') if j==limit else ())))
        if j==limit:
            tg=C(0,(),m.clean(L(prefix+'10'*(base+grow))+R('10')+R('X')))
        else:
            k,z=dest[j]
            tg=C(0,(),m.clean(L(prefix+'10'*k+'1'*z)+R('11')))
        code,aa,bb=generate_macro(p,f'Case{j}',st,tg)
        assert (aa,bb)==(a[j],b[j]),(idx,j,aa,bb)
        out.append(code)
    out.append('''def ones (n : Nat) := rep [true] n
theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m := by
  induction n with
  | zero => simp [ones,rep]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega]
    change [true]++ones (n+m) = ([true]++ones n)++ones m
    rw [ih,List.append_assoc]
theorem pair_ones (n : Nat) : rep [true,true] n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ,Nat.add_comm (2*n) 2,ones_add]; simp only [rep,ih]; rfl''')
    out.append(f'def config (n k : Nat) : Z0 := ⟨0,[],{bits(prefix+"10"*mn)}++rep [true,false] n++ones k⟩')
    for i,cases in enumerate(small):
        for j,(k,z,t) in enumerate(cases):
            out.append(f'theorem small{i}_{j} : run0 table {t} (config {i} {j}) = some (config {k-mn} {z}) := by rfl')
        start=bits(prefix+'10'*(mn+i)+'1'*limit)
        end=bits(prefix+'10'*(mn+i+grow))
        out.append(f'theorem small{i}_many (R : List Bool) : run0 table {smallcost[i]} ⟨0,[],{start}++R⟩ = some ⟨0,[],{end}++R⟩ := by rfl')
    ls=["theorem progress (n k : Nat) : ∃ n' k' t : Nat, 0 < t ∧ run0 table t (config n k) = some (config n' k') := by",'  match n with']
    for i,cases in enumerate(small):
        ls.extend([f'  | {i} =>','    match k with'])
        for j,(kk,z,t) in enumerate(cases):
            ls.append(f'    | {j} => exact ⟨{kk-mn},{z},{t},by decide,small{i}_{j}⟩')
        ls.extend([f'    | k+{limit} =>',f'      refine ⟨{i+grow},k,{smallcost[i]},by decide,?_⟩',f'      simp only [config,show k+{limit}={limit}+k by omega,ones_add]',f'      simpa only [{SIMP}] using small{i}_many (ones k)'])
    delta=base-mn
    ls.extend([f'  | n+{delta} =>','    match k with'])
    for j,(kk,z) in enumerate(dest):
        ls.extend([f'    | {j} =>',f'      refine ⟨{kk-mn},{z}+2*n,{a[j]}+{b[j]}*n,by omega,?_⟩',f'      simp only [config,ones_add]',f'      simpa only [{SIMP}] using Case{j}.equation n'])
    ls.extend([f'    | k+{limit} =>',f'      refine ⟨n+{delta+grow},k,{a[limit]}+{b[limit]}*n,by omega,?_⟩',f'      simp only [config,show k+{limit}={limit}+k by omega,ones_add]',f'      simpa only [{SIMP}] using Case{limit}.equation n (ones k)'])
    out.append('\n'.join(ls))
    out.append('''abbrev Mode := Nat × Nat
def cfg (x : Mode) : Z0 := config x.1 x.2
theorem phaseStep (x : Mode) : ∃ y : Nat × Mode, 0 < y.1 ∧ run0 table y.1 (cfg x) = some (cfg y.2) := by
  obtain ⟨a,b,t,ht,h⟩ := progress x.1 x.2
  exact ⟨(t,a,b),ht,h⟩
noncomputable def next (x : Mode) : Nat × Mode := Classical.choose (phaseStep x)
noncomputable def orbit : Nat → Mode
  | 0 => (0,0)
  | n+1 => (next (orbit n)).2
theorem entry : run0 table 23 ⟨0,[],[]⟩ = some (cfg (orbit 0)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => cfg (orbit n)) 23 (fun n => (next (orbit n)).1) entry
    (fun n => (Classical.choose_spec (phaseStep (orbit n))).1)
    (fun n => (Classical.choose_spec (phaseStep (orbit n))).2) m hm
#print axioms progress
#print axioms entry
#print axioms never''')
    out.append(f'end M{idx}')
    code = '\n\n'.join(out)
    if idx in (1928,1934):
        code = code.replace('| 0 => (0,0)', '| 0 => (0,2)').replace('run0 table 23', 'run0 table 15').replace('(orbit n)) 23', '(orbit n)) 15')
    return code
