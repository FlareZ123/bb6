"""Emit bounded generic-predecessor theorem using full finite-period reflection."""
from functools import lru_cache
from math import gcd

CONES = {
  402: [(0,0,1,(2,5,7)),(3,-2,15,(8,10)),(9,-4688,1485,(16,18))],
  1738: [(0,0,1,(2,5)),(3,-2,15,(8,)),(6,-196,135,(12,14,16))]
}
PARENTS = {(402,0):(15,2,8),(402,1):(1485,4688,512),
           (1738,0):(15,2,8),(1738,1):(135,196,64)}
GOOD = {(402,0):(1,1),(402,1):(1,4),
        (1738,0):(1,1),(1738,1):(0,2)}

@lru_cache(None)
def order2(m):
    p,x=1,2%m
    while x!=1:
        p,x=p+1,x*2%m
    return p

def title(r,i):
    if (r,i) not in PARENTS:
        return 'False'
    m,c,z=PARENTS[(r,i)]
    return f'{m}*x+{c}={z}*2^({r}+4860*k)'

def branch(r,i,s,b,d,h,amax):
    D=d*3**h
    E=2**(h+1)*(d-b)
    base=r+s+h+1
    shift=3*D
    ident=f'r{r}_n{i}_h{h}'
    M=f'M_{ident}'
    C=f'C_{ident}'
    cy=f'cycle_{ident}'
    cycles=[]
    for a in range(amax):
        m=D*(2**(a+1)+1)
        c=order2(m)//gcd(order2(m),4860)
        assert pow(2,4860*c,m)==1
        cycles.append(c)
    good=GOOD.get((r,i))
    gooda=good[1] if good and good[0]==h else None
    guard='i.val ≠ 0'+(f' → i.val ≠ {gooda}' if gooda is not None else '')
    cert='(show a≠0 from by omega)'+(' (by omega)' if gooda is not None else '')
    z=[f'private def {M} (a:Nat) : Nat := {D}*(2^(a+1)+1)',
       f'private def {C} (a:Nat) : Nat := 2*a*{D}+{E}',
       f'private def {cy} : Nat → Nat']
    z.extend(f'  | {a} => {c}' for a,c in enumerate(cycles))
    z += ['  | _ => 1','',
      f'private theorem branch_{ident} (k x a v : Nat)',
      '    (ha : 1≤a) (hx : x=2^a*v)',
      f'    (heqRow : {D}*(2^(a+1)+1)*v+2*a*{D}+{E}=2^({base}+4860*k)+{shift}) :',
      f'    {title(r,i)} := by',
      f'  have ha_low : a<{amax} := by',
      f'    by_cases ha0 : a<{amax}',
      '    · exact ha0',
      f'    · have hgap := SheepHighCases.high_r{r}_n{i}_h{h} a (by omega)',
      f'      exact False.elim (SheepGenericHigh.no_large_generic_equation {D} {E} a ({base}+4860*k) v',
      '        (by omega) hgap (by simpa using heqRow))',
      f'  have hM : ∀ i : Fin {amax}, 1<{M} i.val := by decide',
      f'  have hCycle : ∀ i : Fin {amax}, 0<{cy} i.val := by decide',
      f'  have hp : ∀ i : Fin {amax}, 2^(4860*{cy} i.val)%{M} i.val=1 := by',
      f'    have hraw : ∀ i : Fin {amax}, Nat.powMod 2 (4860*{cy} i.val) ({M} i.val)=1 := by decide',
      '    simpa only [Nat.powMod_def] using hraw',
      f'  have hc : ∀ i : Fin {amax}, {guard} → ∀ t : Fin ({cy} i.val),',
      f'    (2^({base}+4860*t.val)+{shift})%{M} i.val≠{C} i.val%{M} i.val := by',
      f'    have hraw : ∀ i : Fin {amax}, {guard} → ∀ t : Fin ({cy} i.val),',
      f'      (Nat.powMod 2 ({base}+4860*t.val) ({M} i.val)+{shift})%{M} i.val ≠ {C} i.val%{M} i.val := by decide',
      '    simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using hraw']
    if gooda is not None:
        factor=2**(s+h+1)
        z += [f'  by_cases hagood : a={gooda}',
          '  · subst a',
          f'    have hpow : 2^({base}+4860*k)={factor}*2^({r}+4860*k) := by',
          f'      rw [show {base}+4860*k=({s+h+1})+({r}+4860*k) by omega, Nat.pow_add]',
          '    rw [hpow] at heqRow',
          '    simp at heqRow hx',
          '    omega','  ·']
        indent='    '
    else:
        indent='  '
    z += [indent+f'exact False.elim (SheepPeriodicGate.no_generic_equation ({M} a) {base} {shift} ({C} a) ({cy} a) k v',
          indent+f'  (hM ⟨a,ha_low⟩) (hCycle ⟨a,ha_low⟩) (hp ⟨a,ha_low⟩)',
          indent+f'  (hc ⟨a,ha_low⟩ {cert})',
          indent+f'  (by simpa [{M},{C},Nat.add_assoc] using heqRow))','']
    return z
