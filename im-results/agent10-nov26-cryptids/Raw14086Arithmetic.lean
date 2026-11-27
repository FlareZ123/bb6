import Std
namespace Raw14086Arithmetic
inductive Kind where | a0 | a2 | b0 deriving DecidableEq, Repr
abbrev Cfg := Kind × Nat
def next (s : Nat) := (s+1)%6
def carry (s : Nat) := if s=5 then 1 else 0
def termB (p s : Nat) : Cfg :=
  match s with
  | 0 => (.b0,p+2) | 1 => (.a2,p+2) | 2 => (.a0,p+3)
  | 3 => (.b0,p+6) | 4 => (.b0,p+6) | _ => (.a2,p+4)
def termA (p s : Nat) : Cfg :=
  match s with
  | 0 => (.a2,p+2) | 1 => (.a0,p+5) | 2 => (.a0,p+5)
  | 3 => (.b0,p+6) | 4 => (.a0,p+6) | _ => (.b0,p+9)
def dReturn (k : Nat) : Cfg :=
  let n := k/6; let s := k%6; let h := k+8
  if h%2=1 then termB (2*h+2+5*n) s
  else termB (2*h+11+5*(n+carry s-2)) (next s)
def termC (p s : Nat) : Cfg :=
  match s with
  | 0 => dReturn (p-2) | 1 => (.a0,p+5) | 2 => (.b0,p+6)
  | 3 => (.a2,p+6) | 4 => (.a2,p+6) | _ => (.a0,p+7)
def ret : Kind → Nat → Cfg
  | .a2,p => dReturn (p-4)
  | .a0,p =>
    let n := (p-5)/6; let s := (p-5)%6
    if p%2=0 then termC (2*p+6+5*n) s
    else termC (2*p+15+5*(n+carry s-2)) (next s)
  | .b0,p =>
    let n := (p-3)/6; let s := (p-3)%6
    let n' := n+carry s-1; let s' := next s
    if p%2=1 then termA (2*p+6+5*n') s'
    else termA (2*p+15+5*(n'+carry s'-2)) (next s')
theorem termB_bound (p s : Nat) : p ≤ (termB p s).2 := by
  unfold termB; split <;> simp <;> omega
theorem termA_bound (p s : Nat) : p ≤ (termA p s).2 := by
  unfold termA; split <;> simp <;> omega
theorem dReturn_bound (k : Nat) : 2*k+18 ≤ (dReturn k).2 := by
  unfold dReturn; dsimp only; split
  · have h := termB_bound (2*(k+8)+2+5*(k/6)) (k%6)
    omega
  · have h := termB_bound (2*(k+8)+11+5*(k/6+carry (k%6)-2)) (next (k%6))
    omega
theorem termC_bound (p s : Nat) : p ≤ (termC p s).2 := by
  unfold termC; split <;> try simp
  · have h := dReturn_bound (p-2); omega
  all_goals omega
theorem ret_growth (k : Kind) (p : Nat) (hp : 24 ≤ p) : 2*p ≤ (ret k p).2 := by
  cases k with
  | a2 => have h := dReturn_bound (p-4); simp only [ret]; omega
  | a0 =>
    unfold ret; dsimp only; split
    · have h := termC_bound (2*p+6+5*((p-5)/6)) ((p-5)%6); omega
    · have h := termC_bound (2*p+15+5*((p-5)/6+carry ((p-5)%6)-2)) (next ((p-5)%6)); omega
  | b0 =>
    unfold ret; dsimp only; split
    · have h := termA_bound (2*p+6+5*((p-3)/6+carry ((p-3)%6)-1)) (next ((p-3)%6)); omega
    · have h := termA_bound (2*p+15+5*((p-3)/6+carry ((p-3)%6)-1+carry (next ((p-3)%6))-2)) (next (next ((p-3)%6))); omega
theorem bank_guards (p : Nat) (hp : 24 ≤ p) :
    3 ≤ (p-4)/6 ∧ 3 ≤ (p-5)/6 ∧ 3 ≤ (p-3)/6 ∧
    2 ≤ (p-3)/6+carry ((p-3)%6)-1 := by omega
def orbit : Nat → Cfg
  | 0 => (.a2,39)
  | n+1 => let c := orbit n; ret c.1 c.2
theorem orbit_large (n : Nat) : 24 ≤ (orbit n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := ret_growth (orbit n).1 (orbit n).2 ih
    simp only [orbit]; omega
theorem orbit_growth (n : Nat) : 2*(orbit n).2 ≤ (orbit (n+1)).2 :=
  ret_growth _ _ (orbit_large n)
#print axioms ret_growth
#print axioms bank_guards
#print axioms orbit_large
#print axioms orbit_growth
#eval orbit 11
end Raw14086Arithmetic
