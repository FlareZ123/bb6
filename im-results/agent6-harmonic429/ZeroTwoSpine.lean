import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429.ZeroTwoSpine

def backStep (s : State) : State := ((s.1-3)/2,s.1+s.2)
def back (i : Nat) (s : State) : State :=
  match i with
  | 0 => s
  | i+1 => backStep (back i s)

private theorem pow_mul_ge (e c : Nat) (he : 6 ≤ e) (hc : 0 < c) :
    64 ≤ 2^e*c := by
  have h : 64 ≤ 2^e := Nat.pow_le_pow_right (n:=2) (by decide) he
  exact Nat.le_trans h (Nat.le_mul_of_pos_right _ hc)

private theorem first_step (e c b : Nat) (he : 6 ≤ e) (hc : 0 < c) :
    backStep (2^(e+1)*c-3,b) = (2^e*c-3,2^(e+1)*c-3+b) ∧
    next (backStep (2^(e+1)*c-3,b)) = some (2^(e+1)*c-3,b) := by
  have h : 64 ≤ 2^e*c := pow_mul_ge e c he hc
  have hp : 2^(e+1)*c=2*(2^e*c) := by
    rw [Nat.pow_succ, Nat.mul_right_comm, Nat.mul_comm (2^e*c) 2]
  have hb : (2^(e+1)*c-3-3)/2=2^e*c-3 := by omega
  constructor
  · simp [backStep,hb]
  · simp only [backStep,hb]
    have hguard : 2*(2^e*c-3)+3 ≤ 2^(e+1)*c-3+b := by omega
    simp only [next,ite_eq_left hguard,Option.some.injEq,Prod.mk.injEq]
    omega

/-- The entire inverse F chain stays in the row a = 61 mod 64. -/
theorem first_coordinate (d c b i : Nat) (hc : 0<c) (hi : i≤d) :
    (back i (2^(d+6)*c-3,b)).1 = 2^(d+6-i)*c-3 := by
  induction i with
  | zero => simp [back]
  | succ i ih =>
    have hp := ih (by omega)
    have he : 6 ≤ d+6-(i+1) := by omega
    have heq : d+6-i = (d+6-(i+1))+1 := by omega
    rw [heq] at hp
    have hpair : back i (2^(d+6)*c-3,b) =
        (2^((d+6-(i+1))+1)*c-3,(back i (2^(d+6)*c-3,b)).2) := by
      exact Prod.ext hp rfl
    change (backStep (back i (2^(d+6)*c-3,b))).1 = _
    rw [hpair]
    rw [(first_step (d+6-(i+1)) c _ he hc).1]

theorem row_and_size (d c b i : Nat) (hc : 0<c) (hi : i≤d) :
    (back i (2^(d+6)*c-3,b)).1 % 64 = 61 ∧
    61 ≤ (back i (2^(d+6)*c-3,b)).1 := by
  rw [first_coordinate d c b i hc hi]
  have he : 6 ≤ d+6-i := by omega
  have heq : d+6-i=6+(d-i) := by omega
  rw [heq,Nat.pow_add,show (2:Nat)^6=64 by decide,Nat.mul_assoc]
  have hpos : 0 < 2^(d-i)*c := Nat.mul_pos (Nat.pow_pos (by decide)) hc
  omega

theorem exact_edge (d c b i : Nat) (hc : 0<c) (hi : i<d) :
    next (back (i+1) (2^(d+6)*c-3,b)) = some (back i (2^(d+6)*c-3,b)) := by
  have hp := first_coordinate d c b i hc (by omega)
  have he : 6 ≤ d+6-(i+1) := by omega
  have heq : d+6-i=(d+6-(i+1))+1 := by omega
  rw [heq] at hp
  have hpair : back i (2^(d+6)*c-3,b) =
      (2^((d+6-(i+1))+1)*c-3,(back i (2^(d+6)*c-3,b)).2) := Prod.ext hp rfl
  change next (backStep (back i (2^(d+6)*c-3,b))) = some _
  rw [hpair]
  exact (first_step (d+6-(i+1)) c _ he hc).2

/-- Positive natural states, exact source edges, and no residue failure,
    for an arbitrarily long F-only inverse chain. -/
theorem arbitrary_depth (d c b : Nat) (hc : 0<c) :
    (∀ i≤d, (back i (2^(d+6)*c-3,b)).1%64=61 ∧
      61≤(back i (2^(d+6)*c-3,b)).1) ∧
    (∀ i<d, next (back (i+1) (2^(d+6)*c-3,b)) =
      some (back i (2^(d+6)*c-3,b))) :=
  ⟨fun i hi => row_and_size d c b i hc hi,fun i hi => exact_edge d c b i hc hi⟩

/-- The exact positive-counter residue tests of side_branch_sieve.js.
    This is a predicate on candidate inverse states, not a root theorem. -/
def necessary (a b : Nat) : Prop :=
  (if a%2=0 then b%16=(if a%4=0 then 2 else 10) else
    ((a%8=1 ∧ b%4≠3) ∨ (a%8=3 ∧ b%4≠0) ∨ a%8=5 ∨
      (a%8=7 ∧ (b%4=2 ∨ b%4=3))) ∧
    (a%8=7 → b%8=2 ∨ b%8=3) ∧
    (a%16=1 → b%8=1 ∨ b%8=2) ∧
    (a%32=5 → b%8=2 ∨ b%8=4 ∨ b%8=5) ∧
    (b%2=1 →
      ((a%16=1 ∨ a%16=9) → b%8=1) ∧
      ((a%16=3 ∨ a%16=11) → b%8=7) ∧
      ((a%16=7 ∨ a%16=15) → b%8=3))) ∧
  ¬ ((a%16=15 ∧ b%32=26) ∨
     (a%32=15 ∧ b%32=24) ∨ (a%32=31 ∧ b%32=24) ∨
     (a%32=1 ∧ b%32=25) ∨
     (a%64=1 ∧ b%32=23) ∨ (a%64=33 ∧ b%32=23) ∨
     (a%64=5 ∧ b%32=20) ∨ (a%16=3 ∧ b%32=18) ∨
     (a%32=9 ∧ b%32=9) ∨ (a%64=21 ∧ b%32=20))

theorem row61_necessary (a b : Nat) (h : a%64=61) : necessary a b := by
  have h2 : a%2=1 := by omega
  have h8 : a%8=5 := by omega
  have h16 : a%16=13 := by omega
  have h32 : a%32=29 := by omega
  simp [necessary,h2,h8,h16,h32,h]

private theorem le_pow_two (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have h : 0 < 2^n := Nat.pow_pos (by decide)
    omega

/-- For every depth d, an exact diagonal zero-two candidate has an F-only
    predecessor path of that length, with every vertex passing the sieve.
    Thus this fixed-depth residue filter cannot exclude the entire family. -/
theorem congruence_spine (d r : Nat) (hr : 0<r) :
    ∃ m J N a z : Nat,
      m=2+2^(d+6)*r ∧ J=4*m+2 ∧ N=8*2^J+J-11 ∧
      z+48*2^J+3*J=12*2^(N+2)+36 ∧ z%4=2 ∧
      129≤a ∧ next (a,2*a+2)=some (0,z) ∧
      (∀ i≤d, 61≤(back i (a,2*a+2)).1 ∧
        necessary (back i (a,2*a+2)).1 (back i (a,2*a+2)).2) ∧
      (∀ i<d, next (back (i+1) (a,2*a+2))=some (back i (a,2*a+2))) := by
  let e := d+6
  let t := 2^e
  let m := 2+t*r
  let J := 4*m+2
  let N := 8*2^J+J-11
  let x := 2^(J-e)
  let y := 2^(N-e)
  have ht : 64≤t := Nat.pow_le_pow_right (n:=2) (by decide) (show 6≤e by omega)
  have het : e≤t := le_pow_two e
  have htr : t≤t*r := Nat.le_mul_of_pos_right t hr
  have hrt : r≤t*r := Nat.le_mul_of_pos_left r (by omega)
  have heJ : e≤J := by dsimp [J,m]; omega
  have hJ : 10≤J := by dsimp [J,m]; omega
  have hpowJ : 4≤2^J := Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤J by omega)
  have hJN : J+1≤N := by dsimp [N]; omega
  have hx : 0<x := Nat.pow_pos (by decide)
  have hrx : r≤x := by
    have h : r≤J-e := by dsimp [J,m]; omega
    exact Nat.le_trans h (le_pow_two (J-e))
  have hy : 2*x≤y := by
    have hh : 2^(J-e+1)≤2^(N-e) :=
      Nat.pow_le_pow_right (n:=2) (by decide) (by omega)
    rw [Nat.pow_succ] at hh
    dsimp [x,y]; omega
  let c := 12*y-12*x-3*r
  have hc : 9≤c := by dsimp [c]; omega
  let a := t*c-3
  let z := 4*a+18
  have hat : 576≤t*c := by
    have h := Nat.mul_le_mul ht hc
    exact h
  have ha : 129≤a := by dsimp [a]; omega
  have hX : 2^J=t*x := by
    dsimp [t,x]
    rw [← Nat.pow_add,show e+(J-e)=J by omega]
  have hY : 2^N=t*y := by
    dsimp [t,y]
    rw [← Nat.pow_add,show e+(N-e)=N by omega]
  have hcx : c+12*x+3*r=12*y := by dsimp [c]; omega
  have hmul := congrArg (fun q : Nat => t*q) hcx
  simp only [Nat.mul_add, Nat.mul_left_comm t 12, Nat.mul_left_comm t 3] at hmul
  have hcoord : a+12*2^J+3*m=12*2^N+3 := by
    rw [hX,hY]
    dsimp [a,m]
    omega
  have hN2 : 2^(N+2)=4*2^N := by
    rw [Nat.pow_add,show (2:Nat)^2=4 by decide,Nat.mul_comm]
  have hJdef : J=4*m+2 := rfl
  have hzdef : z=4*a+18 := rfl
  have hz : z+48*2^J+3*J=12*2^(N+2)+36 := by
    rw [hN2]
    omega
  have hstep : next (a,2*a+2)=some (0,z) := by
    have hguard : ¬ 2*a+3≤2*a+2 := by omega
    simp [next,show ¬ 2*a+2≥2*a+3 by omega,z]
  have hs := arbitrary_depth d c (2*a+2) (by omega)
  change (∀ i≤d, (back i (a,2*a+2)).1%64=61 ∧ 61≤(back i (a,2*a+2)).1) ∧
    (∀ i<d, next (back (i+1) (a,2*a+2))=some (back i (a,2*a+2))) at hs
  refine ⟨m,J,N,a,z,rfl,rfl,rfl,hz,?_,ha,hstep,?_,hs.2⟩
  · dsimp [z]; omega
  · intro i hi
    obtain ⟨hr,hsz⟩ := hs.1 i hi
    exact ⟨hsz,row61_necessary _ _ hr⟩

#print axioms arbitrary_depth
#print axioms row61_necessary
#print axioms congruence_spine
end BB429.ZeroTwoSpine
