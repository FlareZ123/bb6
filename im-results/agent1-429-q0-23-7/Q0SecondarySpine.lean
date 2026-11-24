import Lean

namespace BB429Q0Secondary

abbrev State := Int × Int

def allowed (a b : Int) : Prop :=
  (a%8=0 ∧ (b%4=0 ∨ b%4=2)) ∨
  (a%8=1 ∧ (b%4=0 ∨ b%4=1 ∨ b%4=2)) ∨
  (a%8=2 ∧ b%4=2) ∨
  (a%8=3 ∧ (b%4=1 ∨ b%4=2 ∨ b%4=3)) ∨
  (a%8=4 ∧ b%4=2) ∨ a%8=5 ∨
  (a%8=6 ∧ b%4=2) ∨ (a%8=7 ∧ (b%4=2 ∨ b%4=3))

-- Exact residue tests listed by Agent6's depth-16 sieve, on positive first counters.
-- This is a copied arithmetic model, not an import of the original source.
def rootOK (s : State) : Prop :=
  let (a,b) := s
  allowed a b ∧ (a%2=0 → b%8=2) ∧
  ¬(a%8=7 ∧ b%8=7) ∧ ¬(a%16=1 ∧ b%8=6) ∧
  ¬(a%16=5 ∧ b%8=6) ∧ ¬(a%32=5 ∧ b%16=1) ∧
  (a%16=11 → b%8=2 ∨ b%8=6 ∨ b%8=7) ∧
  (a%32=19 ∨ a%32=27 → b%8=2 ∨ b%8=7) ∧
  ¬(a%16=15 ∧ b%32=26) ∧ ¬(a%32=15 ∧ b%32=24) ∧
  ¬(a%32=31 ∧ b%32=24) ∧ ¬(a%32=1 ∧ b%32=25) ∧
  ¬(a%64=1 ∧ b%32=23) ∧ ¬(a%64=33 ∧ b%32=23) ∧
  ¬(a%64=5 ∧ b%32=20) ∧ ¬(a%16=3 ∧ b%32=18) ∧
  ¬(a%32=9 ∧ b%32=9) ∧ ¬(a%64=21 ∧ b%32=20)

inductive Label where | f | s | e deriving DecidableEq, Repr

inductive Inv : Label → State → State → Prop where
  | f (a b : Int) (ha : 13 ≤ a) (hb : 0 ≤ b) (odd : a%2=1) :
      Inv .f (a,b) ((a-3)/2,b+a)
  | s (a b : Int) (ha : 13 ≤ a) (hb : 0 ≤ b) (odd : a%2=1) (res : b%4=2) :
      Inv .s (a,b) ((4*a+b-26)/4,(b+4)/2)
  | e (a b : Int) (ha : 6 ≤ a) (hb : 0 ≤ b) (even : a%2=0) (res : b%8=2) :
      Inv .e (a,b) ((4*a+b-14)/4,b/2)

inductive Path : List Label → State → State → Prop where
  | nil (s : State) (ok : rootOK s) : Path [] s s
  | cons {l ls x y z} (ok : rootOK x) (h : Inv l x y) (tail : Path ls y z) :
      Path (l::ls) x z

theorem path_append {ls ms x y z} (p : Path ls x y) (q : Path ms y z) : Path (ls++ms) x z := by
  induction p with
  | nil _ _ => exact q
  | cons ok h _ ih => exact .cons ok h (ih q)

theorem rootOK_61 (a b : Int) (ha : a%64=61) : rootOK (a,b) := by
  have h8 : a%8=5 := by omega
  have h16 : a%16=13 := by omega
  have h32 : a%32=29 := by omega
  have h2 : a%2=1 := by omega
  simp [rootOK, allowed, ha, h8, h16, h32, h2]

-- The three blocks are fixed affine words. w is any positive multiple of 64.
theorem three_blocks (t : Int) (ht : 0<t) :
    Path [.f,.s,.f,.e,.f,.s,.f,.e,.f,.s,.f,.e]
      ((262144*t + 21), (524288*t + 29)) ((349504*t - 3), (349568*t + 5)) := by
  refine Path.cons (y := ((131072*t + 9), (786432*t + 50))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (262144*t + 21) (524288*t + 29) (by omega) (by omega) (by omega)
    have h1 : ((262144*t + 21)-3)/2 = (131072*t + 9) := by omega
    have h2 : (524288*t + 29)+(262144*t + 21) = (786432*t + 50) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((327680*t + 15), (393216*t + 27))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.s (131072*t + 9) (786432*t + 50) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(131072*t + 9)+(786432*t + 50)-26)/4 = (327680*t + 15) := by omega
    have h2 : ((786432*t + 50)+4)/2 = (393216*t + 27) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((163840*t + 6), (720896*t + 42))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (327680*t + 15) (393216*t + 27) (by omega) (by omega) (by omega)
    have h1 : ((327680*t + 15)-3)/2 = (163840*t + 6) := by omega
    have h2 : (393216*t + 27)+(327680*t + 15) = (720896*t + 42) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((344064*t + 13), (360448*t + 21))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.e (163840*t + 6) (720896*t + 42) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(163840*t + 6)+(720896*t + 42)-14)/4 = (344064*t + 13) := by omega
    have h2 : (720896*t + 42)/2 = (360448*t + 21) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((172032*t + 5), (704512*t + 34))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (344064*t + 13) (360448*t + 21) (by omega) (by omega) (by omega)
    have h1 : ((344064*t + 13)-3)/2 = (172032*t + 5) := by omega
    have h2 : (360448*t + 21)+(344064*t + 13) = (704512*t + 34) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((348160*t + 7), (352256*t + 19))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.s (172032*t + 5) (704512*t + 34) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(172032*t + 5)+(704512*t + 34)-26)/4 = (348160*t + 7) := by omega
    have h2 : ((704512*t + 34)+4)/2 = (352256*t + 19) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((174080*t + 2), (700416*t + 26))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (348160*t + 7) (352256*t + 19) (by omega) (by omega) (by omega)
    have h1 : ((348160*t + 7)-3)/2 = (174080*t + 2) := by omega
    have h2 : (352256*t + 19)+(348160*t + 7) = (700416*t + 26) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((349184*t + 5), (350208*t + 13))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.e (174080*t + 2) (700416*t + 26) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(174080*t + 2)+(700416*t + 26)-14)/4 = (349184*t + 5) := by omega
    have h2 : (700416*t + 26)/2 = (350208*t + 13) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((174592*t + 1), (699392*t + 18))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (349184*t + 5) (350208*t + 13) (by omega) (by omega) (by omega)
    have h1 : ((349184*t + 5)-3)/2 = (174592*t + 1) := by omega
    have h2 : (350208*t + 13)+(349184*t + 5) = (699392*t + 18) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((349440*t - 1), (349696*t + 11))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.s (174592*t + 1) (699392*t + 18) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(174592*t + 1)+(699392*t + 18)-26)/4 = (349440*t - 1) := by omega
    have h2 : ((699392*t + 18)+4)/2 = (349696*t + 11) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((174720*t - 2), (699136*t + 10))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.f (349440*t - 1) (349696*t + 11) (by omega) (by omega) (by omega)
    have h1 : ((349440*t - 1)-3)/2 = (174720*t - 2) := by omega
    have h2 : (349696*t + 11)+(349440*t - 1) = (699136*t + 10) := by omega
    rw [h1,h2] at h
    exact h
  refine Path.cons (y := ((349504*t - 3), (349568*t + 5))) ?_ ?_ ?_
  · simp [rootOK, allowed] <;> omega
  · have h := Inv.e (174720*t - 2) (699136*t + 10) (by omega) (by omega) (by omega) (by omega)
    have h1 : (4*(174720*t - 2)+(699136*t + 10)-14)/4 = (349504*t - 3) := by omega
    have h2 : (699136*t + 10)/2 = (349568*t + 5) := by omega
    rw [h1,h2] at h
    exact h
  exact Path.nil _ (rootOK_61 _ _ (by omega))

theorem allF (k : Nat) (t b : Int) (ht : 0<t) (hb : 0≤b) :
    Path (List.replicate k .f)
      (64*((2:Int)^k*t)-3,b)
      (64*t-3,b+128*((2:Int)^k*t-t)-3*(k:Int)) := by
  induction k generalizing b with
  | zero =>
    simp only [List.replicate_zero, Int.pow_zero, Int.one_mul, Int.ofNat_zero]
    have hz : b+128*(t-t)-3*0=b := by omega
    rw [hz]
    exact .nil _ (rootOK_61 _ _ (by omega))
  | succ k ih =>
    have hP : (0:Int)<2^k := Int.pow_pos (by decide : (0:Int)<2)
    have hT : 0<(2:Int)^k*t := Int.mul_pos hP ht
    have heq : (2:Int)^(k+1)*t = 2*(2^k*t) := by
      simp only [Int.pow_succ]
      ac_rfl
    rw [heq, List.replicate_succ]
    refine Path.cons (y := (64*((2:Int)^k*t)-3,b+(128*((2:Int)^k*t)-3))) ?_ ?_ ?_
    · exact rootOK_61 _ _ (by omega)
    · have hf := Inv.f (64*(2*((2:Int)^k*t))-3) b (by omega) hb (by omega)
      have ha : (64*(2*((2:Int)^k*t))-3-3)/2=64*((2:Int)^k*t)-3 := by omega
      have hb' : b+(64*(2*((2:Int)^k*t))-3)=b+(128*((2:Int)^k*t)-3) := by omega
      rw [ha,hb'] at hf
      exact hf
    · have h := ih (b+(128*((2:Int)^k*t)-3)) (by omega)
      have hlast : b+(128*((2:Int)^k*t)-3)+128*((2:Int)^k*t-t)-3*(k:Int) =
        b+128*(2*((2:Int)^k*t)-t)-3*((k+1:Nat):Int) := by omega
      rwa [hlast] at h

/-- Every length k is attained by the *same fixed* three-block prefix followed by F^k,
    with all vertices passing the copied necessary conditions. -/
theorem secondary_spine (k : Nat) (t : Int) (ht : 0<t) :
    ∃ z, Path ([.f,.s,.f,.e,.f,.s,.f,.e,.f,.s,.f,.e] ++ List.replicate k .f)
      (262144*((2:Int)^k*t)+21,524288*((2:Int)^k*t)+29) z := by
  have hP : 0<(2:Int)^k := Int.pow_pos (by decide : (0:Int)<2)
  have hT : 0<(2:Int)^k*t := Int.mul_pos hP ht
  have h := three_blocks ((2:Int)^k*t) hT
  have hf := allF k (5461*t) (349568*((2:Int)^k*t)+5) (by omega) (by omega)
  have heq : 64*((2:Int)^k*(5461*t))-3 = 349504*((2:Int)^k*t)-3 := by
    have h1 : (2:Int)^k*(5461*t)=5461*((2:Int)^k*t) := by ac_rfl
    rw [h1]
    omega
  rw [heq] at hf
  exact ⟨_,path_append h hf⟩


-- Explicit q0 parameters with arbitrarily large valuation, avoiding an existence axiom.
def parameter : Nat → Nat
  | 0 => 1
  | s+1 => 4*parameter s+5

theorem parameter_lower (s : Nat) : s+1 ≤ parameter s := by
  induction s with
  | zero => decide
  | succ s ih => simp only [parameter]; omega

theorem parameter_eq (s : Nat) : 3*(parameter s:Int)+5 = (2:Int)^(2*s+3) := by
  induction s with
  | zero => decide
  | succ s ih =>
    have h : 2*(s+1)+3=(2*s+3)+2 := by omega
    rw [h,Int.pow_add]
    simp only [parameter, Int.natCast_add, Int.natCast_mul]
    have hp : (2:Int)^2=4 := by decide
    rw [hp,← ih]
    omega

def q0a (u : Nat) : Int := 13*(2:Int)^(23+32*u)-24*(u:Int)-19

private theorem factor (P E N r v : Int) (hE : E=P*r) (hN : N=E*v) :
    P*(r*(13*v-1))=13*N-E := by
  rw [hN,hE, ← Int.mul_assoc, Int.mul_sub, Int.mul_one]
  have h : P*r*(13*v)=13*(P*r*v) := by ac_rfl
  rw [h]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem q0_unbounded_secondary (k : Nat) :
    ∃ u : Nat, ∃ z, Path
      ([.f,.s,.f,.e,.f,.s,.f,.e,.f,.s,.f,.e] ++ List.replicate k .f)
      (q0a u,2*q0a u-13) z := by
  let s := k+6
  let u := parameter s
  let n := 23+32*u
  let e := 2*s+6
  let p := 18+k
  have hu : s+1≤u := parameter_lower s
  have he : e≤n := by dsimp [e,n]; omega
  have hp : p≤e := by dsimp [p,e,s]; omega
  let v : Int := (2:Int)^(n-e)
  let r : Int := (2:Int)^(e-p)
  have hv : 0<v := Int.pow_pos (by decide : (0:Int)<2)
  have hr : 0<r := Int.pow_pos (by decide : (0:Int)<2)
  let t := r*(13*v-1)
  have ht : 0<t := Int.mul_pos hr (by omega)
  have hnr : (2:Int)^n = (2:Int)^e*v := by
    dsimp [v]
    rw [← Int.pow_add, Nat.add_sub_of_le he]
  have hep : (2:Int)^e = (2:Int)^p*r := by
    dsimp [r]
    rw [← Int.pow_add, Nat.add_sub_of_le hp]
  have hwp : q0a u-21 = 13*(2:Int)^n-(2:Int)^e := by
    have hpar := parameter_eq s
    have heq : (2:Int)^e = (2:Int)^(2*s+3)*8 := by
      have h : e=(2*s+3)+3 := by dsimp [e]
      rw [h,Int.pow_add]
      rfl
    rw [heq,← hpar]
    dsimp [q0a,n,u]
    omega
  have hprod : (2:Int)^p*t = 13*(2:Int)^n-(2:Int)^e := by
    exact factor ((2:Int)^p) ((2:Int)^e) ((2:Int)^n) r v hep hnr
  have hpow : (2:Int)^p = 262144*(2:Int)^k := by
    dsimp [p]
    rw [Int.pow_add]
    rfl
  have hinit : q0a u=262144*((2:Int)^k*t)+21 := by
    rw [hpow,Int.mul_assoc] at hprod
    omega
  obtain ⟨z,h⟩ := secondary_spine k t ht
  refine ⟨u,z,?_⟩
  rw [hinit]
  have hb : 2*(262144*((2:Int)^k*t)+21)-13=524288*((2:Int)^k*t)+29 := by omega
  rw [hb]
  exact h

#print axioms three_blocks
#print axioms allF
#print axioms secondary_spine
#print axioms q0_unbounded_secondary
end BB429Q0Secondary
