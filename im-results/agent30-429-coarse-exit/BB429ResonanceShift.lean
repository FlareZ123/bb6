import BB429ResonanceMinimal

namespace BB429.CoarseExit

set_option maxHeartbeats 10000000

/-- Removing a leading false digit from a temporal base-four word merely
    shifts the remaining branch function. -/
theorem word4_shift_false (e : Nat → Bool) (i : Nat) (h0 : e 0=false) :
    word4 e (i+1)=word4 (fun k => e (k+1)) i := by
  induction i with
  | zero =>
      simp [word4,h0]
  | succ i ih =>
      simp only [word4,ih]
      rfl

/-- PhaseBlocks is stable under dropping its first ordinary two-step block. -/
theorem phaseBlocks_shift (U V : Nat → Int) (e ph : Nat → Bool) (n : Nat)
    (hs : PhaseBlocks U V e ph (n+1)) :
    PhaseBlocks (fun k => U (k+1)) (fun k => V (k+1))
      (fun k => e (k+1)) (fun k => ph (k+1)) n := by
  intro i hi
  have h := hs (i+1) (by omega)
  simpa only [show i+1+1=i+2 by omega,show (i+1)+1=i+2 by omega] using h


/-- If the initial odd-rank phase agrees with the parity of the remaining
    block count, alternating PhaseBlocks always finish in phase false. -/
theorem phaseBlocks_end_false
    (U V : Nat → Int) (e ph : Nat → Bool) (n : Nat)
    (hs : PhaseBlocks U V e ph n)
    (hstart : ph 0=decide (n%2=1)) :
    ph n=false := by
  induction n generalizing U V e ph with
  | zero =>
      simpa using hstart
  | succ n ih =>
      have hhead := hs 0 (by omega)
      have hpar :
          decide ((n+1)%2=1) = !decide (n%2=1) := by
        have hb := Nat.mod_lt n (by decide : 0<2)
        by_cases hz : n%2=0
        · have hsuc : (n+1)%2=1 := by omega
          simp [hz,hsuc]
        · have hone : n%2=1 := by omega
          have hsuc : (n+1)%2=0 := by omega
          simp [hone,hsuc]
      have hstart' : ph 1=decide (n%2=1) := by
        rw [hhead.1,hstart,hpar]
        simp
      have hshift := phaseBlocks_shift U V e ph n hs
      have hh := ih
        (fun k => U (k+1)) (fun k => V (k+1))
        (fun k => e (k+1)) (fun k => ph (k+1))
        hshift hstart'
      simpa only [show n+1=n+1 by rfl] using hh

/-- A leading false ordinary block is exactly FF at the transformed level:
    U is multiplied by four and V-error increases by 18. -/
theorem phaseBlocks_false_head
    (U V : Nat → Int) (e ph : Nat → Bool) (n : Nat)
    (hs : PhaseBlocks U V e ph (n+1)) (h0 : e 0=false) :
    ph 1= !ph 0 ∧ U 1=4*U 0 ∧ V 1=V 0+18 := by
  have h := hs 0 (by omega)
  simpa [h0] using h

/-- Absorb a leading false block into the burst scale.  This is the algebraic
    operation used to strip leading zero base-four digits from a nonminimal
    second resonance. -/
theorem d234_false_head_rescale
    (i : Nat) (a P y : Int)
    (U V : Nat → Int) (e ph : Nat → Bool)
    (hs : PhaseBlocks U V e ph (i+1)) (h0 : e 0=false)
    (hU : U 0=a*P)
    (hV : V 0=(54*(4:Int)^(i+1))*P+y) :
    U 1=a*(4*P) ∧
    V 1=(54*(4:Int)^i)*(4*P)+(y+18) := by
  obtain ⟨_,hu,hv⟩ := phaseBlocks_false_head U V e ph i hs h0
  rw [hu,hv,hU,hV,Int.pow_succ]
  constructor <;> grind +ring

/-- The d=234 low-order V-error formula is invariant under the same shift:
    y(i)+18 = y(i-1). -/
theorem d234_y_shift (m i : Nat) (hi : 1≤i) :
    (108*(m:Int)+777-18*(i:Int))+18 =
      108*(m:Int)+777-18*((i-1:Int)) := by
  push_cast
  omega

/-- The linear budget strictly decreases when one false head block is
    absorbed into P. -/
theorem budget_false_shift (i : Nat) (y : Int) :
    budget 0 (y+18) (i+3) = budget 0 y (i+4)-48 := by
  simp [budget]
  omega

#print axioms word4_shift_false
#print axioms phaseBlocks_shift
#print axioms phaseBlocks_end_false
#print axioms d234_false_head_rescale
#print axioms d234_y_shift
#print axioms budget_false_shift

end BB429.CoarseExit
