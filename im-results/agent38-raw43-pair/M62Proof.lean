import M62B
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

/-- Removing exactly five initial zero bits from W2(k+1) leaves W2(k). -/
theorem w2_succ (k : Nat) (w : List Bool) :
    w2 (k+1)++w = zeros 5++(w2 k++w) := by
  have hn : 5*(k+1)+2 = 5+(5*k+2) := by omega
  simp only [w2,hn,zeros_add,List.append_assoc]

theorem w4_succ (k : Nat) (w : List Bool) :
    w4 (k+1)++w = zeros 5++(w4 k++w) := by
  have hn : 5*(k+1)+4 = 5+(5*k+4) := by omega
  simp only [w4,hn,zeros_add,List.append_assoc]

/-- Exhaust all W-code constructors in phase B. -/
theorem phase_b_step (L R : List Bool) (hL : LeftB L) (hR : Word R) :
    ∃ n L' R', 0<n ∧
      ((LeftA L' ∧ RightA R') ∨ (LeftB L' ∧ Word R')) ∧
      run0 table n (fSection L R) = some (fSection L' R') := by
  cases hR with
  | nil =>
      cases hL with
      | mk t s ht hs =>
          obtain ⟨n,L',R',hn,hLa,hRa,hrun⟩ :=
            phase_b_carry_empty t s ht hs
          exact ⟨n,L',R',hn,Or.inl ⟨hLa,hRa⟩,hrun⟩
  | two k w hw =>
      cases k with
      | zero =>
          exact ⟨11,bits "11111"++L,w,by omega,
            Or.inr ⟨left_b_five hL,hw⟩,
            by simpa only [Nat.mul_zero,Nat.zero_add,w2] using
              phase_b_two L w hw⟩
      | succ k =>
          cases hL with
          | mk t s ht hs =>
              obtain ⟨n,L',R',hn,hLa,hRa,hrun⟩ :=
                phase_b_carry_five t s (w2 k++w) ht hs (Word.two k w hw)
              refine ⟨n,L',R',hn,Or.inl ⟨hLa,hRa⟩,?_⟩
              simpa only [Nat.succ_eq_add_one,w2_succ] using hrun
  | four k w hw =>
      cases k with
      | zero =>
          exact ⟨11,bits "1100111"++L,w,by omega,
            Or.inr ⟨left_b_eleven hL,hw⟩,
            by simpa only [Nat.mul_zero,Nat.zero_add,w4] using
              phase_b_four L w hw⟩
      | succ k =>
          cases hL with
          | mk t s ht hs =>
              obtain ⟨n,L',R',hn,hLa,hRa,hrun⟩ :=
                phase_b_carry_five t s (w4 k++w) ht hs (Word.four k w hw)
              refine ⟨n,L',R',hn,Or.inl ⟨hLa,hRa⟩,?_⟩
              simpa only [Nat.succ_eq_add_one,w4_succ] using hrun

/-- The complete two-phase regular-language invariant for raw M62. -/
inductive Inv : Z0 → Prop
  | a (L R : List Bool) (hL : LeftA L) (hR : RightA R) :
      Inv (fSection L R)
  | b (L R : List Bool) (hL : LeftB L) (hR : Word R) :
      Inv (fSection L R)

/-- Every invariant checkpoint has a genuinely positive, defined first
return to another invariant checkpoint, using only assigned transitions. -/
theorem step_inv (z : Z0) (hz : Inv z) :
    ∃ n z', 0<n ∧ run0 table n z = some z' ∧ Inv z' := by
  cases hz with
  | a L R hL hR =>
      obtain ⟨n,L',R',hn,hLb,hW,hrun⟩ :=
        phase_a_step L R hL hR
      exact ⟨n,fSection L' R',hn,hrun,Inv.b L' R' hLb hW⟩
  | b L R hL hR =>
      obtain ⟨n,L',R',hn,hnxt,hrun⟩ :=
        phase_b_step L R hL hR
      rcases hnxt with ha | hb
      · exact ⟨n,fSection L' R',hn,hrun,Inv.a L' R' ha.1 ha.2⟩
      · exact ⟨n,fSection L' R',hn,hrun,Inv.b L' R' hb.1 hb.2⟩

theorem first_inv : Inv (fSection (bits "111") (bits "01")) := by
  have hleft : LeftA (ones 3) :=
    LeftA.mk (ones 3) [] (AFrame.base 0) OuterTail.nil
  have hleft' : LeftA (bits "111") := by
    simpa [bits,ones] using hleft
  exact Inv.a (bits "111") (bits "01") hleft' RightA.simple

/-- Unbounded original-machine live prefixes, not a numerical replay. -/
theorem live (N : Nat) :
    ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero =>
      exact ⟨12,_,by omega,section_blank,first_inv⟩
  | succ N ih =>
      obtain ⟨t,z,ht,hz,hi⟩ := ih
      obtain ⟨a,z',ha,hr,hi'⟩ := step_inv z hi
      exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper

/-- Original six-state semantics: EVERY completion of missing F1
  is nonhalting from the blank tape. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some z :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
      have H := zrun_sound table m hm t s z' hZ
      have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
      rw [hb] at H
      rw [show t=n+(t-n) by omega,run_append] at H
      cases he : run m n blank with
      | none => simp [he] at H
      | some c => rfl

#print axioms phase_b_step
#print axioms live
#print axioms never
end BB6.Agent38M62
