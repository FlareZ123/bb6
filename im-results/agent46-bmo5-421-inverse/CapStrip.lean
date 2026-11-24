import CapNegativePhase
namespace CapSieve

theorem pow3_mod4 (n : Nat) : 3^n%4=if n%2=0 then 1 else 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_mod,ih]
    split <;> rename_i h
    · have h' : (n+1)%2≠0 := by omega
      simp [h']
    · have h' : (n+1)%2=0 := by omega
      simp [h']

theorem unit_parity {j n w : Nat} (h : 3^n*w=2*(j+n)+3) : w%4=(2*j+3)%4 := by
  have hh:=congrArg (fun x:Nat=>x%4) h
  change (3^n*w)%4=(2*(j+n)+3)%4 at hh
  rw [Nat.mul_mod,pow3_mod4] at hh
  split at hh <;> omega

/-- Every divisor of the terminal boundary magnitude gives a real ancestry
    run, with no guarded-depth condition. -/
theorem terminal_up_exists (j n : Nat) :
    (∃ x, UpRun j n x (T (j+n))) ↔ 3^n∣2*(j+n)+3 := by
  constructor
  · rintro ⟨x,h⟩; exact terminal_up_divides h
  · rintro ⟨w,hw⟩
    have hp : 0<3^n := Nat.pow_pos (by decide)
    have hwpos : 0<w := by
      by_cases h0 : w=0
      · subst w; simp at hw
      · omega
    have hle : w≤2*j+3 := by
      exact Nat.le_of_mul_le_mul_left (by rw [←hw]; exact threshold_growth j n) hp
    have hpar := unit_parity hw.symm
    let z:=(2*j+3-w)/4
    have hz : 4*z+w=2*j+3 := by dsimp [z]; omega
    have hpj:=p_ge j
    have ht : T j+j+6=2*P j := by unfold P; rw [←Nat.mul_assoc]; exact t_add j
    have hl:=l_add j
    have hn:=l_add (j+1)
    rw [p_succ] at hn
    have hzl : z≤j+1 := by omega
    have hzt : z≤T j := by omega
    let x:=T j-z
    have hxadd : x+z=T j := Nat.sub_add_cancel hzt
    have hx : Band j x := by unfold Band; omega
    have hxw : W j x= -(w:Int) := by unfold W; omega
    have hwi : (3^n:Int)*(w:Int)=2*((j+n:Nat):Int)+3 := by exact_mod_cast hw.symm
    refine ⟨x,terminal_up_of_w hx ?_⟩
    rw [hxw,Int.mul_neg,hwi]

/-- At the end of the initial divisible run, a nonzero unit residue decides
    whether the whole ancestry has stopped, or must enter a positive-W sector. -/
theorem negative_unit_parent {j y : Nat} (hj : 6≤j) (hy : Band j y)
    (hneg : W j y<0) (hunit : W j y%3≠0) :
    (∃ x, Arc x y) ↔ W j y%3=(P j:Int)%3 := by
  have hp:=p_ge_large hj
  have hby:=band_bounds hy
  have hp0:=p_nonzero j
  have he : (W j y)%3=(2*(P j:Int)-(y:Int))%3 := by unfold W; omega
  have hlarge : P j+3≤y := by unfold W at hneg; omega
  have hrange : y+9≤4*P j := by omega
  have hpm : P j%3=1 ∨ P j%3=2 := hp0
  have hpm' : (P j:Int)%3=1 ∨ (P j:Int)%3=2 := by exact_mod_cast hpm
  have hneq1 : y+3≠P j := by omega
  have hneq2 : y+6≠P j := by omega
  have hc:=large_band_no_parent hj hy
  constructor
  · intro h
    have hn : y%3≠0 := by intro hh; exact (hc.mpr (Or.inl hh)) h
    omega
  · intro h
    by_cases hex : ∃ x, Arc x y
    · exact hex
    · have hh:=hc.mp hex
      omega

theorem p_parity_mod3 (j : Nat) : P j%3=if j%2=0 then 2 else 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [p_succ,Nat.mul_mod,ih]
    split <;> rename_i h
    · have h' : (j+1)%2≠0 := by omega
      simp [h']
    · have h' : (j+1)%2=0 := by omega
      simp [h']

/-- After stripping the 3-adic part of the terminal magnitude, its unit modulo
    12 decides whether the initial run is already a complete ancestry. -/
theorem stripped_unit_stop {j n w x : Nat} (hj : 6≤j)
    (h : 3^n*w=2*(j+n)+3) (hunit : w%3≠0)
    (hr : UpRun j n x (T (j+n))) :
    (¬ ∃ y, Arc y x) ↔ w%12=1 ∨ w%12=11 := by
  have hpar:=unit_parity h
  have hx:=(up_run_bands hr).1
  have hw:=(terminal_up_iff hx).mp hr
  have hi : (3^n:Int)*(w:Int)=2*((j+n:Nat):Int)+3 := by exact_mod_cast h
  have hpow : 0<(3^n:Int) := Int.pow_pos (by decide)
  have he : W j x= -(w:Int) := by
    apply Int.eq_of_mul_eq_mul_left (show (3^n:Int)≠0 by omega)
    rw [hw,Int.mul_neg,hi]
  have hneg : W j x<0 := by rw [he]; omega
  have hu : W j x%3≠0 := by rw [he]; omega
  have hparent:=negative_unit_parent hj hx hneg hu
  have hp:=p_parity_mod3 j
  constructor
  · intro hn
    have hneq : W j x%3≠(P j:Int)%3 := by intro hh; exact hn (hparent.mpr hh)
    rw [he] at hneq
    split at hp <;> omega
  · intro hc
    intro he'
    have hh:=hparent.mp he'
    rw [he] at hh
    split at hp <;> omega

/-- A closed sufficient terminal exclusion condition (for every exponent n). -/
theorem stripped_unit_root {j n w : Nat} (hj : 6≤j)
    (h : 3^n*w=2*(j+n)+3) (hc : w%12=1 ∨ w%12=11) :
    ∃ x, UpRun j n x (T (j+n)) ∧ (¬ ∃ y, Arc y x) ∧ 3<x := by
  obtain ⟨x,hr⟩ := (terminal_up_exists j n).mpr ⟨w,h.symm⟩
  have hx:=(up_run_bands hr).1
  have hp:=p_ge_large hj
  have hl:=l_add j
  have hroot : 3<x := by unfold Band at hx; omega
  exact ⟨x,hr,(stripped_unit_stop hj h (by omega) hr).mpr hc,hroot⟩

/-- Any existing parent after the maximal negative inverse run is regular
    in the same band, and its signed upper-boundary coordinate is positive. -/
theorem negative_unit_parent_positive {j x y : Nat} (hj : 6≤j) (hy : Band j y)
    (hneg : W j y<0) (hunit : W j y%3≠0) (ha : Arc x y) :
    RegFrom j x y ∧ 0<W j x := by
  have hP:=p_ge_large hj
  have hlow : P j+3≤y := by unfold W at hneg; omega
  have hreg : RegFrom j x y := by
    rcases (large_band_arc hj hy).mp ha with h|h|h|h
    · exact h
    · have hh:=w_regular_down h
      rw [show j-1+1=j by omega] at hh
      omega
    · obtain ⟨r,hr,_,hry⟩:=h
      have hp : P j=4*P (j-2) := by
        calc
          P j = P ((j-2)+1+1) := congrArg P (by omega)
          _ = 4*P (j-2) := by rw [p_succ,p_succ]; omega
      omega
    · omega
  have hh:=w_regular_same hreg
  have hb:=(w_bounds hy).1
  exact ⟨hreg,by omega⟩

#print axioms negative_unit_parent_positive
#print axioms terminal_up_exists
#print axioms stripped_unit_stop
#print axioms stripped_unit_root
end CapSieve
