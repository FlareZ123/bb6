import CapBandRun
import CapPositiveMacroCore

namespace CapSieve

/-- Maximal same-band run, followed by its first non-same-band event. -/
def bandCount (k q : Nat) : Nat := CapMacro.tripleCount (2*P k+k+2) q

def bandLastQ (k q : Nat) : Nat := 3^(bandCount k q)*q

def bandMacro (k q : Nat) : Option (Nat × Nat) :=
  let z := bandLastQ k q
  let u := 3*z
  if z=2*P k+k then none
  else if z=2*P k+k+2 then some (k+1,3*k+15)
  else if u≤6*P k+k then some (k+1,u+3-2*P k)
  else some (k+2,u+6-6*P k)

/-- Exact range and parity of the endpoint coordinate. -/
theorem band_last_spec {k x : Nat} (hb : Band k x) :
    let z := bandLastQ k (Q k x)
    Q k x≤z ∧ z≤2*P k+k+2 ∧ 2*P k+k+2<3*z ∧ z%2=k%2 := by
  dsimp
  have hq := q_bounds hb
  obtain ⟨hlo,hhi⟩ := CapMacro.tripleCount_spec (show 0<Q k x by omega) hq.2
  change bandLastQ k (Q k x)≤2*P k+k+2 at hlo
  rw [Nat.pow_succ] at hhi
  change 2*P k+k+2< (3^(bandCount k (Q k x))*3)*Q k x at hhi
  have h3 : (3^(bandCount k (Q k x))*3)*Q k x=3*bandLastQ k (Q k x) := by unfold bandLastQ; ac_rfl
  rw [h3] at hhi
  have hpos : 0<3^(bandCount k (Q k x)) := Nat.pow_pos (by decide)
  have hmin := Nat.le_mul_of_pos_left (Q k x) hpos
  change Q k x≤bandLastQ k (Q k x) at hmin
  have hpar : ∀ n : Nat, 3^n%2=1 := by
    intro n; induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
  refine ⟨hmin,hlo,hhi,?_⟩
  unfold bandLastQ
  rw [Nat.mul_mod,hpar]
  have hQ : Q k x%2=k%2 := by unfold Q; omega
  simp [hQ]

/-- Realize every coordinate in the exact band range and parity. -/
theorem q_realize {k q : Nat} (hlo : k+6≤q) (hhi : q≤2*P k+k+2)
    (hpar : q%2=k%2) : ∃ x, Band k x ∧ Q k x=q := by
  let r := (q-(k+6))/2
  let x := L k+r
  have he : q=2*r+k+6 := by dsimp [r]; omega
  have hp := p_ge k
  have hb : Band k x := by unfold Band; rw [l_succ]; dsimp [x]; omega
  exact ⟨x,hb,by unfold Q; dsimp [x]; omega⟩

/-- Complete forward band macro: a certified same-band run, then halt or
    an actual transition to one of the next two bands. -/
theorem band_macro_sound {k x : Nat} (hb : Band k x) :
    ∃ z, SameRun k (bandCount k (Q k x)) x z ∧
      Q k z=bandLastQ k (Q k x) ∧
      match bandMacro k (Q k x) with
      | none => z=T k
      | some (j,q) => k<j ∧ j≤k+2 ∧ ∃ y, Arc z y ∧ Band j y ∧ Q j y=q := by
  obtain ⟨hlo,hhi,hcross,hpar⟩ := band_last_spec hb
  have hq := q_bounds hb
  obtain ⟨z,hbz,hz⟩ := q_realize (show k+6≤bandLastQ k (Q k x) by omega) hhi hpar
  have hs : SameRun k (bandCount k (Q k x)) x z := same_run_of_q hb hbz hz
  refine ⟨z,hs,hz,?_⟩
  unfold bandMacro
  dsimp
  rw [←hz]
  by_cases ht : Q k z=2*P k+k
  · rw [if_pos ht]
    exact q_inj hbz (terminal_band k) (ht.trans (q_terminal k).symm)
  · rw [if_neg ht]
    by_cases hsp : Q k z=2*P k+k+2
    · rw [if_pos hsp]
      have he := q_inj hbz (special_band k) (hsp.trans (q_special k).symm)
      have hy := special_target_band k
      have hyq := q_eq hy
      rw [p_succ] at hyq
      exact ⟨by omega,by omega,2*P k,by rw [he]; exact Arc.special k,hy,by omega⟩
    · rw [if_neg hsp]
      let a := z-L k
      have hza : z=L k+a := by have := hbz.1; dsimp [a]; omega
      have hqa : Q k z=2*a+k+6 := by unfold Q; rfl
      have ha : a+4≤P k := by rw [←hz] at hhi hpar; omega
      let y := 3*a+P k+3
      have harc : Arc z y := by rw [hza]; exact Arc.regular k a ha
      have hl1 := l_add (k+1)
      rw [p_succ] at hl1
      have hl2 := l_add (k+2)
      have hp2 : P (k+2)=4*P k := by rw [show k+2=(k+1)+1 by omega,p_succ,p_succ]; omega
      rw [hp2] at hl2
      have hl3 := l_add (k+3)
      have hp3 : P (k+3)=8*P k := by rw [show k+3=(k+2)+1 by omega,p_succ,hp2]; omega
      rw [hp3] at hl3
      have hp := p_ge k
      have hy : y=3*a+P k+3 := rfl
      rw [←hz] at hcross
      by_cases hnext : 3*Q k z≤6*P k+k
      · rw [if_pos hnext]
        have hyb : Band (k+1) y := by change L (k+1)≤y ∧ y<L (k+2); omega
        have hyq := q_eq hyb
        rw [p_succ] at hyq
        exact ⟨by omega,by omega,y,harc,hyb,by omega⟩
      · rw [if_neg hnext]
        have hyb : Band (k+2) y := by change L (k+2)≤y ∧ y<L (k+3); omega
        have hyq := q_eq hyb
        rw [hp2] at hyq
        exact ⟨by omega,by omega,y,harc,hyb,by omega⟩

#print axioms band_last_spec
#print axioms q_realize
#print axioms band_macro_sound
end CapSieve
