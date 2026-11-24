import CapBandBoundary
namespace CapSieve

/-- The positive threshold grows linearly, strictly slower than a 3-power. -/
theorem threshold_growth (j n : Nat) : 2*(j+n)+3≤3^n*(2*j+3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_assoc,show 3*(2*j+3)= (2*j+3)*3 by omega,←Nat.mul_assoc]
    omega

theorem threshold_growth_strict (j n : Nat) : 2*(j+(n+1))+3<3^(n+1)*(2*j+3) := by
  have h:=threshold_growth j n
  rw [Nat.pow_succ,Nat.mul_assoc,show 3*(2*j+3)=(2*j+3)*3 by omega,←Nat.mul_assoc]
  omega

/-- An exact negative-sector endpoint equation is sufficient for an authentic
    run of single-band regular edges, not merely necessary. -/
theorem terminal_up_of_w {j n x : Nat} (hx : Band j x)
    (hw : (3^n:Int)*W j x= -(2*((j+n:Nat):Int)+3)) :
    UpRun j n x (T (j+n)) := by
  induction n generalizing j x with
  | zero =>
    simp at hw ⊢
    have ht:=w_terminal j
    have he : x=T j := by unfold W at hw ht; omega
    subst x
    exact .zero hx
  | succ n ih =>
    have hpow : 0<(3^(n+1):Int) := Int.pow_pos (by decide)
    have hneg : W j x<0 := by
      by_cases h : W j x<0
      · exact h
      · have hh:=Int.mul_nonneg (Int.le_of_lt hpow) (show 0≤W j x by omega)
        omega
    have hg : (2*((j+(n+1):Nat):Int)+3)<(3^(n+1):Int)*(2*(j:Int)+3) := by exact_mod_cast threshold_growth_strict j n
    have hregular : -(2*(j:Int)+3)<W j x := by
      by_cases h : -(2*(j:Int)+3)<W j x
      · exact h
      · have hh:=Int.mul_le_mul_of_nonneg_left (show W j x≤ -(2*(j:Int)+3) by omega) (Int.le_of_lt hpow)
        rw [Int.mul_neg] at hh
        omega
    let r:=x-L j
    have he : x=L j+r := by dsimp [r]; have := hx.1; omega
    have hr : r+4≤P j := by
      have hl:=l_add j
      unfold W at hregular
      dsimp [r]
      omega
    let z:=3*r+P j+3
    have hreg : RegFrom j x z := ⟨r,hr,he,rfl⟩
    have hzW:=w_regular_down hreg
    have hw' : (3^n:Int)*W (j+1) z= -(2*(((j+1)+n:Nat):Int)+3) := by
      rw [hzW,←Int.mul_assoc,←Int.pow_succ]
      rw [hw]
      omega
    have hpos : 0<(3^n:Int) := Int.pow_pos (by decide)
    have hg' : (2*(((j+1)+n:Nat):Int)+3)≤(3^n:Int)*(2*((j+1:Nat):Int)+3) := by exact_mod_cast threshold_growth (j+1) n
    have hzlo : -(2*((j+1:Nat):Int)+3)≤W (j+1) z := by
      by_cases h : -(2*((j+1:Nat):Int)+3)≤W (j+1) z
      · exact h
      · have hh:=Int.mul_lt_mul_of_pos_left (show W (j+1) z< -(2*((j+1:Nat):Int)+3) by omega) hpos
        rw [Int.mul_neg] at hh
        omega
    have hzneg : W (j+1) z<0 := by rw [hzW]; omega
    have hzband : Band (j+1) z := by
      have hp:=p_ge j
      have hl:=l_add (j+1)
      have hn:=l_add (j+2)
      rw [p_succ] at hl
      rw [show j+2=(j+1)+1 by omega,p_succ,p_succ] at hn
      unfold W at hzlo hzneg
      rw [p_succ] at hzlo hzneg
      unfold Band
      omega
    have htail := ih hzband hw'
    have hout : UpRun j (n+1) x (T ((j+1)+n)) := .head hreg htail
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hout

theorem terminal_up_iff {j n x : Nat} (hx : Band j x) :
    UpRun j n x (T (j+n)) ↔ (3^n:Int)*W j x= -(2*((j+n:Nat):Int)+3) := by
  constructor
  · intro h; have hh:=up_run_w h; rw [w_terminal] at hh; exact hh.symm
  · exact terminal_up_of_w hx

/-- The endpoint exponent is unique: after at most one negative phase the
    trajectory must either halt or escape the sector. -/
theorem terminal_up_unique {j n m x : Nat}
    (hn : UpRun j n x (T (j+n))) (hm : UpRun j m x (T (j+m))) : n=m := by
  have hnW := (terminal_up_iff (up_run_bands hn).1).mp hn
  have hmW := (terminal_up_iff (up_run_bands hm).1).mp hm
  have aux : ∀ a b : Nat, a<b →
      (3^a:Int)*W j x= -(2*((j+a:Nat):Int)+3) →
      (3^b:Int)*W j x= -(2*((j+b:Nat):Int)+3) → False := by
    intro a b hab ha hb
    obtain ⟨k,hk⟩ : ∃ k : Nat, b=a+(k+1) := ⟨b-a-1,by omega⟩
    subst b
    rw [Int.pow_add,Int.mul_comm (3^a:Int),Int.mul_assoc,ha,Int.mul_neg] at hb
    have hh : (2*(((j+a)+(k+1):Nat):Int)+3)<(3^(k+1):Int)*(2*((j+a:Nat):Int)+3) := by exact_mod_cast threshold_growth_strict (j+a) k
    omega
  by_cases hne : n=m
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with h|h
    · exact False.elim (aux n m h hnW hmW)
    · exact False.elim (aux m n h hmW hnW)

#print axioms terminal_up_iff
#print axioms terminal_up_unique
end CapSieve
