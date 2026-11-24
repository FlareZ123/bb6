import SmallSeed

namespace BB6.Agent9Renewal
open BB6P1Unit
set_option maxHeartbeats 2000000

/-- Sufficient explicit threshold for a polynomial seed, for h blocks.
The seed may stay in the zero phase or enter the nonzero renewal grid. -/
def smallMarginThreshold (B C p : Nat) : Nat := coefficientThreshold (4*(C+8)*B) (p+1)

def smallThreshold : Nat → Nat → Nat → Nat → Nat
  | 0,B,C,p => smallMarginThreshold B C p
  | h+1,B,C,p => max (smallMarginThreshold B C p)
      (max (smallThreshold h (C*B) C (p+1)) (manyThreshold h firstGrid (C*B) C (p+1)))

theorem smallThreshold_margin (h B C p : Nat) : smallMarginThreshold B C p≤smallThreshold h B C p := by
  cases h with
  | zero => exact Nat.le_refl _
  | succ h => exact Nat.le_max_left _ _

theorem small_seed_margin (n d s B C p : Nat) (hn : 1≤n)
    (hd : d≤B*n^p) (hs : s≤C*n) (hdom : smallMarginThreshold B C p≤n) :
    4*(s+8)*d<7*2^n := by
  have hsn : s+8≤(C+8)*n := by
    rw [Nat.add_mul]
    omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hsn) hd
  have he : 4*((C+8)*n)*(B*n^p)=4*(C+8)*B*n^(p+1) := by rw [Nat.pow_succ]; ac_rfl
  rw [he] at hmul
  have hdom' := coefficient_dom (4*(C+8)*B) (p+1) n hdom
  omega

/-- Every polynomial-size positive seed (including a zero mod-seven phase)
remains uniformly away from both endpoints over every fixed linear time
range before the critical clock. The threshold depends only on the four
integer envelope parameters, not on the actual seed or orbit. -/
theorem small_seed_safe (h B C p n q d s m : Nat)
    (hn : 1≤n) (hB : 0<B) (hC : 0<C) (hp : 1≤p) (hhC : h≤C)
    (hdom : smallThreshold h B C p≤n) (hclock : q+s=7*2^n)
    (hd : 2≤d) (hdB : d≤B*n^p) (hs : s≤C*n)
    (hm : m≤h*n) (hsm : m+2≤s) :
    2≤run q d m ∧ run q d m+8≤q+m := by
  induction h generalizing B p q d s m with
  | zero =>
    have hsmall := small_seed_margin n d s B C p hn hdB hs hdom
    obtain ⟨_,_,_,_,_,_,_,_,hlo,hhi⟩ := small_grid_prefix n q d s m hclock hd (by omega) hsm hsmall
    exact ⟨hlo,hhi⟩
  | succ h ih =>
    have hsmall := small_seed_margin n d s B C p hn hdB hs (Nat.le_trans (smallThreshold_margin _ _ _ _) hdom)
    by_cases hle : m≤n
    · obtain ⟨_,_,_,_,_,_,_,_,hlo,hhi⟩ := small_grid_prefix n q d s m hclock hd hle hsm hsmall
      exact ⟨hlo,hhi⟩
    · obtain ⟨E,hE,hend,hlo,hhi⟩ := small_grid_end n q d s hclock hd (by omega) hsmall
      let q' := q+n
      let d' := run q d n
      let s' := s-n
      let m' := m-n
      have hclock' : q'+s'=7*2^n := by dsimp [q',s']; omega
      have hB' : 0<C*B := Nat.mul_pos hC hB
      have hE' : E≤(C*B)*n^(p+1) := by
        have hmul := Nat.mul_le_mul hs hdB
        have he : C*n*(B*n^p)=(C*B)*n^(p+1) := by rw [Nat.pow_succ]; ac_rfl
        rw [he] at hmul
        omega
      have hm' : m'≤h*n := by dsimp [m']; rw [Nat.add_mul,Nat.one_mul] at hm; omega
      have hsm' : m'+2≤s' := by dsimp [m',s']; omega
      have hs' : s'≤C*n := by dsimp [s']; omega
      have hsplit : n+m'=m := by dsimp [m']; omega
      have hdom' : max (smallThreshold h (C*B) C (p+1)) (manyThreshold h firstGrid (C*B) C (p+1))≤n := Nat.le_trans (Nat.le_max_right _ _) hdom
      by_cases hz : d%7=0
      · have hd' : d'≤(C*B)*n^(p+1) := by dsimp [d']; rw [hend,hz,Nat.mul_zero,Nat.zero_add]; exact hE'
        have hr := ih (C*B) (p+1) q' d' s' m' hB' (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hdom') hclock' hlo hd' hs' hm' hsm'
        rw [←hsplit,run_add]
        simpa [q',d',Nat.add_assoc] using hr
      · have hclockI : (q':Int)=7*(2:Int)^n-(s':Int) := by
          have hh : (q':Int)+(s':Int)=7*(2:Int)^n := by exact_mod_cast hclock'
          omega
        have ha : ∀ j : Nat, j≤h*n → Bound (-(s':Int)+j) ((C:Int)*n) := by
          intro j hj
          have hcn := Nat.mul_le_mul_right n (show h≤C by omega)
          have hjC : j≤C*n := by omega
          have hjI : (j:Int)≤(C:Int)*n := by exact_mod_cast hjC
          have hsI : (s':Int)≤(C:Int)*n := by exact_mod_cast hs'
          unfold Bound
          omega
        have hinit : Bound (firstGrid.D*(d':Int)-7*(2:Int)^n*((d%7:Nat):Int)) (firstGrid.D*(((C*B:Nat):Int)*(n:Int)^(p+1))) := by
          have hh : (d':Int)=(2:Int)^n*((d%7:Nat):Int)+(E:Int) := by exact_mod_cast hend
          have hE'I : (E:Int)≤((C*B:Nat):Int)*(n:Int)^(p+1) := by exact_mod_cast hE'
          change Bound (7*(d':Int)-7*(2:Int)^n*((d%7:Nat):Int)) (7*(((C*B:Nat):Int)*(n:Int)^(p+1)))
          rw [hh,Int.mul_add,←Int.mul_assoc]
          unfold Bound
          omega
        have hp7 : (((d%7:Nat):Int)%7)≠0 := by omega
        have hpD : ((d%7:Nat):Int)<firstGrid.D := by change ((d%7:Nat):Int)<7; omega
        have hdq' : d'<q' := by dsimp [q',d']; omega
        have hr := many_blocks h firstGrid (C*B) C (p+1) firstGrid_valid hB' (by omega) n q' d' ((d%7:Nat):Int) (-(s':Int)) hn (Nat.le_trans (Nat.le_max_right _ _) hdom') (by omega) hpD hp7 hdq' (by omega) ha hinit m' (by dsimp [m']; omega) hm'
        rw [←hsplit,run_add]
        simpa [q',d',Nat.add_assoc] using hr

#print axioms small_seed_safe
end BB6.Agent9Renewal
