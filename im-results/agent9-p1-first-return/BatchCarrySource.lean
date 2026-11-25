import BatchCarry
import P1CarryWideSource

namespace BB6.Agent9BatchCarry
open BB6.P1CarryExact BB6.P1CarryExtinction

theorem weightSum_eq (n j : Nat) (xs : List Bool) :
    weightSum (n+3+j) xs=weightedTail n j xs := by
  induction xs generalizing j with
  | nil => rfl
  | cons b bs ih =>
    simp only [weightSum,weightedTail]
    rw [show n+3+j+1=n+3+(j+1) by omega,ih (j+1)]

/-- Exact equivalence to the previously accepted source width, with the
    compulsory first bit removed. -/
theorem width_pos_iff_center (n K : Nat) (hn : 14≤n) (hK : 0<K) (heven : n%2=0) :
    0<width K n ↔ (n+2)/2∈live (n+4) (K-1) := by
  rw [width_pos_iff K n hK,mem_live]
  constructor
  · rintro ⟨xs,hx,he⟩
    let a := expr n xs/2^K
    have heq : expr n xs=1+2^K*a := by
      have h := Nat.mod_add_div (expr n xs) (2^K)
      rw [he] at h
      exact h.symm
    have hlen : K=xs.length+1 := by omega
    have hs : (n+2)/2+weightSum (n+4) xs=2^xs.length*a := by
      rw [expr_eq,hlen,Nat.pow_succ] at heq
      rw [show n+4=n+3+1 by omega,weightSum_eq]
      have ha : (2^xs.length*2)*a=2*(2^xs.length*a) := by ac_rfl
      rw [ha] at heq
      omega
    have hi : Interior (n+4) ((n+2)/2) := by unfold Interior; omega
    have hw := walk_of_weight (n+4) ((n+2)/2) xs a hi hs
    exact ⟨a,by simpa [hlen] using hw⟩
  · rintro ⟨a,hw⟩
    obtain ⟨xs,hx,he⟩ := weight_of_walk hw
    have hlen : xs.length+1=K := by omega
    refine ⟨xs,hlen,?_⟩
    rw [show n+4=n+3+1 by omega,weightSum_eq] at he
    have hp : 2^K*a=2*(2^(K-1)*a) := by
      have heq : K=K-1+1 := by omega
      calc
        _ = 2^(K-1+1)*a := by rw [← heq]
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
    have hexpr : expr n xs=1+2^K*a := by rw [expr_eq,hp]; omega
    have hP : 1<2^K := by
      have h := Nat.pow_lt_pow_right (show 1<2 by decide) hK
      simpa using h
    rw [hexpr,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hP]

/-- A single common terminal-clock sweep excludes every missing even index
    whose horizon is positive and no greater than the source index. -/
theorem critical_reset_no_reach_batch (F L n : Nat) (hn : 14≤n) (hL : L≤n)
    (hF : n+4≤F) (hK : F≤2*n+3) (he : n%2=0) (h : n∉batch F L) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  let K := F-(n+3)
  have hk : 0<K := by dsimp [K]; omega
  have hKn : K≤n := by dsimp [K]; omega
  apply critical_reset_no_reach_of_empty_full n K hk hn hKn
  by_cases hzero : width K n=0
  · exact hzero
  · exfalso
    have hpos : 0<width K n := by omega
    have hm := (width_pos_iff_center n K hn hk he).mp hpos
    have hlen : K-1=F-(n+4) := by dsimp [K]; omega
    rw [hlen] at hm
    exact h ((mem_batch F L n (by omega)).mpr ⟨hL,hF,he,hm⟩)

/-- An empty filtered hit list yields a whole closed even-index interval. -/
theorem critical_reset_no_reach_interval (F L R : Nat)
    (hL : 14≤L) (hF : R+4≤F) (hK : F≤2*L+3)
    (hEmpty : (batch F L).filter (·≤R)=[]) :
    ∀ n, L≤n → n≤R → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n hlo hhi he
  apply critical_reset_no_reach_batch F L n (by omega) hlo (by omega) (by omega) he
  intro hm
  have hf : n∈(batch F L).filter (·≤R) := List.mem_filter.mpr ⟨hm,by simpa using hhi⟩
  rw [hEmpty] at hf
  exact List.not_mem_nil hf

#print axioms width_pos_iff_center
#print axioms critical_reset_no_reach_batch
#print axioms critical_reset_no_reach_interval
end BB6.Agent9BatchCarry
