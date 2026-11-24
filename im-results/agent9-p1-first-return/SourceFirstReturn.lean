import OddConeMass
import InverseIff
import FirstReturn

/-! Exact source-to-scalar equivalence for P1 odd inverse histories. -/
namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6.Agent47P1

/-- Source transport preserves both the scalar right counter and the exact mass. -/
theorem gap_of_oddcone (b0 Q b d m : Nat) (hroot : b0+10=2*Q)
    (h : OddCone b0 3 b d m) :
    ∃ v, d=2*v+1 ∧ b+2*v+2*m+8=2*Q ∧ Gap Q m v := by
  induction h with
  | root => exact ⟨1, rfl, by omega, Gap.root⟩
  | parent b d m t k c hp hb hb4 hd hi hk hc ih =>
    obtain ⟨p, hdp, hmass, hgap⟩ := ih
    let v := (c+3)/2
    have hcv : c+3=2*v := by dsimp [v]; omega
    have hv : 2≤v := by dsimp [v]; omega
    have hpower := ((inverseAt_iff_power_mass b d t k c (by omega) hb4 hd).mp hi).1
    have hpow : 2^(t+1)*v=2^t*(c+3) := by
      rw [hcv, Nat.pow_succ]; ac_rfl
    have he : p+(Q-m)=2^(t+1)*v := by rw [hpow, ←hpower]; omega
    have hnew := odd_cone_mass b0 3 (2*k-4) (c+4) (m+t+1)
      (OddCone.parent b d m t k c hp hb hb4 hd hi hk hc)
    have hg := Gap.edge m p (t+1) v hgap (by omega) (by omega) hv (by omega) he
    exact ⟨v,by omega,by omega,by simpa [Nat.add_assoc] using hg⟩

/-- Conversely, every guarded scalar gap lifts to the original inverseAt relation. -/
theorem oddcone_of_gap (b0 Q m v : Nat) (hroot : b0+10=2*Q)
    (h : Gap Q m v) :
    ∃ b, b+2*v+2*m+8=2*Q ∧ OddCone b0 3 b (2*v+1) m := by
  induction h with
  | root => exact ⟨b0,by omega,OddCone.root⟩
  | edge m p k d hp hk hsize hd hchild he ih =>
    obtain ⟨b,hbalance,hcone⟩ := ih
    let t := k-1
    let c := 2*d-3
    let s := Q-(m+k)-d-2
    have htk : t+1=k := by dsimp [t]; omega
    have hc : c%2=1 := by dsimp [c]; omega
    have hsc : 2≤s := by dsimp [s]; omega
    have hb : 8≤b := by omega
    have hpow : 2^k*d=2*(2^t*d) := by rw [←htk, Nat.pow_succ]; ac_rfl
    have hb4 : b%4=0 := by rw [hpow] at he; omega
    have hdp : (2*p+1)%2=1 := by omega
    have hpc : 2^t*(c+3)=2^k*d := by
      rw [show c+3=2*d by dsimp [c]; omega, ←htk, Nat.pow_succ]
      ac_rfl
    have hip : (2*p+1)+b/2+3=2^t*(c+3) := by rw [hpc, ←he]; omega
    have him : 2*s+c+2*t+1+c%2=b+(2*p+1) := by dsimp [s,c,t]; omega
    have hi := (inverseAt_iff_power_mass b (2*p+1) t s c (by omega) hb4 hdp).mpr ⟨hip,him⟩
    have hnext := OddCone.parent b (2*p+1) m t s c hcone hb hb4 hdp hi hsc hc
    refine ⟨2*s-4, by dsimp [s]; omega, ?_⟩
    rw [show 2*d+1=c+4 by dsimp [c]; omega, show m+k=m+t+1 by omega]
    exact hnext

theorem source_right_five_iff (b0 Q : Nat) (hroot : b0+10=2*Q) :
    (∃ b m, OddCone b0 3 b 5 m) ↔
    ∃ q k, 5≤q ∧ q+k=Q ∧ FirstReturn q k ∧ Safe q 1 k := by
  rw [← right_five_iff Q]
  constructor
  · rintro ⟨b,m,h⟩
    obtain ⟨v,hd,_,hg⟩ := gap_of_oddcone b0 Q b 5 m hroot h
    have hv : v=2 := by omega
    exact ⟨m, hv ▸ hg⟩
  · rintro ⟨m,h⟩
    obtain ⟨b,_,hc⟩ := oddcone_of_gap b0 Q m 2 hroot h
    exact ⟨b,m,hc⟩

private theorem pow_dom (n : Nat) (hn : 4≤n) : n+4≤2^n := by
  have h : ∀ j : Nat, j+8≤2^(j+4) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show j+1+4=j+4+1 by omega, Nat.pow_succ]
      omega
  have hj : n-4+4=n := by omega
  have hh := h (n-4)
  rw [hj] at hh
  omega

/-- The actual critical root is represented without a mass or clock assumption. -/
theorem critical_right_five_iff (n : Nat) (hn : 14≤n) :
    (∃ b m, OddCone (14*2^n-2*n-16) 3 b 5 m) ↔
    ∃ q k, 5≤q ∧ q+k=7*2^n-n-3 ∧ FirstReturn q k ∧ Safe q 1 k := by
  have hdom := pow_dom n (by omega)
  apply source_right_five_iff
  omega

#print axioms gap_of_oddcone
#print axioms oddcone_of_gap
#print axioms source_right_five_iff
#print axioms critical_right_five_iff
end BB6.Agent9FirstReturn
