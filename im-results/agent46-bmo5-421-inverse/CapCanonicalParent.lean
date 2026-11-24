import CapResetInverse

namespace CapSieve

def resetParent (b v : Nat) : Option (Nat × Nat) :=
  let n := (strip3 v).1
  let w := (strip3 v).2
  let k := b-n
  if w%3=2^k%3 then some (k,rayParent k ((w+3)/2))
  else none

theorem negative_entry_exit {k w : Nat} (hv : CapNegative.Valid k w)
    (hphase : w%3=2^k%3) :
    ExitP k ((w+3)/2) ∧ (w+3)/2<k+7 ∧ 2*((w+3)/2)-3=w := by
  have he : 2*((w+3)/2)=w+3 := by unfold CapNegative.Valid at hv; omega
  have hp := p_ge (k+1)
  have hpar := hv.2.2
  have hlo := hv.1
  have hhi := hv.2.1
  unfold ExitP
  rw [Nat.pow_succ]
  omega

theorem reset_parent_sound {b v j q k u : Nat} (hb : 3≤b)
    (hf : FinalReturn b v j q) (he : resetParent b v=some (k,u)) :
    CanonQ k u ∧ (signedEvent k u).2=some (j,q) := by
  have hs := strip3_spec hf.1.1
  have hlt := strip_below_band hb hf.1
  unfold resetParent at he
  dsimp at he
  split at he
  next hphase =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
    let n := (strip3 v).1
    let w := (strip3 v).2
    let k := b-n
    change w%3=2^k%3 at hphase
    have hk : 1≤k := by dsimp [k,n]; omega
    have hkb : k+n=b := by dsimp [k,n]; omega
    have hvw : v=3^n*w := hs.2.2
    have hfin : FinalReturn (k+n) (3^n*w) j q := by rw [hkb,←hvw]; exact hf
    have hval := negative_unscale_valid hfin.1
    obtain ⟨hp,hfail,hw⟩ := negative_entry_exit hval hphase
    obtain ⟨hc,hnext⟩ := ray_parent_spec hk hp
    change CanonQ k (rayParent k ((w+3)/2)) ∧
      (signedEvent k (rayParent k ((w+3)/2))).2=some (j,q)
    refine ⟨hc,?_⟩
    unfold signedEvent
    rw [if_pos hc.1.2.1]
    dsimp
    rw [hnext,if_neg (by omega : ¬k+7≤(w+3)/2),hw]
    exact negative_final_event hk hfin
  next h => contradiction

theorem reset_parent_complete {k u j q : Nat} (hc : CanonQ k u)
    (hfail : positiveNext k u<k+7)
    (he : (CapNegative.event k (2*positiveNext k u-3)).2=some (j,q))
    (hj : 5≤j) :
    ∃ b v, resetFinal j q=some (b,v) ∧ resetParent b v=some (k,u) := by
  let w := 2*positiveNext k u-3
  let n := CapNegative.stopCount k w
  let b := k+n
  let v := 3^n*w
  have hw := entry_weight hc.1 hfail
  have hfin : FinalReturn b v j q := negative_event_final hw.1 he
  have hphase : w%3=2^k%3 := hw.2
  have hunit : w%3≠0 := by rw [hphase]; rcases two_unit_phase k with h|h <;> omega
  have hstrip : strip3 v=(n,w) := strip3_unique hunit rfl
  have hb : 3≤b := by rcases hfin.2 with h|h <;> omega
  have hlt := strip_below_band hb hfin.1
  rw [hstrip] at hlt
  have hk : 1≤k := by dsimp [b] at hlt; omega
  have hbsub : b-n=k := by dsimp [b]; omega
  refine ⟨b,v,final_return_reset hfin,?_⟩
  unfold resetParent
  rw [hstrip]
  dsimp
  rw [hbsub,if_pos hphase]
  have hplo := (positive_next_bounds (show 0<u by have := hc.1.1; omega) hc.1.2.1).1
  have hw' : (w+3)/2=positiveNext k u := by dsimp [w]; omega
  rw [hw',ray_parent_inverse hk hc]

theorem negative_event_div3 {k w j q : Nat} (hv : CapNegative.Valid k w)
    (he : (CapNegative.event k w).2=some (j,q)) : q%3=0 :=
  final_return_div3 (negative_event_final hv he)

/-- Exact inverse of the signed positive-return macro in the high bands. -/
def canonicalParent (j q : Nat) : Option (Nat × Nat) :=
  if q%3=2^j%3 then some (j-1,rayParent (j-1) q)
  else match resetFinal j q with
       | none => none
       | some (b,v) => resetParent b v

theorem canonical_parent_sound {j q k u : Nat} (hj : 5≤j) (hq : CanonQ j q)
    (he : canonicalParent j q=some (k,u)) :
    CanonQ k u ∧ (signedEvent k u).2=some (j,q) := by
  unfold canonicalParent at he
  split at he
  next hphase =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
    exact regular_parent_exact (by omega) hq.1 hphase
  next hn =>
    cases hf : resetFinal j q with
    | none => rw [hf] at he; contradiction
    | some z =>
      obtain ⟨b,v⟩ := z
      rw [hf] at he
      obtain ⟨hb,hfin⟩ := reset_final_sound hj hq.1 hf
      exact reset_parent_sound hb hfin he

theorem canonical_parent_complete {k u j q : Nat} (hj : 5≤j) (hc : CanonQ k u)
    (he : (signedEvent k u).2=some (j,q)) :
    canonicalParent j q=some (k,u) := by
  unfold signedEvent at he
  rw [if_pos hc.1.2.1] at he
  dsimp at he
  by_cases hpass : k+7≤positiveNext k u
  · rw [if_pos hpass] at he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
    have hphase := positive_next_phase hc.1
    unfold canonicalParent
    rw [if_pos hphase,show k+1-1=k by omega,ray_parent_inverse (by omega) hc]
  · rw [if_neg hpass] at he
    have hfail : positiveNext k u<k+7 := by omega
    have hw := entry_weight hc.1 hfail
    have hqdiv := negative_event_div3 hw.1 he
    have hphase : q%3≠2^j%3 := by rw [hqdiv]; rcases two_unit_phase j with h|h <;> omega
    obtain ⟨b,v,hf,hp⟩ := reset_parent_complete hc hfail he hj
    unfold canonicalParent
    rw [if_neg hphase,hf]
    exact hp

theorem canonical_parent_iff {j q k u : Nat} (hj : 5≤j) (hq : CanonQ j q) :
    canonicalParent j q=some (k,u) ↔
      CanonQ k u ∧ (signedEvent k u).2=some (j,q) :=
  ⟨canonical_parent_sound hj hq,fun ⟨hc,he⟩ => canonical_parent_complete hj hc he⟩

#print axioms reset_parent_sound
#print axioms reset_parent_complete
#print axioms canonical_parent_iff
end CapSieve
