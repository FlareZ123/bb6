import ReverseCertificate
import Mass

namespace CascadeSource

set_option maxHeartbeats 30000

/-- Every enumerated reverse edge is a genuine original source-C episode. -/
theorem edge_sound {x p : Nat × Nat}
    (hp : p ∈ preimageEdges x.1 x.2) :
    Cstep p.1 p.2 = some x := by
  have hh := (List.mem_filter.mp hp).2
  have hd : decide (Cstep p.1 p.2=some (x.1,x.2))=true := by
    cases hwb : wellBool p.1 p.2 <;> simpa [hwb] using hh
  exact of_decide_eq_true hd

/-- Once a finite reverse closure is certified, extending its fuel cannot
    invalidate the certificate. -/
theorem reverseCert_succ : ∀ n x, reverseCert n x=true →
    reverseCert (n+1) x=true := by
  intro n
  induction n with
  | zero => intro x h; simp [reverseCert] at h
  | succ n ih =>
      intro x h
      have hne : x ≠ (2,0) := by
        intro hx
        subst x
        simp [reverseCert] at h
      have hall : (preimageEdges x.1 x.2).all (reverseCert n)=true := by
        simpa [reverseCert,hne] using h
      have hall' : (preimageEdges x.1 x.2).all (reverseCert (n+1))=true := by
        apply List.all_eq_true.mpr
        intro y hy
        exact ih y ((List.all_eq_true.mp hall) y hy)
      simpa [reverseCert,hne] using hall'

theorem reverseCert_mono (n k : Nat) (x : Nat × Nat)
    (h : reverseCert n x=true) : reverseCert (n+k) x=true := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact reverseCert_succ (n+k) x ih

/-- The reverse certificate is also complete, with the explicit global
    weighted-mass fuel bound. Every actual predecessor has strictly lower
    mass and every finite predecessor is included by the verified generator. -/
theorem reverseCert_complete (x : Nat × Nat)
    (hnot : ¬CascadeSweep.ReachC (2,0) x) :
    reverseCert (mass x+1) x = true := by
  generalize hm : mass x = n
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
      have hne : x ≠ (2,0) := by
        intro hx
        subst x
        exact hnot (CascadeSweep.ReachC.refl (2,0))
      have hall : (preimageEdges x.1 x.2).all (reverseCert n) = true := by
        apply List.all_eq_true.mpr
        intro p hp
        have he := edge_sound hp
        have hmass : mass p < mass x := by
          rcases p with ⟨a,b⟩
          rcases x with ⟨u,v⟩
          exact Cstep_mass_strict a b u v he
        have hn : mass p<n := by omega
        have hnotp : ¬CascadeSweep.ReachC (2,0) p := by
          intro hr
          exact hnot (CascadeSweep.ReachC.push hr he)
        have hc : reverseCert (mass p+1) p=true :=
          ih (mass p) hn p hnotp rfl
        have hle : mass p+1≤n := by omega
        obtain ⟨k,hk⟩ : ∃k, n=mass p+1+k :=
          ⟨n-(mass p+1),by omega⟩
        rw [hk]
        exact reverseCert_mono (mass p+1) k p hc
      simpa [reverseCert,hne] using hall

/-- Complete yes/no decision procedure for finite source-C targets from the
    authentic post-initial root. This theorem makes no assertion that the
    infinite list of fatal heights is decidable uniformly. -/
theorem reverseCert_iff_unreachable (x : Nat × Nat) :
    reverseCert (mass x+1) x=true ↔
      ¬CascadeSweep.ReachC (2,0) x := by
  constructor
  · exact reverseCert_sound x (mass x+1)
  · exact reverseCert_complete x

#print axioms edge_sound
#print axioms reverseCert_succ
#print axioms reverseCert_complete
#print axioms reverseCert_iff_unreachable

end CascadeSource
