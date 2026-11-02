module

public import Agent19P1Bridge
public import BlankCriterion

@[expose] public section

namespace BB6.P1Bridge

open BusyBeaver BB6.HaltingFunnel

/-- A finite locally defined halting trace implies the library's iterator halts. -/
theorem haltsIn_to_iter {n a c : Nat} (h : HaltsIn n a c) :
    ((Option.bind · nextLocal)^[n] (some (a,c))).isNone := by
  induction h with
  | now a c hnone =>
      change ((Option.bind · nextLocal)^[1] (some (a,c))).isNone
      rw [Function.iterate_succ_apply]
      simp [nextLocal, hnone]
  | next n a c b d hnext _ ih =>
      rw [Function.iterate_succ_apply]
      simpa [nextLocal, hnext] using ih

/-- Conversely, every stopping iteration has a finite HaltsIn certificate. -/
theorem iter_to_halts (n : Nat) (a c : Nat)
    (h : ((Option.bind · nextLocal)^[n] (some (a,c))).isNone) :
    ∃ m, HaltsIn m a c := by
  induction n generalizing a c with
  | zero => simp at h
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      rcases ht : T a c with _ | ⟨b,d⟩
      · exact ⟨1, HaltsIn.now a c ht⟩
      · have hs : ((Option.bind · nextLocal)^[n] (some (b,d))).isNone := by
          simpa [nextLocal, ht] using h
        obtain ⟨m,hm⟩ := ih b d hs
        exact ⟨m+1, HaltsIn.next m a c b d ht hm⟩

/-- The earlier finite trace predicate agrees with Cryptids' CollatzHalts. -/
theorem local_halts_iff :
    CollatzHalts nextLocal (2,1) ↔ ∃ m, HaltsIn m 2 1 := by
  unfold CollatzHalts
  constructor
  · rintro ⟨n,hn⟩
    exact iter_to_halts n 2 1 hn
  · rintro ⟨m,hm⟩
    exact ⟨m,haltsIn_to_iter hm⟩

/-- Kernel-level entire proof chain: the original blank-tape machine halts
    exactly when the local accelerated trajectory hits a sparse critical gate. -/
theorem raw_halts_iff_sparse_gate :
    IsHalt Source.target ↔
    ∃ n, ReachT 2 1 2 (14*2^n-2*n-10) := by
  exact raw_halts_iff.trans (local_halts_iff.trans blank_halts_iff_closed)

#print axioms haltsIn_to_iter
#print axioms iter_to_halts
#print axioms local_halts_iff
#print axioms raw_halts_iff_sparse_gate

end BB6.P1Bridge
