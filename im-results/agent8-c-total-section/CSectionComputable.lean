import CSectionTotal
import GenericScan
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8ComputableC
open BB6.Agent8Section BB6.Agent8Scan BB6.Agent8TotalC
open BB6.CReachBridge

/-- Primitive-recursive recognition of the zero-right-counter section. -/
def decode : S → Option (Nat × Nat)
  | (a,k,0) => some (a,k)
  | _ => none

theorem decode_sound (s : S) (y : Nat × Nat)
    (h : decode s = some y) : s = embed y := by
  rcases s with ⟨a,k,c⟩
  cases c with
  | zero =>
      simp only [decode,Option.some.injEq] at h
      subst y
      rfl
  | succ c => simp [decode] at h

theorem decode_complete (y : Nat × Nat) : decode (embed y) = some y := by
  rcases y with ⟨a,k⟩
  rfl

/-- A directly executable finite search, starting after the mandatory first
    call and bounded by Agent 21's universally proved c0 excursion budget. -/
def scan0 (p : Nat × Nat) : Option (Nat × Option (Nat × Nat)) :=
  scan BB6CLine.nextC decode (4*p.2+4) (BB6CLine.nextC (embed p))

/-- No fuel-exhaustion branch is reachable for any natural input pair. -/
theorem scan0_complete (p : Nat × Nat) :
    ∃ m y, scan0 p = some (m,y) := by
  obtain ⟨n,hlo,hhi,y,hy⟩ := bounded_exit p
  have hn : (n-1)+1=n := by omega
  have htail : run BB6CLine.nextC (n-1) (BB6CLine.nextC (embed p)) =
      y.map embed := by
    rw [←hn,run_succ_head] at hy
    simpa using hy
  have ht : ∃ z : Option (Nat × Nat),
      finish decode (run BB6CLine.nextC (n-1)
        (BB6CLine.nextC (embed p))) = some z := by
    rw [htail]
    cases y with
    | none => exact ⟨none,rfl⟩
    | some t => exact ⟨some t,by simp [finish,decode_complete]⟩
  exact scan_complete BB6CLine.nextC decode (n-1) (4*p.2+4)
    (BB6CLine.nextC (embed p)) (by omega) ht

def fastTime (p : Nat × Nat) : Nat :=
  match scan0 p with
  | some (m,_) => m+1
  | none => 1

def fastNext (p : Nat × Nat) : Option (Nat × Nat) :=
  match scan0 p with
  | some (_,y) => y
  | none => none

/-- The executable fast map consumes at least one and at most 4k+5 original
    counter steps, without requiring any unbounded search or choice. -/
theorem fastTime_bounds (p : Nat × Nat) :
    1 ≤ fastTime p ∧ fastTime p ≤ 4*p.2+5 := by
  obtain ⟨m,y,hm⟩ := scan0_complete p
  have hsound := scan_sound BB6CLine.nextC decode embed decode_sound
    (4*p.2+4) (BB6CLine.nextC (embed p)) m y hm
  simp only [fastTime,hm]
  omega

/-- The executable two-counter map is exactly a segment of the unchanged
    published counter accelerator, with the certified positive elapsed time. -/
theorem fastNext_exact (p : Nat × Nat) :
    run BB6CLine.nextC (fastTime p) (some (embed p)) =
      (fastNext p).map embed := by
  obtain ⟨m,y,hm⟩ := scan0_complete p
  obtain ⟨hbound,hsound⟩ := scan_sound BB6CLine.nextC decode embed decode_sound
    (4*p.2+4) (BB6CLine.nextC (embed p)) m y hm
  have hh : run BB6CLine.nextC (m+1) (some (embed p)) = y.map embed := by
    rw [run_succ_head]
    simpa using hsound
  simpa only [fastTime,fastNext,hm] using hh

/-- The published Machine C halt question is *exactly* eventual stopping
    of a primitive-recursive total two-counter map from (5,1). -/
theorem blank_halts_iff_computable_two_counter :
    RunHalts ↔ ∃ m, run fastNext m (some (5,1)) = none := by
  rw [blank_halts_iff_c0]
  exact section_halts_iff_of_step BB6CLine.nextC embed fastTime fastNext
    (fun p => (fastTime_bounds p).1) fastNext_exact (5,1)

/-- No intermediate positive-time state before fastTime is a c=0 return
    or a halting configuration. This proves the computed return is the first. -/
theorem fastNext_first (p : Nat × Nat) (j : Nat)
    (hpos : 1 ≤ j) (hlt : j < fastTime p) :
    finish decode (run BB6CLine.nextC j (some (embed p))) = none := by
  obtain ⟨m,y,hm⟩ := scan0_complete p
  have hmpos : j-1 < m := by
    simp only [fastTime,hm] at hlt
    omega
  have hi := scan_first BB6CLine.nextC decode (4*p.2+4)
    (BB6CLine.nextC (embed p)) m y hm (j-1) hmpos
  have htime : (j-1)+1=j := by omega
  rw [← htime,run_succ_head]
  simpa using hi

/-- Independent definitional-evaluation smoke check on the source-aligned
    first three blank-entry section returns and exact elapsed call counts. -/
theorem first_three_sections :
    fastNext (5,1) = some (3,4) ∧ fastTime (5,1) = 3 ∧
    fastNext (3,4) = some (4,7) ∧ fastTime (3,4) = 7 ∧
    fastNext (4,7) = some (20,4) ∧ fastTime (4,7) = 17 := by decide

#print axioms fastNext_first
#print axioms first_three_sections

#print axioms scan0_complete
#print axioms fastNext_exact
#print axioms blank_halts_iff_computable_two_counter
end BB6.Agent8ComputableC
