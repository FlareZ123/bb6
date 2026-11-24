import CanonicalAudit
import FARFrontier
namespace BB6Coverage.Canonical

/-- The true finite-support blank trace never consults an unintroduced state. -/
theorem firstUnknown_scoped (p : PartialMachine) (k n : Nat) (c : FinRayCfg)
    (hp : Scoped k p) (hc : c.state.val < k) (s : Slot)
    (h : firstUnknownPhysical p n c = some s) : s.1.val < k := by
  induction n generalizing c with
  | zero => simp [firstUnknownPhysical] at h
  | succ n ih =>
    cases ht : p (c.state,finiteTape c c.head) with
    | none =>
      have he : s = (c.state,finiteTape c c.head) := by
        simpa [firstUnknownPhysical,ht] using h.symm
      rw [he]
      exact hc
    | some t =>
      cases t with
      | none => simp [firstUnknownPhysical,ht] at h
      | some mv =>
        have hn : (finiteMove c mv).state.val < k := (hp _ _ ht).2
        exact ih (finiteMove c mv) hn (by simpa [firstUnknownPhysical,ht] using h)

/-- Genuine physical first-unknown splitting, with checked terminal oracles.
    Fuel limits only exploration of the finite transition table. -/
def search (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit : Nat) :
    (depth k : Nat) → (p : PartialMachine) → Scoped k p → (0<k ∧ k≤6) → Audit bound p k
  | depth,k,p,hp,hk =>
    if h : lassoDecisionOracle p bound rayLimit lassoLimit entryLimit macroLimit = true then
      .certified p k (lassoDecisionOracle_sound p bound rayLimit lassoLimit entryLimit macroLimit h)
    else if h : FAR.oracle p farLimit = true then
      .certified p k (.leaf p (fun m hm => Or.inl (FAR.oracle_sound p farLimit h m hm)))
    else
      match depth with
      | 0 => .unresolved p k
      | n+1 =>
        match hs : firstUnknownPhysical p scanLimit finiteBlank with
        | none => .unresolved p k
        | some s =>
          have hs' : s.1.val < k := firstUnknown_scoped p k scanLimit finiteBlank hp hk.1 s hs
          .branch p k s (firstUnknownPhysical_sound p scanLimit finiteBlank s hs) hp hs' hk
            (fun t _ => search bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit
              n (nextK k t) (refine p s t) (scoped_refine k p s t hp hs') (nextK_bounds k t hk))
termination_by depth k p hp hk => depth

def global (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat) :
    Audit bound emptyTable 1 :=
  search bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth 1 emptyTable
    (by intro s t h; simp [emptyTable] at h) (by decide)

theorem global_exhaustive (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat)
    (m : Machine) : DecidedBelow bound m ∨
      (global bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth).open m :=
  (global bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth).exhaustive m (empty_compatible m)

theorem global_conserves (bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth : Nat) :
    let a := global bound rayLimit scanLimit lassoLimit entryLimit macroLimit farLimit depth
    a.report.1+a.report.2 = 25^12 := by
  intro a
  calc
    _ = cylinderMass emptyTable := a.conserves
    _ = 25^12 := by decide

#print axioms firstUnknown_scoped
#print axioms global_exhaustive
#print axioms global_conserves
end BB6Coverage.Canonical
