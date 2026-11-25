import FastAuditWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10CachedAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent10ZipAudit BB6.Agent10ExactAuditWeight

/-- A successful run cannot have queried an unspecified transition.  Thus
assigning that transition preserves every previously certified prefix. -/
theorem step_refine_hole {p : PartialMachine} {s : Slot} (hhole : p s = none)
    (tr : Transition) (a b : Z) (h : step p a = some b) :
    step (refine p s tr) a = some b := by
  have hn : (a.q,a.l.headD false) ≠ s := by
    intro he
    simp [step,he,hhole] at h
  simpa only [step,refine,if_neg hn] using h

theorem run_refine_hole {p : PartialMachine} {s : Slot} (hhole : p s = none)
    (tr : Transition) (n : Nat) (a b : Z) (h : zrun p n a = some b) :
    zrun (refine p s tr) n a = some b := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    cases he : step p a with
    | none => simp [zrun,he] at h
    | some c =>
      have ht : zrun p n c = some b := by simpa [zrun,he] using h
      simp only [zrun,step_refine_hole hhole tr a c he,Option.bind_some]
      exact ih c ht

structure Cursor where
  t : Nat
  z : Z

def Cursor.Valid (p : PartialMachine) (c : Cursor) : Prop :=
  zrun p c.t start = some c.z

def rootCursor : Cursor := ⟨0,start⟩

def runAt (p : PartialMachine) (c : Cursor) (n : Nat) : Option Z :=
  if c.t ≤ n then zrun p (n-c.t) c.z else zrun p n start

theorem runAt_eq (p : PartialMachine) (c : Cursor) (n : Nat)
    (hc : c.Valid p) : runAt p c n = zrun p n start := by
  unfold runAt
  split
  · have hr := zrun_add p c.t (n-c.t) start
    rw [hc] at hr
    simp only [Option.bind_some] at hr
    rw [show c.t + (n-c.t) = n by omega] at hr
    exact hr.symm
  · rfl

def queryAt (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) && (decide (p s = none) && fastWeight B p n s)

theorem queryAt_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z)
    (hz : zrun p n start = some z) : queryAt B p n s = zipQueryOK B p n s := by
  simp [queryAt,zipQueryOK,zipRead,hz,fastWeight_eq]

def cycleAt (p : PartialMachine) (c : Cursor) (entry period : Nat) (right : Bool) (boundary : Int) : Bool :=
  match runAt p c entry with
  | none => false
  | some z => match zipWindow p right boundary period z with
    | none => false
    | some d => zipTailEq right boundary z d

theorem cycleAt_eq (p : PartialMachine) (c : Cursor) (e k : Nat) (r : Bool) (b : Int)
    (hc : c.Valid p) : cycleAt p c e k r b = zipCycle p e k r b := by
  unfold cycleAt zipCycle
  rw [runAt_eq _ _ _ hc]

/-- Every ordinary child inherits the concrete configuration immediately
before its parent's first missing instruction. Prefix work is shared rather
than replayed from blank at every descendant query. -/
def cachedCheck (B : Nat) (p : PartialMachine) (c : Cursor) : (t : Audit) → Bool
  | .last n s =>
    match runAt p c n with
    | none => false
    | some z => queryAt B p n s z && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleAt p c e k r b
  | .far rev _ cert => cert.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids =>
    match runAt p c n with
    | none => false
    | some z =>
      queryAt B p n s z &&
      allMoves (fun mv => cachedCheck B (refine p s (some mv)) ⟨n,z⟩ (kids mv))
termination_by structural t => t

theorem cachedCheck_eq (B : Nat) (p : PartialMachine) (c : Cursor) (t : Audit)
    (hc : c.Valid p) : cachedCheck B p c t = zipCheck B p t := by
  induction t generalizing p c with
  | last n s =>
    simp only [cachedCheck,zipCheck,runAt_eq _ _ _ hc]
    cases hz : zrun p n start with
    | none => simp [zipQueryOK,zipRead,hz]
    | some z => rw [queryAt_eq _ _ _ _ _ hz]
  | cycle e k r b =>
    simp only [cachedCheck,zipCheck,cycleAt_eq _ _ _ _ _ _ hc]
  | far rev d cert => rfl
  | proven q safe => rfl
  | split n s kids ih =>
    simp only [cachedCheck,zipCheck,runAt_eq _ _ _ hc]
    cases hz : zrun p n start with
    | none => simp [zipQueryOK,zipRead,hz]
    | some z =>
      rw [queryAt_eq _ _ _ _ _ hz]
      cases hq : zipQueryOK B p n s with
      | false => simp
      | true =>
        have hh := (zipQueryOK_sound hq).2.1
        have he : (fun mv => cachedCheck B (refine p s (some mv)) ⟨n,z⟩ (kids mv)) =
            (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) := by
          funext mv
          exact ih mv _ _ (run_refine_hole hh (some mv) n start z hz)
        simp [he]

theorem root_check_eq (B : Nat) (p : PartialMachine) (t : Audit) :
    cachedCheck B p rootCursor t = zipCheck B p t :=
  cachedCheck_eq B p rootCursor t rfl

#print axioms run_refine_hole
#print axioms cachedCheck_eq
#print axioms root_check_eq
end BB6.Agent10CachedAudit
