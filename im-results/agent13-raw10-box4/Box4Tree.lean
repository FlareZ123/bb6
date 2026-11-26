import Box4Lower
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box4
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 (tableEq tableEq_sound haltBound haltBound_sound slot decode)
open BB6Coverage.Agent10ZipAudit

structure Known (target : Fin 12) where
  p : PartialMachine
  good : Good target p

inductive Witness where
  | short (n : Nat)
  | exact (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | known (i : Nat)
  deriving Inhabited

inductive Tree where
  | leaf (w : Witness)
  | branch (s : Fin 12) (kids : List (Fin 25 × Tree))
  deriving Inhabited

def checkLeaf {target : Fin 12} (known : Array (Known target))
    (p : PartialMachine) : Witness → Bool
  | .short n => zipHalt p n && decide (n+6 ≤ 3640)
  | .exact n => haltBound p n 3640
  | .cycle entry period right boundary =>
      decide (0<period) && zipCycle p entry period right boundary
  | .known i => match known[i]? with | some v => tableEq p v.p | none => false

theorem checkLeaf_sound {target : Fin 12} (known : Array (Known target))
    (p : PartialMachine) (w : Witness) (h : checkLeaf known p w = true) :
    Good target p := by
  cases w with
  | short n =>
    simp only [checkLeaf,Bool.and_eq_true] at h
    exact good_short target p n h.1 (of_decide_eq_true h.2)
  | exact n => exact good_halt target p n h
  | cycle entry period right boundary =>
    simp only [checkLeaf,Bool.and_eq_true] at h
    exact good_cycle target p entry period right boundary (of_decide_eq_true h.1) h.2
  | known i =>
    cases he : known[i]? with
    | none => simp [checkLeaf,he] at h
    | some q =>
      have hp := tableEq_sound p q.p (by simpa [checkLeaf,he] using h)
      exact hp.symm ▸ q.good

def audit {target : Fin 12} (known : Array (Known target)) : Nat → PartialMachine → Tree → Bool
  | _,p,.leaf w => checkLeaf known p w
  | 0,_,.branch _ _ => false
  | fuel+1,p,.branch s kids =>
    (kids.map Prod.fst == sliceDomain target s) &&
      kids.all (fun (v,t) => audit known fuel (refine p (slot s) (decode v)) t)

theorem audit_sound {target : Fin 12} (known : Array (Known target))
    (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : audit known fuel p t = true) : Good target p := by
  induction fuel generalizing p t with
  | zero =>
    cases t with
    | leaf w => exact checkLeaf_sound known p w h
    | branch s kids => simp [audit] at h
  | succ fuel ih =>
    cases t with
    | leaf w => exact checkLeaf_sound known p w h
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply good_split target p s
      intro v hv
      rw [← h.1] at hv
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hv
      dsimp at hw
      subst w
      exact ih _ u (List.all_eq_true.mp h.2 (v,u) hmem)

/-- A proven subtree can be reused as one known leaf in its parent.
    All table equality and completeness checks remain inside the kernel. -/
def certified {target : Fin 12} (known : Array (Known target)) (p : PartialMachine)
    (t : Tree) (h : audit known 12 p t = true) : Known target :=
  ⟨p,audit_sound known 12 p t h⟩

#print axioms audit_sound
end BB6.Agent13.Box4
