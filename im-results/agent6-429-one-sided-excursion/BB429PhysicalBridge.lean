import BB429SourceRows
import Lean.Elab.Tactic.Omega

namespace BB429PhysicalBridge
open BB6Coverage BB429PhysicalFrontier BB429OddExcursion BB429SourceRows

private def fcast (j : Nat) : Int := (j:Int) + 1

/-- The entire physical tape is represented by the two finite zipper stacks;
     all unspecified cells are blank. -/
def Represents (z : Zipper) (c : Config) : Prop :=
  c.state.val = z.state ∧
  c.tape c.head = z.current ∧
  (∀ j : Nat, c.tape (c.head - fcast j) = z.left.getD j false) ∧
  (∀ j : Nat, c.tape (c.head + fcast j) = z.right.getD j false)

private theorem getD_tail (xs : List Bool) (j : Nat) :
    xs.tail.getD j false = xs.getD (j+1) false := by
  cases xs <;> rfl

private theorem headD_getD (xs : List Bool) :
    xs.headD false = xs.getD 0 false := by
  cases xs <;> rfl

def zipperLeft (z : Zipper) (s : Fin 6) (w : Bool) : Zipper :=
  BB429OddExcursion.z s.val z.left.tail (z.left.headD false) (w::z.right)

def zipperRight (z : Zipper) (s : Fin 6) (w : Bool) : Zipper :=
  BB429OddExcursion.z s.val (w::z.left) (z.right.headD false) z.right.tail

theorem rightRep (z : Zipper) (c : Config) (s : Fin 6) (w : Bool)
    (h : Represents z c) :
    Represents (zipperRight z s w)
      (applyMove c ⟨w,true,s⟩) := by
  rcases h with ⟨hstate,hcur,hl,hr⟩
  unfold Represents zipperRight
  refine ⟨by rfl, ?_, ?_, ?_⟩
  · change (if c.head+1=c.head then w else c.tape (c.head+1)) = z.right.headD false
    have hneq : c.head+1 ≠ c.head := by omega
    rw [if_neg hneq,headD_getD]
    simpa [fcast] using hr 0
  · intro j
    cases j with
    | zero =>
        change (if c.head+1-(↑(0:Nat)+1)=c.head then w else
          c.tape (c.head+1-(↑(0:Nat)+1))) = w
        have hh : c.head+1-(↑(0:Nat)+1)=c.head := by omega
        rw [hh];simp
    | succ j =>
        change (if c.head+1- (↑(j+1:Nat)+1) = c.head then w else
          c.tape (c.head+1-(↑(j+1:Nat)+1))) = z.left.getD j false
        have hh : c.head+1-(↑(j+1:Nat)+1)=c.head-fcast j := by simp [fcast];omega
        rw [hh]
        have hn : c.head-fcast j ≠ c.head := by simp [fcast];omega
        rw [if_neg hn]
        exact hl j
  · intro j
    change (if c.head+1+fcast j=c.head then w else
        c.tape (c.head+1+fcast j)) = z.right.tail.getD j false
    have hh : c.head+1+fcast j=c.head+fcast (j+1) := by simp [fcast];omega
    rw [hh]
    have hn : c.head+fcast (j+1) ≠ c.head := by simp [fcast];omega
    rw [if_neg hn,getD_tail]
    exact hr (j+1)

theorem leftRep (z : Zipper) (c : Config) (s : Fin 6) (w : Bool)
    (h : Represents z c) :
    Represents (zipperLeft z s w)
      (applyMove c ⟨w,false,s⟩) := by
  rcases h with ⟨hstate,hcur,hl,hr⟩
  unfold Represents zipperLeft
  refine ⟨by rfl, ?_, ?_, ?_⟩
  · change (if c.head-1=c.head then w else c.tape (c.head-1)) = z.left.headD false
    have hneq : c.head-1 ≠ c.head := by omega
    rw [if_neg hneq,headD_getD]
    simpa [fcast] using hl 0
  · intro j
    change (if c.head-1-fcast j=c.head then w else
        c.tape (c.head-1-fcast j)) = z.left.tail.getD j false
    have hh : c.head-1-fcast j=c.head-fcast (j+1) := by simp [fcast];omega
    rw [hh]
    have hn : c.head-fcast (j+1) ≠ c.head := by simp [fcast];omega
    rw [if_neg hn,getD_tail]
    exact hl (j+1)
  · intro j
    cases j with
    | zero =>
        change (if c.head-1+(↑(0:Nat)+1)=c.head then w else
            c.tape (c.head-1+(↑(0:Nat)+1))) = w
        have hh : c.head-1+(↑(0:Nat)+1)=c.head := by omega
        rw [hh];simp
    | succ j =>
        change (if c.head-1+fcast (j+1)=c.head then w else
          c.tape (c.head-1+fcast (j+1))) = z.right.getD j false
        have hh : c.head-1+fcast (j+1)=c.head+fcast j := by simp [fcast];omega
        rw [hh]
        have hn : c.head+fcast j ≠ c.head := by simp [fcast];omega
        rw [if_neg hn]
        exact hr j

theorem one_right (z : Zipper) (s : Fin 6) (w : Bool)
    (h : action z.state z.current = some (s.val,w,true)) :
    one z = some (zipperRight z s w) := by
  simp [one,h,zipperRight]
  cases z.right <;> rfl

theorem one_left (z : Zipper) (s : Fin 6) (w : Bool)
    (h : action z.state z.current = some (s.val,w,false)) :
    one z = some (zipperLeft z s w) := by
  simp [one,h,zipperLeft]
  cases z.left <;> rfl

/-- A successful zipper step is a successful original-table physical step,
     and the two configurations remain related on their entire tapes. -/
theorem sim_one (z : Zipper) (c : Config) (h : Represents z c)
    (z' : Zipper) (hz : one z = some z') :
    ∃ c', rawStep target429 c = some c' ∧ Represents z' c' := by
  rcases h with ⟨hstate,hcur,hl,hr⟩
  have hrep : Represents z c := ⟨hstate,hcur,hl,hr⟩
  have hsource : action z.state z.current =
      (target429 (readSlot c)).map
        (fun move => (move.next.val,move.write,move.right)) := by
    have h0 := action_matches_target c.state (c.tape c.head)
    simp only [readSlot]
    rw [←hstate, ←hcur]
    exact h0
  cases hm : target429 (readSlot c) with
  | none =>
      have ha : action z.state z.current = none := by simpa [hm] using hsource
      simp [one,ha] at hz
  | some move =>
      have ha : action z.state z.current =
          some (move.next.val,move.write,move.right) := by
        simpa [hm] using hsource
      have hr : rawStep target429 c = some (applyMove c move) := by
        simp [rawStep,hm]
      cases hd : move.right with
      | false =>
          have hz' : one z = some (zipperLeft z move.next move.write) :=
            one_left z move.next move.write (by simpa [hd] using ha)
          have heq : z' = zipperLeft z move.next move.write := by
            exact Option.some.inj (hz.symm.trans hz')
          refine ⟨applyMove c move,hr,?_⟩
          subst z'
          have hx := leftRep z c move.next move.write hrep
          have he : (⟨move.write,false,move.next⟩ : Move) = move := by
            cases move
            simp at hd ⊢
            simp [hd]
          simpa only [he] using hx
      | true =>
          have hz' : one z = some (zipperRight z move.next move.write) :=
            one_right z move.next move.write (by simpa [hd] using ha)
          have heq : z' = zipperRight z move.next move.write := by
            exact Option.some.inj (hz.symm.trans hz')
          refine ⟨applyMove c move,hr,?_⟩
          subst z'
          have hx := rightRep z c move.next move.write hrep
          have he : (⟨move.write,true,move.next⟩ : Move) = move := by
            cases move
            simp at hd ⊢
            simp [hd]
          simpa only [he] using hx

theorem physical_run_succ (m : Machine) (n : Nat) (c : Config) :
  BB6Coverage.run m (n+1) c =
    (rawStep m c).bind (BB6Coverage.run m n) := by
  induction n with
  | zero => simp [BB6Coverage.run]
  | succ n ih =>
    change (BB6Coverage.run m (n+1) c).bind (rawStep m) =
      (rawStep m c).bind (BB6Coverage.run m (n+1))
    rw [ih]
    cases hstep : rawStep m c with
    | none => simp [hstep]
    | some d => simp [hstep,BB6Coverage.run]

theorem source_run_rep (n : Nat) (z : Zipper) (c : Config)
    (hrep : Represents z c) (z' : Zipper)
    (hz : BB429OddExcursion.run n z = some z') :
    ∃ c', BB6Coverage.run target429 n c = some c' ∧
      Represents z' c' := by
  induction n generalizing z c with
  | zero =>
    have heq : z=z' := by simpa [BB429OddExcursion.run] using hz
    subst z'
    exact ⟨c,by rfl,hrep⟩
  | succ n ih =>
    have he : ∃ z1, one z=some z1 ∧
        BB429OddExcursion.run n z1=some z' := by
      cases h1 : one z with
      | none => simp [BB429OddExcursion.run,h1] at hz
      | some z1 =>
          refine ⟨z1,rfl,?_⟩
          simpa [BB429OddExcursion.run,h1] using hz
    obtain ⟨z1,h1,h2⟩ := he
    obtain ⟨c1,hphys1,hrep1⟩ := sim_one z c hrep z1 h1
    obtain ⟨c2,hphys2,hrep2⟩ := ih z1 c1 hrep1 h2
    refine ⟨c2,?_,hrep2⟩
    rw [physical_run_succ,hphys1]
    simpa using hphys2

/-- Exact raw physical prepared state, distinct from the blank origin. -/
def sourcePrepared (n : Nat) : Config :=
  { state := ⟨4,by decide⟩
    head := 0
    tape := fun x => if x=1 then true else
      decide (-(n:Int) ≤ x ∧ x<0) }

theorem replicated_ones_getD (n j : Nat) :
    (List.replicate n true).getD j false = decide (j<n) := by
  induction n generalizing j with
  | zero => simp [List.getD]
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
        simpa [List.replicate_succ, show (j+1<n+1) ↔ (j<n) by omega] using ih j

theorem source_prepared_rep (n : Nat) :
    Represents (prepared n) (sourcePrepared n) := by
  unfold Represents
  refine ⟨by rfl, ?_, ?_, ?_⟩
  · change (sourcePrepared n).tape 0 = false
    simp [sourcePrepared]
  · intro j
    change (sourcePrepared n).tape ((0:Int)-fcast j) =
      (List.replicate n true).getD j false
    have hpos : (0:Int)-fcast j ≠ 1 := by simp [fcast];omega
    have hiff : (-(n:Int) ≤ (0:Int)-fcast j ∧ (0:Int)-fcast j<0) ↔
        j<n := by simp [fcast];omega
    change (if (0:Int)-fcast j = 1 then true else
      decide (-(n:Int) ≤ (0:Int)-fcast j ∧ (0:Int)-fcast j<0)) = _
    rw [if_neg hpos]
    simp only [hiff]
    exact (replicated_ones_getD n j).symm
  · intro j
    change (sourcePrepared n).tape ((0:Int)+fcast j) =
      ([true] : List Bool).getD j false
    cases j with
    | zero => simp [sourcePrepared,fcast]
    | succ j =>
        have hneq : (0:Int)+fcast (j+1) ≠ 1 := by simp [fcast];omega
        have hnonneg : ¬((-(n:Int) ≤ (0:Int)+fcast (j+1)) ∧
          (0:Int)+fcast (j+1)<0) := by simp [fcast];omega
        change (if (0:Int)+fcast (j+1) = 1 then true else
          decide (-(n:Int) ≤ (0:Int)+fcast (j+1) ∧
                  (0:Int)+fcast (j+1)<0)) = _
        rw [if_neg hneq]
        simp [hnonneg]
        omega

/-- Source-semantic C/01 fatal event for every odd prepared left block. -/
theorem odd_original_source_fatal (k : Nat) :
    ∃ c, BB6Coverage.run target429 (2*(2*k+3)+12) (sourcePrepared (2*k+3)) =
      some c ∧ c.state.val=2 ∧ c.tape c.head=false ∧
      c.tape (c.head+1)=true := by
  obtain ⟨l,hl⟩ := odd_prepared_fatal k
  obtain ⟨c,hc,hrep⟩ := source_run_rep _ _ _
    (source_prepared_rep (2*k+3)) _ hl
  rcases hrep with ⟨hs,hcur,hleft,hright⟩
  refine ⟨c,hc,hs,hcur,?_⟩
  simpa [fcast,z] using hright 0

/-- The even prepared family reaches a nonfatal C/1, at the marked boundary. -/
theorem even_original_source_at_boundary (k : Nat) :
    ∃ c, BB6Coverage.run target429 (2*(2*k+2)+3) (sourcePrepared (2*k+2)) =
      some c ∧ c.state.val=2 ∧ c.tape c.head=true := by
  obtain ⟨l,hl⟩ := even_prepared_crosses k
  obtain ⟨c,hc,hrep⟩ := source_run_rep _ _ _
    (source_prepared_rep (2*k+2)) _ hl
  exact ⟨c,hc,hrep.1,hrep.2.1⟩

theorem fatal_event_stops_after_two_queries (c : Config)
    (hstate : c.state.val=2) (hcur : c.tape c.head=false)
    (hright : c.tape (c.head+1)=true) :
    (rawStep target429 c).bind (rawStep target429) = none := by
  have hs : c.state = (⟨2,by decide⟩ : Fin 6) := Fin.ext hstate
  have hrow : target429 (⟨2,by decide⟩,false) =
      some ⟨false,true,⟨3,by decide⟩⟩ := by rfl
  have hh : target429 (⟨3,by decide⟩,true) = none := by rfl
  have hslot : readSlot c = (⟨2,by decide⟩,false) := by
    exact Prod.ext hs hcur
  have hstep : rawStep target429 c =
      some (applyMove c ⟨false,true,⟨3,by decide⟩⟩) := by
    unfold rawStep
    rw [hslot,hrow]
    rfl
  rw [hstep]
  change rawStep target429 (applyMove c ⟨false,true,⟨3,by decide⟩⟩) = none
  have hread : readSlot (applyMove c ⟨false,true,⟨3,by decide⟩⟩) =
      (⟨3,by decide⟩,true) := by
    have hne : c.head+1 ≠ c.head := by omega
    simp [readSlot,applyMove,hne,hright]
  unfold rawStep
  rw [hread,hh]
  rfl

/-- All odd prepared E-head source inputs are actual raw-physical halting
    starts. This does NOT assert reachability from blank. The terminal
    query occurs after 2*n+14 executed queries in this interpreter. -/
theorem odd_original_source_halts (k : Nat) :
    BB6Coverage.run target429 (2*(2*k+3)+14)
      (sourcePrepared (2*k+3)) = none := by
  obtain ⟨c,hc,hs,h0,h1⟩ := odd_original_source_fatal k
  have hstop := fatal_event_stops_after_two_queries c hs h0 h1
  have ht : 2*(2*k+3)+14 = (2*(2*k+3)+12)+1+1 := by omega
  rw [ht]
  change (((BB6Coverage.run target429 (2*(2*k+3)+12)
    (sourcePrepared (2*k+3))).bind (rawStep target429)).bind
    (rawStep target429)) = none
  rw [hc]
  exact hstop

#print axioms rightRep
#print axioms leftRep
#print axioms sim_one
#print axioms source_run_rep
#print axioms source_prepared_rep
#print axioms odd_original_source_fatal
#print axioms even_original_source_at_boundary
#print axioms odd_original_source_halts
end BB429PhysicalBridge
