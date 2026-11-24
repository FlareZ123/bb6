import R1Pumps

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R1Sweep
open BB6Coverage Agent50Zipper

abbrev zeroRF_RB (useF : Bool) : Move := ⟨false,true,if useF then 5 else 1⟩
abbrev PP : List Bool := [true,true,false,true,false,true,true]
abbrev LRB : List Bool := [false,true,true]
abbrev actRB (useF : Bool) := zeroRF_RB useF

variable (useF : Bool)

theorem rbInit (R : List Bool) : M (actRB useF) 0 (true::LX) (K++R) (false::LRB) (F++R) := by
  cases useF
  · exact atom 20 (-2) (by decide) rfl
  · exact atom 18 (-2) (by decide) rfl

theorem rbFinish (R : List Bool) : M (actRB useF) 0 [true,true] (K++R) [] (PP++R) :=
  atom 11 (-5) (by decide) rfl

theorem rbPrefixX (R : List Bool) : M (actRB useF) 1 [] (PP++X++R) (false::(LX++J)) (F++R) :=
  atom 31 7 (by decide) rfl

theorem rbPrefixT (R : List Bool) : M (actRB useF) 1 [] (PP++T++R) (false::(LT++J)) (F++R) :=
  atom 25 9 (by decide) rfl

theorem rbFinishX (R : List Bool) : M (actRB useF) 0 (true::(D++J)) (K++R) [] (P++E++X++R) :=
  atom 15 (-9) (by decide) rfl

theorem rbFinishT (R : List Bool) : M (actRB useF) 0 (true::(V++LT++J)) (K++R) [] (P++E++T++T++R) :=
  atom 31 (-17) (by decide) rfl

theorem rbPrefixET (R : List Bool) : M (actRB useF) 1 [] (P++E++T++R) (false::(Q++C)) (F++R) :=
  atom 25 9 (by decide) rfl

theorem rbFinishET (R : List Bool) : M (actRB useF) 0 (true::(V++Q++C)) (K++R) [] (P++X++Y++T++R) :=
  atom 39 (-17) (by decide) rfl

/-- Reverse a run of X's with a two-bit extra marker before L. -/
theorem reverseMarkedXs {action : Move} (k m : Nat) (L : List Bool) :
    M action 0 (true::(V++rep Q k++J++L)) (K++rep T m++E)
      (true::L) (K++rep X k++rep T (m+1)++E) := by
  have h1 := reverseStart (action:=action) (rep Q k++L) (rep T m++E)
  have h2 := reverseXs (action:=action) k L (rep T (m+1)++E)
  have heq : V++rep Q k++J++L = V++J++(rep Q k++L) := by
    simp only [List.append_assoc,← List.append_assoc (rep Q k) J L,repJ_comm k,List.append_assoc]
  rw [heq]
  simp only [rep,List.append_assoc] at h1 h2 ⊢
  exact h1.then h2

/-- The usual X-zero case now performs an additional complete sweep and
    switches to a seven-bit prefix PP. -/
theorem rbFamilyXZero (i m : Nat) : M (actRB useF) 1 []
    (P++rep X (i+1)++Y++rep T m++E) []
    (PP++rep X (i+1)++rep T (m+2)++E) := by
  have h1 := prefixX (action:=actRB useF) (rep X i++Y++rep T m++E)
  have h2 := phaseZero (action:=actRB useF) i m LX
  have h3 := rbInit useF (rep X (i+1)++rep T (m+1)++E)
  have h4 := forwardXs (action:=actRB useF) (i+1) LRB (rep T (m+1)++E)
  have h5 := suffixSweep (action:=actRB useF) (m+1) (rep Q (i+1)++LRB)
  have h6 := reverseMarkedXs (action:=actRB useF) (i+1) (m+1) [true]
  have h7 := rbFinish useF (rep X (i+1)++rep T (m+2)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact ((((((h1.then h2).then h3).then h4).then h5).then h6).then h7)

theorem rbPPX (k m : Nat) : M (actRB useF) 1 [] (PP++rep X (k+1)++rep T m++E)
    [] (P++E++rep X (k+1)++rep T (m+1)++E) := by
  have h1 := rbPrefixX useF (rep X k++rep T m++E)
  have h2 := forwardXs (action:=actRB useF) k (LX++J) (rep T m++E)
  have h3 := suffixSweep (action:=actRB useF) m (rep Q k++LX++J)
  have h4 := reverseMarkedXs (action:=actRB useF) k m (D++J)
  have h5 := rbFinishX useF (rep X k++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 h5 ⊢
  exact ((((h1.then h2).then h3).then h4).then h5)

theorem rbPPT (m : Nat) : M (actRB useF) 1 [] (PP++rep T (m+1)++E)
    [] (P++E++rep T (m+2)++E) := by
  have h1 := rbPrefixT useF (rep T m++E)
  have h2 := suffixSweep (action:=actRB useF) m (LT++J)
  have h3 := rbFinishT useF (rep T m++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem rbPET (m : Nat) : M (actRB useF) 1 [] (P++E++rep T (m+1)++E)
    [] (P++X++Y++rep T (m+1)++E) := by
  have h1 := rbPrefixET useF (rep T m++E)
  have h2 := suffixSweep (action:=actRB useF) m (Q++C)
  have h3 := rbFinishET useF (rep T m++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

inductive GoodRB : List Bool → Prop where
  | e (i m : Nat) : GoodRB (P++E++rep X (i+1)++rep T m++E)
  | t (i j m : Nat) : GoodRB (P++T++rep X i++Y++rep X j++rep T m++E)
  | x (i j m : Nat) : GoodRB (P++rep X (i+1)++Y++rep X j++rep T m++E)
  | pp (k m : Nat) : GoodRB (PP++rep X k++rep T (m+1)++E)
  | et (m : Nat) : GoodRB (P++E++rep T (m+1)++E)

theorem rbStep {r : List Bool} (H : GoodRB r) : ∃ r', GoodRB r' ∧ M (actRB useF) 1 [] r [] r' := by
  cases H with
  | e i m => exact ⟨_,by simpa [rep] using GoodRB.t 0 i m,familyE i m⟩
  | t i j m =>
    cases j with
    | zero => exact ⟨_,by simpa [rep] using GoodRB.x 0 (i+1) (m+1),by simpa [rep] using familyTZero (action:=actRB useF) i m⟩
    | succ j => exact ⟨_,GoodRB.t (i+1) j (m+1),familyTPos i j m⟩
  | x i j m =>
    cases j with
    | zero => exact ⟨_,GoodRB.pp (i+1) (m+1),by simpa [rep] using rbFamilyXZero useF i m⟩
    | succ j => exact ⟨_,GoodRB.x (i+1) j (m+1),familyXPos i j m⟩
  | pp k m =>
    cases k with
    | zero => exact ⟨_,GoodRB.et (m+1),by simpa [rep] using rbPPT useF m⟩
    | succ k => exact ⟨_,GoodRB.e k (m+2),rbPPX useF k (m+1)⟩
  | et m => exact ⟨_,by simpa [rep] using GoodRB.x 0 0 (m+1),rbPET useF m⟩

theorem rbFirst : zrun (tableWith (actRB useF)) (if useF then 108 else 110) start = some ⟨0,-8,[],PP++T++E⟩ := by cases useF <;> rfl

theorem all_defined_RB_RF (n : Nat) : ∃ z, zrun (tableWith (actRB useF)) n start = some z :=
  runForeverOf GoodRB ⟨_, -8,_,by simpa [rep] using GoodRB.pp 0 0,rbFirst useF⟩
    (fun _ h => rbStep useF h) n

#print axioms all_defined_RB_RF
end BB6Coverage.Agent47R1Sweep
