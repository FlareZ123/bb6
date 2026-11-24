import R1RB

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R1Sweep
open BB6Coverage Agent50Zipper

abbrev oneRF : Move := ⟨true,true,5⟩
abbrev U : List Bool := [false,false,true,false,true,true]
abbrev LUX' : List Bool := [true,false,false,true,false,true,true,false,true]
abbrev LUX : List Bool := J++LUX'
abbrev LUT : List Bool := [false,true,false,false,true,false,false,true,false,true,true,false,true]
abbrev LXET : List Bool := [false,true,false,true,false,false,false,true,false,true,true,false,true]
abbrev LXT' : List Bool := [false,false,false,true,false,true,true,false,true]
abbrev LXT : List Bool := J++LXT'

theorem rfPrefixUX (R : List Bool) : M oneRF 1 [] (P++U++X++R) (false::LUX) (F++R) :=
  atom 51 11 (by decide) rfl
theorem rfFinishUX (R : List Bool) : M oneRF 0 (true::LUX') (K++R) [] (P++X++E++X++R) :=
  atom 19 (-13) (by decide) rfl
theorem rfPrefixUT (R : List Bool) : M oneRF 1 [] (P++U++T++R) (false::LUT) (F++R) :=
  atom 45 13 (by decide) rfl
theorem rfFinishUT (R : List Bool) : M oneRF 0 (true::(V++LUT)) (K++R) [] (P++X++E++T++T++R) :=
  atom 35 (-21) (by decide) rfl
theorem rfAtomUE : M oneRF 1 [] (P++U++E) [] (P++X++E++T++E) :=
  atom 76 (-4) (by decide) rfl
theorem rfAtomXEX (R : List Bool) : M oneRF 1 [] (P++X++E++X++R) [] (P++X++T++Y++R) :=
  atom 68 (-4) (by decide) rfl
theorem rfPrefixXET (R : List Bool) : M oneRF 1 [] (P++X++E++T++R) (false::LXET) (F++R) :=
  atom 45 13 (by decide) rfl
theorem rfFinishXET (R : List Bool) : M oneRF 0 (true::(V++LXET)) (K++R) [] (P++X++X++Y++T++R) :=
  atom 43 (-21) (by decide) rfl
theorem rfPrefixXT (R : List Bool) : M oneRF 1 [] (P++X++T++R) (false::LXT) (F++R) :=
  atom 39 11 (by decide) rfl
theorem rfFinishXTPos (R : List Bool) : M oneRF 0 (true::LXT') (K++R) [] (P++X++T++R) :=
  atom 23 (-13) (by decide) rfl
theorem rfFinishXTZero (R : List Bool) : M oneRF 0 (true::LXT) (K++R) [] (P++X++X++Y++R) :=
  atom 33 (-15) (by decide) rfl
theorem rfFinishXZero (R : List Bool) : M oneRF 0 (true::LX) (K++R) [] (P++U++R) :=
  atom 19 (-9) (by decide) rfl

theorem rfUX (k m : Nat) : M oneRF 1 [] (P++U++rep X (k+1)++rep T m++E)
    [] (P++X++E++rep X (k+1)++rep T (m+1)++E) := by
  have h1 := rfPrefixUX (rep X k++rep T m++E)
  have h2 := forwardXs (action:=oneRF) k LUX (rep T m++E)
  have h3 := suffixSweep (action:=oneRF) m (rep Q k++LUX)
  have h4 := reverseMarkedXs (action:=oneRF) k m LUX'
  have h5 := rfFinishUX (rep X k++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 h5 ⊢
  exact ((((h1.then h2).then h3).then h4).then h5)

theorem rfUT (m : Nat) : M oneRF 1 [] (P++U++rep T (m+1)++E)
    [] (P++X++E++rep T (m+2)++E) := by
  have h1 := rfPrefixUT (rep T m++E)
  have h2 := suffixSweep (action:=oneRF) m LUT
  have h3 := rfFinishUT (rep T m++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem rfXEX (k m : Nat) : M oneRF 1 [] (P++X++E++rep X (k+1)++rep T m++E)
    [] (P++X++T++Y++rep X k++rep T m++E) := by
  simpa only [rep,List.append_assoc] using rfAtomXEX (rep X k++rep T m++E)

theorem rfXET (m : Nat) : M oneRF 1 [] (P++X++E++rep T (m+1)++E)
    [] (P++X++X++Y++rep T (m+1)++E) := by
  have h1 := rfPrefixXET (rep T m++E)
  have h2 := suffixSweep (action:=oneRF) m LXET
  have h3 := rfFinishXET (rep T m++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem rfXTPos (i j m : Nat) : M oneRF 1 [] (P++X++T++rep X i++Y++rep X (j+1)++rep T m++E)
    [] (P++X++T++rep X (i+1)++Y++rep X j++rep T (m+1)++E) := by
  have h1 := rfPrefixXT (rep X i++Y++rep X (j+1)++rep T m++E)
  have h2 := phasePos (action:=oneRF) i j m LXT
  have h3 := reverseX (action:=oneRF) LXT' (rep X i++Y++rep X j++rep T (m+1)++E)
  have h4 := rfFinishXTPos (rep X (i+1)++Y++rep X j++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 ⊢
  exact ((h1.then h2).then h3).then h4

theorem rfXTZero (i m : Nat) : M oneRF 1 [] (P++X++T++rep X i++Y++rep T m++E)
    [] (P++X++X++Y++rep X (i+1)++rep T (m+1)++E) := by
  have h1 := rfPrefixXT (rep X i++Y++rep T m++E)
  have h2 := phaseZero (action:=oneRF) i m LXT
  have h3 := rfFinishXTZero (rep X (i+1)++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem rfXZero (i m : Nat) : M oneRF 1 [] (P++rep X (i+1)++Y++rep T m++E)
    [] (P++U++rep X (i+1)++rep T (m+1)++E) := by
  have h1 := prefixX (action:=oneRF) (rep X i++Y++rep T m++E)
  have h2 := phaseZero (action:=oneRF) i m LX
  have h3 := rfFinishXZero (rep X (i+1)++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

inductive GoodRF : List Bool → Prop where
  | u (k m : Nat) : GoodRF (P++U++rep X k++rep T m++E)
  | xe (k m : Nat) : GoodRF (P++X++E++rep X k++rep T (m+1)++E)
  | xt (i j m : Nat) : GoodRF (P++X++T++rep X i++Y++rep X j++rep T m++E)
  | x (i j m : Nat) : GoodRF (P++rep X (i+1)++Y++rep X j++rep T m++E)

theorem rfStep {r : List Bool} (H : GoodRF r) : ∃ r', GoodRF r' ∧ M oneRF 1 [] r [] r' := by
  cases H with
  | u k m =>
    cases k with
    | zero =>
      cases m with
      | zero => exact ⟨_,by simpa [rep] using GoodRF.xe 0 0,rfAtomUE⟩
      | succ m => exact ⟨_,by simpa [rep] using GoodRF.xe 0 (m+1),by simpa [rep] using rfUT m⟩
    | succ k => exact ⟨_,GoodRF.xe (k+1) m,rfUX k m⟩
  | xe k m =>
    cases k with
    | zero => exact ⟨_,by simpa [rep] using GoodRF.x 1 0 (m+1),by simpa [rep] using rfXET m⟩
    | succ k => exact ⟨_,by simpa [rep] using GoodRF.xt 0 k (m+1),rfXEX k (m+1)⟩
  | xt i j m =>
    cases j with
    | zero => exact ⟨_,by simpa [rep] using GoodRF.x 1 (i+1) (m+1),by simpa [rep] using rfXTZero i m⟩
    | succ j => exact ⟨_,GoodRF.xt (i+1) j (m+1),rfXTPos i j m⟩
  | x i j m =>
    cases j with
    | zero => exact ⟨_,GoodRF.u (i+1) (m+1),by simpa [rep] using rfXZero i m⟩
    | succ j => exact ⟨_,GoodRF.x (i+1) j (m+1),familyXPos i j m⟩

theorem rfFirst : zrun (tableWith oneRF) 68 start = some ⟨0,-8,[],P++U++E⟩ := rfl

theorem all_defined_RF (n : Nat) : ∃ z, zrun (tableWith oneRF) n start = some z :=
  runForeverOf GoodRF ⟨68,-8,_,by simpa [rep] using GoodRF.u 0 0,rfFirst⟩ (fun _ h => rfStep h) n

#print axioms all_defined_RF
end BB6Coverage.Agent47R1Sweep
