import R1Sweep

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R1Sweep
open BB6Coverage Agent50Zipper

abbrev oneBD (useD : Bool) : Move := ⟨true,false,if useD then 3 else 1⟩
abbrev oneLC : Move := ⟨true,false,2⟩
abbrev pumpAction (useLA : Bool) : Move := if useLA then ⟨true,false,0⟩ else ⟨false,true,4⟩

variable {action : Move}

theorem suffixSweep (n : Nat) (L : List Bool) :
    M action 0 (false::L) (F++rep T n++E) (true::(V++L)) (K++rep T n++E) := by
  have h1 := forwardTs (action:=action) n L E
  have h2 := terminal (action:=action) (rep W n++L)
  have h3 := reverseTs (action:=action) n L E
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem finishBD (useD : Bool) (R : List Bool) :
    M (oneBD useD) 0 (true::(V++LT)) (K++R) [] (P++T++T++R) :=
  atom 29 (-15) (by decide) (by cases useD <;> rfl)

theorem pumpBD (useD : Bool) (n : Nat) :
    M (oneBD useD) 1 [] (P++rep T (n+1)++E) [] (P++rep T (n+2)++E) := by
  have h1 := prefixT (action:=oneBD useD) (rep T n++E)
  have h2 := suffixSweep (action:=oneBD useD) n LT
  have h3 := finishBD useD (rep T n++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem firstBD (useD : Bool) : zrun (tableWith (oneBD useD)) 140 start = some ⟨0,-12,[],P++rep T 2++E⟩ := by cases useD <;> rfl
theorem all_defined_BD (useD : Bool) (n : Nat) : ∃ z, zrun (tableWith (oneBD useD)) n start = some z := by
  apply runForeverOf (fun r => ∃ k : Nat, r = P++rep T (k+1)++E) _ _ n
  · exact ⟨140,-12,_,⟨1,rfl⟩,firstBD useD⟩
  · rintro r ⟨k,rfl⟩
    exact ⟨_,⟨k+1,rfl⟩,pumpBD useD k⟩

theorem finishLC (R : List Bool) :
    M oneLC 0 (true::(V++LX)) (K++R) [] (P++X++T++R) :=
  atom 23 (-13) (by decide) rfl

theorem pumpLC (n : Nat) :
    M oneLC 1 [] (P++X++rep T n++E) [] (P++X++rep T (n+1)++E) := by
  have h1 := prefixX (action:=oneLC) (rep T n++E)
  have h2 := suffixSweep (action:=oneLC) n LX
  have h3 := finishLC (rep T n++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem firstLC : zrun (tableWith oneLC) 124 start = some ⟨0,-10,[],P++X++rep T 1++E⟩ := rfl
theorem all_defined_LC (n : Nat) : ∃ z, zrun (tableWith oneLC) n start = some z := by
  apply runForeverOf (fun r => ∃ k : Nat, r = P++X++rep T k++E) _ _ n
  · exact ⟨124,-10,_,⟨1,rfl⟩,firstLC⟩
  · rintro r ⟨k,rfl⟩
    exact ⟨_,⟨k+1,rfl⟩,pumpLC k⟩

theorem finishLA_RE (useLA : Bool) (R : List Bool) :
    M (pumpAction useLA) 0 (true::(V++Q++W++LT)) (K++R) [] (P++T++T++X++T++R) :=
  atom 43 (-25) (by decide) (by cases useLA <;> rfl)

theorem pumpLA_RE (useLA : Bool) (n : Nat) :
    M (pumpAction useLA) 1 [] (P++T++T++X++rep T n++E) [] (P++T++T++X++rep T (n+1)++E) := by
  have h1 := prefixT (action:=pumpAction useLA) (T++X++rep T n++E)
  have h2 := forwardT (action:=pumpAction useLA) LT (X++rep T n++E)
  have h3 := forwardX (action:=pumpAction useLA) (W++LT) (rep T n++E)
  have h4 := suffixSweep (action:=pumpAction useLA) n (Q++W++LT)
  have h5 := finishLA_RE useLA (rep T n++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 h5 ⊢
  exact (((h1.then h2).then h3).then h4).then h5

theorem firstLA_RE (useLA : Bool) :
    zrun (tableWith (pumpAction useLA)) (if useLA then 856 else 862) start = some ⟨0,-28,[],P++T++T++X++rep T 4++E⟩ := by cases useLA <;> rfl

theorem all_defined_LA_RE (useLA : Bool) (n : Nat) : ∃ z, zrun (tableWith (pumpAction useLA)) n start = some z := by
  apply runForeverOf (fun r => ∃ k : Nat, r = P++T++T++X++rep T k++E) _ _ n
  · exact ⟨_, -28,_,⟨4,rfl⟩,firstLA_RE useLA⟩
  · rintro r ⟨k,rfl⟩
    exact ⟨_,⟨k+1,rfl⟩,pumpLA_RE useLA k⟩

#print axioms all_defined_BD
#print axioms all_defined_LC
#print axioms all_defined_LA_RE
end BB6Coverage.Agent47R1Sweep
