import SparseZipper

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R1Sweep
open BB6Coverage Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,false,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,false,4⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev P : List Bool := [true,true,false,true,true]
abbrev X : List Bool := [false,false,true,true]
abbrev Y : List Bool := [false,true,true,true]
abbrev T : List Bool := [false,true,false,true,true,true]
abbrev E : List Bool := [false,true]
abbrev J : List Bool := [false,true]
abbrev Q : List Bool := [false,true,false,true]
abbrev V : List Bool := [false,false,false,true]
abbrev W : List Bool := [false,true,false,false,false,true]
abbrev K : List Bool := [true,true]
abbrev F : List Bool := [true,true,true,true]
abbrev LT : List Bool := [false,true,false,false,true,false,true]
abbrev LX : List Bool := [false,true,true,false,true]
abbrev C : List Bool := [false,false,true,false,true]
abbrev D : List Bool := [true,false,true]

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) : rep w n ++ w = w ++ rep w n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

theorem repJ_comm (n : Nat) : rep Q n ++ J = J ++ rep Q n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]; rfl

/-- A macro guarantees a defined run for every absolute head coordinate.
    k is a lower bound on its primitive length. Both words are the exact
    zipper lists, with the scanned symbol included on the left. -/
def M (k : Nat) (l r l' r' : List Bool) : Prop :=
  ∀ h : Int, ∃ n h', k ≤ n ∧ zrun table n ⟨0,h,l,r⟩ = some ⟨0,h',l',r'⟩

theorem atom {k : Nat} {l r l' r' : List Bool} (n : Nat) (d : Int)
    (hk : k ≤ n) (H : zrun table n ⟨0,0,l,r⟩ = some ⟨0,d,l',r'⟩) : M k l r l' r' := by
  intro h
  refine ⟨n,d+h,hk,?_⟩
  have hh := zrun_shift table h n ⟨0,0,l,r⟩
  rw [H] at hh
  simpa [shift] using hh

theorem M.then {k : Nat} {l r a b l' r' : List Bool}
    (H : M k l r a b) (G : M 0 a b l' r') : M k l r l' r' := by
  intro h
  obtain ⟨n,h',hn,hr⟩ := H h
  obtain ⟨m,h'',hm,hs⟩ := G h'
  exact ⟨n+m,h'',by omega,join hr hs⟩

theorem M.refl (l r : List Bool) : M 0 l r l r := by
  intro h; exact ⟨0,h,Nat.le_refl _,rfl⟩

-- Each primitive macro is checked by reduction, with opaque list tails.
theorem prefixT (R : List Bool) : M 1 [] (P++T++R) (false::LT) (F++R) :=
  atom 19 7 (by decide) rfl
theorem prefixX (R : List Bool) : M 1 [] (P++X++R) (false::LX) (F++R) :=
  atom 25 5 (by decide) rfl
theorem prefixE (R : List Bool) : M 1 [] (P++E++X++R) (true::C) (K++Y++R) :=
  atom 25 5 (by decide) rfl
theorem forwardX (L R : List Bool) : M 0 (false::L) (F++X++R) (false::(Q++L)) (F++R) :=
  atom 20 4 (by decide) rfl
theorem forwardY (L R : List Bool) : M 0 (false::L) (F++Y++R) (false::(V++L)) (F++R) :=
  atom 8 4 (by decide) rfl
theorem forwardT (L R : List Bool) : M 0 (false::L) (F++T++R) (false::(W++L)) (F++R) :=
  atom 14 6 (by decide) rfl
theorem terminal (L : List Bool) : M 0 (false::L) (F++E) (true::(V++L)) (K++E) :=
  atom 20 4 (by decide) rfl
theorem reverseT (L R : List Bool) : M 0 (true::(V++W++L)) (K++R) (true::(V++L)) (K++T++R) :=
  atom 10 (-6) (by decide) rfl
theorem reverseStart (L R : List Bool) : M 0 (true::(V++J++L)) (K++R) (true::L) (K++T++R) :=
  atom 10 (-6) (by decide) rfl
theorem reverseX (L R : List Bool) : M 0 (true::(Q++L)) (K++R) (true::L) (K++X++R) :=
  atom 4 (-4) (by decide) rfl
theorem reverseY (L R : List Bool) : M 0 (true::(J++V++L)) (K++R) (true::(J++L)) (K++Y++R) :=
  atom 16 (-4) (by decide) rfl
theorem restart (L R : List Bool) : M 0 (true::(V++V++L)) (K++R) (false::(J++L)) (K++T++R) :=
  atom 10 (-6) (by decide) rfl
theorem replayT (L R : List Bool) : M 0 (false::L) (K++T++R) (false::(Q++L)) (F++R) :=
  atom 12 4 (by decide) rfl
theorem finishT (R : List Bool) : M 0 (true::C) (K++R) [] (P++T++R) :=
  atom 19 (-9) (by decide) rfl
theorem finishX (R : List Bool) : M 0 (true::D) (K++R) [] (P++X++R) :=
  atom 13 (-7) (by decide) rfl
theorem finishTX (R : List Bool) : M 0 (true::LT) (K++R) [] (P++X++Y++R) :=
  atom 29 (-11) (by decide) rfl
theorem finishXE (R : List Bool) : M 0 (true::LX) (K++R) [] (P++E++X++R) :=
  atom 15 (-9) (by decide) rfl

theorem forwardXs (n : Nat) (L R : List Bool) : M 0 (false::L) (F++rep X n++R) (false::(rep Q n++L)) (F++R) := by
  induction n generalizing L with
  | zero => exact M.refl _ _
  | succ n ih =>
    have H := (forwardX L (rep X n++R)).then (ih (Q++L))
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Q n) Q L,rep_snoc Q n] using H

theorem forwardTs (n : Nat) (L R : List Bool) : M 0 (false::L) (F++rep T n++R) (false::(rep W n++L)) (F++R) := by
  induction n generalizing L with
  | zero => exact M.refl _ _
  | succ n ih =>
    have H := (forwardT L (rep T n++R)).then (ih (W++L))
    simpa only [rep,List.append_assoc,← List.append_assoc (rep W n) W L,rep_snoc W n] using H

theorem reverseTs (n : Nat) (L R : List Bool) : M 0 (true::(V++rep W n++L)) (K++R) (true::(V++L)) (K++rep T n++R) := by
  induction n generalizing R with
  | zero => exact M.refl _ _
  | succ n ih =>
    have H := (reverseT (rep W n++L) R).then (ih (T++R))
    simpa only [rep,List.append_assoc,← List.append_assoc (rep T n) T R,rep_snoc T n] using H

theorem reverseXs (n : Nat) (L R : List Bool) : M 0 (true::(rep Q n++L)) (K++R) (true::L) (K++rep X n++R) := by
  induction n generalizing R with
  | zero => exact M.refl _ _
  | succ n ih =>
    have H := (reverseX (rep Q n++L) R).then (ih (X++R))
    simpa only [rep,List.append_assoc,← List.append_assoc (rep X n) X R,rep_snoc X n] using H

/-- The first right sweep, terminal reversal, and transfer back over the T suffix. -/
theorem phase (i j m : Nat) (L : List Bool) :
    M 0 (false::L) (F++rep X i++Y++rep X j++rep T m++E)
      (true::(V++rep Q j++V++rep Q i++L)) (K++rep T m++E) := by
  have h1 := forwardXs i L (Y++rep X j++rep T m++E)
  have h2 := forwardY (rep Q i++L) (rep X j++rep T m++E)
  have h3 := forwardXs j (V++rep Q i++L) (rep T m++E)
  have h4 := forwardTs m (rep Q j++V++rep Q i++L) E
  have h5 := terminal (rep W m++rep Q j++V++rep Q i++L)
  have h6 := reverseTs m (rep Q j++V++rep Q i++L) E
  simp only [List.append_assoc] at h1 h2 h3 h4 h5 h6 ⊢
  exact (((((h1.then h2).then h3).then h4).then h5).then h6)

/-- At least one X lies to the right of the marked Y. Move the marker one
    X to the right, leaving one extra T, and process the earlier X blocks. -/
theorem phasePos (i j m : Nat) (L : List Bool) :
    M 0 (false::L) (F++rep X i++Y++rep X (j+1)++rep T m++E)
      (true::(J++L)) (K++rep X i++Y++rep X j++rep T (m+1)++E) := by
  have h1 := phase i (j+1) m L
  have h2 := reverseStart (J++rep Q j++V++rep Q i++L) (rep T m++E)
  have h3 := reverseXs j (J++V++rep Q i++L) (rep T (m+1)++E)
  have h4 := reverseY (rep Q i++L) (rep X j++rep T (m+1)++E)
  have h5 := reverseXs i (J++L) (Y++rep X j++rep T (m+1)++E)
  have eq1 : J++rep Q j = rep Q j++J := (repJ_comm j).symm
  have eq2 : J++rep Q i = rep Q i++J := (repJ_comm i).symm
  simp only [List.append_assoc] at h1 h2 h3 h4 h5 ⊢
  have h12 : M 0 (false::L) (F++(rep X i++(Y++(rep X (j+1)++(rep T m++E)))))
      (true::(J++(rep Q j++(V++(rep Q i++L))))) (K++(rep T (m+1)++E)) := by
    exact h1.then h2
  have h12' : M 0 (false::L) (F++(rep X i++(Y++(rep X (j+1)++(rep T m++E)))))
      (true::(rep Q j++(J++(V++(rep Q i++L))))) (K++(rep T (m+1)++E)) := by
    simpa only [← List.append_assoc J (rep Q j) (V++(rep Q i++L)),eq1,List.append_assoc] using h12
  have h1234 := (h12'.then h3).then h4
  have h1234' : M 0 (false::L) (F++(rep X i++(Y++(rep X (j+1)++(rep T m++E)))))
      (true::(rep Q i++(J++L))) (K++(Y++(rep X j++(rep T (m+1)++E)))) := by
    simpa only [← List.append_assoc J (rep Q i) L,eq2,List.append_assoc] using h1234
  exact h1234'.then h5

/-- The Y marker reaches the end of the X segment: perform a second
    right/left sweep. This is the only case that changes the outer phase. -/
theorem phaseZero (i m : Nat) (L : List Bool) :
    M 0 (false::L) (F++rep X i++Y++rep T m++E)
      (true::L) (K++rep X (i+1)++rep T (m+1)++E) := by
  have h1 := phase i 0 m L
  have h2 := restart (rep Q i++L) (rep T m++E)
  have h3 := replayT (J++rep Q i++L) (rep T m++E)
  have h4 := forwardTs m (Q++J++rep Q i++L) E
  have h5 := terminal (rep W m++Q++J++rep Q i++L)
  have h6 := reverseTs m (Q++J++rep Q i++L) E
  have h7 := reverseStart (Q++rep Q i++L) (rep T m++E)
  have h8 := reverseXs (i+1) L (rep T (m+1)++E)
  simp only [List.append_assoc,rep,List.nil_append] at h1
  simp only [List.append_assoc] at h2 h3 h4 h5 h6 h7 h8 ⊢
  exact (((((((h1.then h2).then h3).then h4).then h5).then h6).then h7).then h8)

theorem familyE (i m : Nat) :
    M 1 [] (P++E++rep X (i+1)++rep T m++E)
      [] (P++T++Y++rep X i++rep T m++E) := by
  have H := (prefixE (rep X i++rep T m++E)).then (finishT (Y++rep X i++rep T m++E))
  simpa only [rep,List.append_assoc] using H

theorem familyTPos (i j m : Nat) :
    M 1 [] (P++T++rep X i++Y++rep X (j+1)++rep T m++E)
      [] (P++T++rep X (i+1)++Y++rep X j++rep T (m+1)++E) := by
  have h1 := prefixT (rep X i++Y++rep X (j+1)++rep T m++E)
  have h2 := phasePos i j m LT
  have h3 := reverseX C (rep X i++Y++rep X j++rep T (m+1)++E)
  have h4 := finishT (rep X (i+1)++Y++rep X j++rep T (m+1)++E)
  simp only [List.append_assoc] at h1 h2 h3 h4 ⊢
  exact ((h1.then h2).then h3).then h4

theorem familyTZero (i m : Nat) :
    M 1 [] (P++T++rep X i++Y++rep T m++E)
      [] (P++X++Y++rep X (i+1)++rep T (m+1)++E) := by
  have h1 := prefixT (rep X i++Y++rep T m++E)
  have h2 := phaseZero i m LT
  have h3 := finishTX (rep X (i+1)++rep T (m+1)++E)
  simp only [List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

theorem familyXPos (i j m : Nat) :
    M 1 [] (P++rep X (i+1)++Y++rep X (j+1)++rep T m++E)
      [] (P++rep X (i+2)++Y++rep X j++rep T (m+1)++E) := by
  have h1 := prefixX (rep X i++Y++rep X (j+1)++rep T m++E)
  have h2 := phasePos i j m LX
  have h3 := reverseX D (rep X i++Y++rep X j++rep T (m+1)++E)
  have h4 := finishX (rep X (i+1)++Y++rep X j++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 h4 ⊢
  exact ((h1.then h2).then h3).then h4

theorem familyXZero (i m : Nat) :
    M 1 [] (P++rep X (i+1)++Y++rep T m++E)
      [] (P++E++rep X (i+2)++rep T (m+1)++E) := by
  have h1 := prefixX (rep X i++Y++rep T m++E)
  have h2 := phaseZero i m LX
  have h3 := finishXE (rep X (i+1)++rep T (m+1)++E)
  simp only [rep,List.append_assoc] at h1 h2 h3 ⊢
  exact (h1.then h2).then h3

inductive Good : List Bool → Prop where
  | e (i m : Nat) : Good (P++E++rep X (i+1)++rep T m++E)
  | t (i j m : Nat) : Good (P++T++rep X i++Y++rep X j++rep T m++E)
  | x (i j m : Nat) : Good (P++rep X (i+1)++Y++rep X j++rep T m++E)

theorem goodStep {r : List Bool} (H : Good r) : ∃ r', Good r' ∧ M 1 [] r [] r' := by
  cases H with
  | e i m =>
    exact ⟨_, by simpa [rep] using Good.t 0 i m, familyE i m⟩
  | t i j m =>
    cases j with
    | zero => exact ⟨_, by simpa [rep] using Good.x 0 (i+1) (m+1), by simpa [rep] using familyTZero i m⟩
    | succ j => exact ⟨_,Good.t (i+1) j (m+1),familyTPos i j m⟩
  | x i j m =>
    cases j with
    | zero => exact ⟨_,Good.e (i+1) (m+1),by simpa [rep] using familyXZero i m⟩
    | succ j => exact ⟨_,Good.x (i+1) j (m+1),familyXPos i j m⟩

def start : Z := ⟨0,0,[],[]⟩
theorem first : zrun table 64 start = some ⟨0,-8,[],P++E++X++E⟩ := rfl

theorem arbitraryRun (n : Nat) : ∃ t h r, n ≤ t ∧ Good r ∧ zrun table t start = some ⟨0,h,[],r⟩ := by
  induction n with
  | zero => exact ⟨64,-8,_,by decide,by simpa [rep] using Good.e 0 0,first⟩
  | succ n ih =>
    obtain ⟨t,h,r,ht,hg,hr⟩ := ih
    obtain ⟨r',hg',hs⟩ := goodStep hg
    obtain ⟨k,h',hk,hs'⟩ := hs h
    exact ⟨t+k,h',r',by omega,hg',join hr hs'⟩

theorem all_defined (n : Nat) : ∃ z, zrun table n start = some z := by
  obtain ⟨t,h,r,ht,_,hr⟩ := arbitraryRun n
  rw [show t=n+(t-n) by omega,zrun_add] at hr
  cases hrun : zrun table n start with
  | none => simp [hrun] at hr
  | some z => exact ⟨z,rfl⟩

#print axioms familyE
#print axioms familyTPos
#print axioms familyTZero
#print axioms familyXPos
#print axioms familyXZero
#print axioms all_defined
end BB6Coverage.Agent47R1Sweep
