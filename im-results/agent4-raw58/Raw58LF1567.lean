import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF1567
open BB6Coverage Agent31Pump
-- 1RB1LF_1RC---_0RD0LF_1LD1RE_0RC0RA_0LC1RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def P : List Bool := [true,false,false]
def Q : List Bool := [false,false,true]
def Z : List Bool := [false,true,false]
def L (k : Nat) : List Bool := rep P k ++ [true,false,true,true]
def D (k : Nat) : Z0 := ⟨3,L k,[]⟩
def E (k : Nat) (r : List Bool) : Z0 := ⟨4,false::L k,r⟩
def B (b : Bool) (r : List Bool) : Z0 := ⟨1,[false,true],false::b::r⟩

theorem pushL (k : Nat) : P ++ L k = L (k+1) := by simp [L,rep,List.append_assoc]

theorem reset (k : Nat) (R : List Bool) :
    run0 table (9*k) ⟨2,false::L k,false::R⟩ =
      some ⟨2,false::L 0,false::(rep Q k ++ R)⟩ := by
  simpa only [L,rep,List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using
    sweepL table 2 [false] [false] P Q 9 (by intro l r; rfl) k [true,false,true,true] R

theorem resetEnd (R : List Bool) :
    run0 table 11 ⟨2,false::L 0,false::R⟩ = some (B false ([false,true]++R)) := by rfl

theorem resetAll (k : Nat) (R : List Bool) :
    run0 table (9*k+11) ⟨2,false::L k,false::R⟩ =
      some (B false ([false,true]++rep Q k++R)) := by
  have h := join0 (reset k R) (resetEnd (rep Q k++R))
  simpa only [List.append_assoc] using h

theorem rotateZ (k : Nat) : [false,true]++rep Q k = rep Z k++[false,true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    change Z ++ ([false,true]++rep Q k) = Z ++ (rep Z k++[false,true])
    rw [ih]

theorem finish1 (k : Nat) (b : Bool) (S : List Bool) :
    run0 table (9*k+7) (E k (true::b::S)) =
      some (B false (rep Z k++[false,false,b]++S)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 5 (E (k+1) (true::b::S)) = some ⟨2,false::L k,[false,false,false,false,b]++S⟩ := by rfl
    have h2 := resetAll k ([false,false,false,b]++S)
    have h := join0 h1 h2
    rw [show 5+(9*k+11)=9*(k+1)+7 by omega] at h
    rw [← List.append_assoc, rotateZ] at h
    -- [01] 000 b = 010 00 b; align the leading reset digit.
    have hz : rep Z (k+1) = rep Z k ++ Z := (rep_snoc Z k).symm
    rw [hz]
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,Z] using h

theorem finish0 (k : Nat) (S : List Bool) :
    run0 table (9*k+13) (E k (false::false::S)) =
      some (B false (rep Z k++[false,true,true]++S)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 11 (E (k+1) (false::false::S)) = some ⟨2,false::L k,[false,false,false,true,true]++S⟩ := by rfl
    have h2 := resetAll k ([false,false,true,true]++S)
    have h := join0 h1 h2
    rw [show 11+(9*k+11)=9*(k+1)+13 by omega] at h
    rw [← List.append_assoc,rotateZ] at h
    have hz : rep Z (k+1) = rep Z k ++ Z := (rep_snoc Z k).symm
    rw [hz]
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,Z] using h

theorem finishBlank (k : Nat) :
    run0 table (9*k+13) (E k []) = some (B false (rep Z k++[false,true,true])) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 11 (E (k+1) []) = some ⟨2,false::L k,[false,false,false,true,true]⟩ := by rfl
    have h2 := resetAll k [false,false,true,true]
    have h := join0 h1 h2
    rw [show 11+(9*k+11)=9*(k+1)+13 by omega] at h
    rw [rotateZ] at h
    have hz : rep Z (k+1) = rep Z k ++ Z := (rep_snoc Z k).symm
    rw [hz]
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,Z] using h

theorem bToggle (R : List Bool) : run0 table 10 (B false R) = some (B true R) := by rfl

theorem bEnter (R : List Bool) (h : R.headD false = false) :
    run0 table 3 (B true R) = some (E 0 R.tail) := by
  cases R with
  | nil => rfl
  | cons x xs => cases x <;> simp_all [List.headD] <;> rfl

theorem bEmpty : run0 table 2 (B true []) = some (D 0) := by rfl

theorem carry (k : Nat) (R : List Bool) (h : R.headD false = false) :
    run0 table 3 (E k (false::true::R)) = some (E (k+1) R.tail) := by
  cases R with
  | nil => rfl
  | cons x xs => cases x <;> simp_all [List.headD] <;> rfl

theorem carryEnd (k : Nat) : run0 table 2 (E k [false,true]) = some (D (k+1)) := by rfl

theorem dEnter (k : Nat) : run0 table 1 (D k) = some (E k []) := by cases k <;> rfl

inductive Digit where | d0 | d1 | d2 | d3 deriving DecidableEq, Repr

def bits : Digit → List Bool
  | .d0 => Z
  | .d1 => [false,false,false]
  | .d2 => [false,true,true]
  | .d3 => [false,false,true]

def word : List Digit → List Bool
  | [] => []
  | d::ds => bits d ++ word ds

def advance : List Digit → Option (List Digit)
  | [] => none
  | .d0::ds => some (.d1::ds)
  | .d1::ds => some (.d2::ds)
  | .d2::ds => some (.d3::ds)
  | .d3::ds => (advance ds).map (Digit.d0::·)

def gap : Digit → Nat
  | .d0 => 3
  | .d1 => 2
  | .d2 => 1
  | .d3 => 0

def remaining : List Digit → Nat
  | [] => 0
  | d::ds => gap d + 4*remaining ds

theorem wordHead (ds : List Digit) : (word ds).headD false = false := by
  cases ds with
  | nil => rfl
  | cons d ds => cases d <;> rfl

theorem advanceRank (ds xs : List Digit) (h : advance ds = some xs) :
    xs.length = ds.length ∧ remaining ds = remaining xs + 1 := by
  induction ds generalizing xs with
  | nil => simp [advance] at h
  | cons d ds ih =>
    cases d with
    | d0 => simp [advance] at h; subst xs; simp [remaining,gap]; omega
    | d1 => simp [advance] at h; subst xs; simp [remaining,gap]; omega
    | d2 => simp [advance] at h; subst xs; simp [remaining,gap]; omega
    | d3 =>
      cases he : advance ds with
      | none => simp [advance,he] at h
      | some ys =>
        simp [advance,he] at h; subst xs
        obtain ⟨hl,hr⟩ := ih ys he
        simp [remaining,gap,hl]
        omega

def target (k : Nat) (ds : List Digit) : Z0 :=
  match advance ds with
  | none => D (k+ds.length)
  | some xs => B false (rep Z k++word xs)

theorem scan (ds : List Digit) (hn : ds ≠ []) (k : Nat) :
    ∃ t, 0<t ∧ run0 table t (E k (word ds).tail) = some (target k ds) := by
  induction ds generalizing k with
  | nil => contradiction
  | cons d ds ih =>
    cases d with
    | d0 => refine ⟨9*k+7,by omega,?_⟩; simpa only [word,bits,Z,target,advance,List.append_assoc,List.cons_append,List.nil_append,List.tail_cons] using finish1 k false (word ds)
    | d1 => refine ⟨9*k+13,by omega,?_⟩; simpa only [word,bits,Z,target,advance,List.append_assoc,List.cons_append,List.nil_append,List.tail_cons] using finish0 k (word ds)
    | d2 => refine ⟨9*k+7,by omega,?_⟩; simpa only [word,bits,Z,target,advance,List.append_assoc,List.cons_append,List.nil_append,List.tail_cons] using finish1 k true (word ds)
    | d3 =>
      cases ds with
      | nil => exact ⟨2,by omega,carryEnd k⟩
      | cons d ds =>
        have h1 := carry k (word (d::ds)) (wordHead (d::ds))
        obtain ⟨t,ht,h2⟩ := ih (by simp) (k+1)
        have h := join0 h1 h2
        have htarg : target (k+1) (d::ds) = target k (.d3::d::ds) := by
          unfold target
          simp only [advance]
          cases he : advance (d::ds) with
          | none => simp only [he,Option.map_none,List.length_cons]; congr 1; omega
          | some xs =>
            simp only [he,Option.map_some,word,bits]
            rw [show rep Z (k+1) = rep Z k ++ Z from (rep_snoc Z k).symm]
            simp only [List.append_assoc]
        rw [htarg] at h
        exact ⟨_,by omega,h⟩

theorem advanceRun (ds : List Digit) : ∃ t, 0<t ∧
    run0 table t (B false (word ds)) = some (target 0 ds) := by
  have h1 := bToggle (word ds)
  cases ds with
  | nil => exact ⟨12,by omega,join0 h1 bEmpty⟩
  | cons d ds =>
    have h2 := bEnter (word (d::ds)) (wordHead (d::ds))
    obtain ⟨t,ht,h3⟩ := scan (d::ds) (by simp) 0
    exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem exhaust (ds : List Digit) : ∃ t, 0<t ∧
    run0 table t (B false (word ds)) = some (D ds.length) := by
  obtain ⟨t,ht,h1⟩ := advanceRun ds
  cases he : advance ds with
  | none =>
    simp [target,he] at h1
    exact ⟨t,ht,h1⟩
  | some xs =>
    obtain ⟨hl,hr⟩ := advanceRank ds xs he
    simp [target,he,rep] at h1
    obtain ⟨u,hu,h2⟩ := exhaust xs
    rw [hl] at h2
    exact ⟨_,by omega,join0 h1 h2⟩
termination_by remaining ds
decreasing_by omega

theorem initialWord (k : Nat) : word (List.replicate k Digit.d0 ++ [.d2]) =
    rep Z k++[false,true,true] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,word,bits,rep,ih,List.append_assoc]

theorem grow (k : Nat) : ∃ t, 0<t ∧ run0 table t (D k) = some (D (k+1)) := by
  have h1 := join0 (dEnter k) (finishBlank k)
  rw [← initialWord] at h1
  obtain ⟨u,hu,h2⟩ := exhaust (List.replicate k Digit.d0 ++ [.d2])
  simp at h2
  exact ⟨_,by omega,join0 h1 h2⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (D k) := by
    intro k
    induction k with
    | zero => exact ⟨13,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow k
      exact ⟨_,by omega,join0 h1 h2⟩
  obtain ⟨t,ht,h1⟩ := h n
  exact ⟨t,D n,ht,h1⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
#print axioms grow
#print axioms arbitrary
end BB6Coverage.Agent4LF1567
