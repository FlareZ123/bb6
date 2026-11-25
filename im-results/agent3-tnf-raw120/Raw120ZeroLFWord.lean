import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120ZeroLFWord
open BB6Coverage BB6Coverage.Agent31Pump

/-- raw120 0LF leaf 3663. B1 is never queried. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev Z (n : Nat) := List.replicate n false

/-- All internal runs have length 3a+2, with gap two or three; a gap-two
    chunk can also carry a short singleton followed by two zeroes.
    Terminal runs have length 3a+1 and arbitrary trailing blank cells. -/
inductive Word where
  | last (a z : Nat)
  | gap2 (a : Nat) (tail : Word)
  | gap3 (a : Nat) (tail : Word)
  | single (a : Nat) (tail : Word)

def rest : Word → List Bool
  | .last a z => O (3*a) ++ Z z
  | .gap2 a w => O (3*a+1) ++ false::false::true::rest w
  | .gap3 a w => O (3*a+1) ++ false::false::false::true::rest w
  | .single a w => O (3*a+1) ++ false::false::true::false::false::true::rest w

def word (w : Word) : List Bool := true::rest w

def Out (r : List Bool) : Prop := ∀ a, ∃ w : Word, O (3*a+2)++r = word w

def Return (R L : List Bool) : Prop :=
  ∃ t out, run0 table t ⟨2,true::L,R⟩ = some ⟨4,L,out⟩ ∧ Out out

theorem longLocal (L R : List Bool) :
    run0 table 5 ⟨2,true::L,true::true::R⟩ = some ⟨4,L,false::false::false::R⟩ := by rfl

theorem longReturn (w : Word) (L : List Bool) : Return (true::true::word w) L := by
  refine ⟨5,false::false::false::word w,longLocal L (word w),?_⟩
  intro a
  exact ⟨.gap3 a w,rfl⟩

theorem readP (L R : List Bool) :
    run0 table 4 ⟨2,true::L,true::false::false::true::R⟩ =
      some ⟨2,true::true::true::false::true::L,R⟩ := by rfl

theorem writeP (L R : List Bool) :
    run0 table 4 ⟨4,true::true::false::true::L,R⟩ =
      some ⟨4,L,false::false::true::true::R⟩ := by rfl

theorem readU (L R : List Bool) :
    run0 table 7 ⟨2,true::L,true::false::false::true::false::false::true::R⟩ =
      some ⟨2,true::true::true::true::true::true::false::true::L,R⟩ := by rfl

theorem writeU (L R : List Bool) :
    run0 table 7 ⟨4,true::true::true::true::true::false::true::L,R⟩ =
      some ⟨4,L,false::false::true::true::true::true::true::R⟩ := by rfl

theorem qLong (L R : List Bool) :
    run0 table 13 ⟨2,true::L,true::false::false::false::true::true::R⟩ =
      some ⟨4,L,false::false::true::false::false::true::true::R⟩ := by rfl

theorem qLast (L : List Bool) (z : Nat) :
    run0 table 13 ⟨2,true::L,true::false::false::false::true::Z z⟩ =
      some ⟨4,L,false::false::true::Z (max 4 (z+3))⟩ := by
  cases z with
  | zero => rfl
  | succ z =>
    rw [show max 4 (z+1+3)=z+4 by omega]
    rfl

theorem lastLocal (L : List Bool) (z : Nat) :
    run0 table 11 ⟨2,true::L,Z z⟩ = some ⟨4,L,O 5++Z (z-4)⟩ := by
  cases z with
  | zero => rfl
  | succ z =>
    cases z with
    | zero => rfl
    | succ z =>
      cases z with
      | zero => rfl
      | succ z =>
        cases z with
        | zero => rfl
        | succ z => rfl

theorem qLongReturn (L R : List Bool) (w : Word) (h : word w = true::true::R) :
    Return (true::false::false::false::word w) L := by
  refine ⟨13,false::false::true::false::false::word w,?_,?_⟩
  · rw [h]; exact qLong L R
  · intro a
    exact ⟨.single a w,rfl⟩

theorem qReturn (w : Word) (L : List Bool) : Return (rest (.gap3 0 w)) L := by
  cases w with
  | last a z =>
    cases a with
    | zero =>
      refine ⟨13,false::false::true::Z (max 4 (z+3)),qLast L z,?_⟩
      intro a
      exact ⟨.gap2 a (.last 0 (max 4 (z+3))),rfl⟩
    | succ a =>
      apply qLongReturn L (O (3*a+2)++Z z) (.last (a+1) z)
      unfold word rest
      rw [show 3*(a+1)=3*a+2+1 by omega]
      rfl
  | gap2 a w =>
    exact qLongReturn L (O (3*a)++false::false::word w) (.gap2 a w) rfl
  | gap3 a w =>
    exact qLongReturn L (O (3*a)++false::false::false::word w) (.gap3 a w) rfl
  | single a w =>
    exact qLongReturn L (O (3*a)++false::false::true::false::false::word w) (.single a w) rfl

theorem core (w : Word) (L : List Bool) : Return (rest w) L := by
  induction w generalizing L with
  | last a z =>
    cases a with
    | zero =>
      refine ⟨11,O 5++Z (z-4),lastLocal L z,?_⟩
      intro a
      refine ⟨.last (a+2) (z-4),?_⟩
      unfold word rest
      rw [← List.append_assoc,List.replicate_append_replicate,show 3*a+2+5=3*(a+2)+1 by omega]
      rfl
    | succ a =>
      have h := longReturn (.last a z) L
      unfold word rest at h
      unfold rest
      rw [show 3*(a+1)=3*a+1+1+1 by omega]
      exact h
  | gap2 a w ih =>
    cases a with
    | zero =>
      obtain ⟨t,r,hr,ho⟩ := ih (true::true::false::true::L)
      have h := join0 (join0 (readP L (rest w)) hr) (writeP L r)
      refine ⟨4+t+4,false::false::true::true::r,h,?_⟩
      intro a
      obtain ⟨v,hv⟩ := ho 0
      refine ⟨.gap2 a v,?_⟩
      have hvr : true::true::r = word v := hv
      change O (3*a+2)++false::false::true::true::r = O (3*a+2)++false::false::word v
      rw [hvr]
    | succ a =>
      have h := longReturn (.gap2 a w) L
      unfold word rest at h
      unfold rest
      rw [show 3*(a+1)+1=3*a+1+1+1+1 by omega]
      exact h
  | gap3 a w ih =>
    cases a with
    | zero => exact qReturn w L
    | succ a =>
      have h := longReturn (.gap3 a w) L
      unfold word rest at h
      unfold rest
      rw [show 3*(a+1)+1=3*a+1+1+1+1 by omega]
      exact h
  | single a w ih =>
    cases a with
    | zero =>
      obtain ⟨t,r,hr,ho⟩ := ih (true::true::true::true::true::false::true::L)
      have h := join0 (join0 (readU L (rest w)) hr) (writeU L r)
      refine ⟨7+t+7,false::false::true::true::true::true::true::r,h,?_⟩
      intro a
      obtain ⟨v,hv⟩ := ho 1
      refine ⟨.gap2 a v,?_⟩
      have hvr : true::true::true::true::true::r = word v := hv
      change O (3*a+2)++false::false::true::true::true::true::true::r = O (3*a+2)++false::false::word v
      rw [hvr]
    | succ a =>
      have h := longReturn (.single a w) L
      unfold word rest at h
      unfold rest
      rw [show 3*(a+1)+1=3*a+1+1+1+1 by omega]
      exact h

def cfg (w : Word) : Z0 := ⟨5,[],false::word w⟩

theorem advance (w : Word) : ∃ t v, 0<t ∧ run0 table t (cfg w) = some (cfg v) := by
  have h1 : run0 table 2 (cfg w) = some ⟨2,[true,true,true],rest w⟩ := by rfl
  obtain ⟨t,r,hr,ho⟩ := core w [true,true]
  obtain ⟨v,hv⟩ := ho 0
  have h2 : run0 table 3 ⟨4,[true,true],r⟩ = some ⟨5,[],false::true::true::r⟩ := by rfl
  refine ⟨2+t+3,v,by omega,?_⟩
  have h := join0 (join0 h1 hr) h2
  have he : true::true::r = word v := hv
  rw [he] at h
  exact h

noncomputable def witness (w : Word) : Nat × Word :=
  let t := Classical.choose (advance w)
  (t,Classical.choose (Classical.choose_spec (advance w)))

theorem witness_ok (w : Word) : 0<(witness w).1 ∧ run0 table (witness w).1 (cfg w) = some (cfg (witness w).2) :=
  Classical.choose_spec (Classical.choose_spec (advance w))
noncomputable def orbit : Nat → Word | 0 => .last 1 0 | n+1 => (witness (orbit n)).2
noncomputable def family (n : Nat) : Z0 := cfg (orbit n)
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => (witness (orbit n)).1) entry
    (fun n => (witness_ok (orbit n)).1) (fun n => (witness_ok (orbit n)).2) m hm
#print axioms never
end BB6.Agent3Raw120ZeroLFWord
