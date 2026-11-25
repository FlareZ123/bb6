import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120OneRCCounter
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaf 939, E0=1RC. All growth phases avoid the undefined F0. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n

theorem consume (a : Nat) (L R : List Bool) :
  run0 table 7 ⟨2,O (a+2)++L,true::false::true::R⟩ =
    some ⟨2,O (a+3)++L,true::false::R⟩ := by rfl

theorem consumeAll (x a : Nat) (L R : List Bool) :
  run0 table (7*x) ⟨2,O (a+2)++L,true::false::(O x++R)⟩ =
    some ⟨2,O (a+x+2)++L,true::false::R⟩ := by
  induction x generalizing a with
  | zero => simp [O,rep,run0]
  | succ x ih =>
    have h := join0 (consume a L (O x++R)) (ih (a+1))
    rw [show 7*(x+1)=7+7*x by omega, ← show a+1+x+2=a+(x+1)+2 by omega]
    exact h

theorem bridge (a : Nat) (L R : List Bool) :
  run0 table 4 ⟨2,O (a+2)++L,true::false::false::true::true::R⟩ =
    some ⟨2,O 4++false::(O (a+1)++L),true::R⟩ := by rfl

theorem terminal (a : Nat) (L : List Bool) :
  run0 table 13 ⟨2,O (a+2)++L,[true,false]⟩ =
    some ⟨2,O (a+3)++L,O 4⟩ := by rfl

theorem resetPrefix (a : Nat) (L R : List Bool) :
  run0 table 6 ⟨2,O (a+2)++L,true::true::R⟩ =
    some ⟨4,O (a+2)++L,false::true::R⟩ := by rfl

theorem resetSweep (L R : List Bool) :
  run0 table 1 ⟨4,true::L,R⟩ = some ⟨4,L,true::R⟩ := by rfl

theorem sweep (a : Nat) (L R : List Bool) :
  run0 table a ⟨4,O a++L,R⟩ = some ⟨4,L,O a++R⟩ := by
  simpa [O] using sweepL table 4 [] [] [true] [true] 1 (by
    intro L R; exact resetSweep L R) a L R

theorem resetLast (a : Nat) (L R : List Bool) :
  run0 table 1 ⟨4,false::L,O (a+2)++false::true::R⟩ =
    some ⟨2,true::true::L,O (a+1)++false::true::R⟩ := by rfl

theorem reset (a : Nat) (L R : List Bool) :
  run0 table (a+9) ⟨2,O (a+2)++false::L,true::true::R⟩ =
    some ⟨2,true::true::L,O (a+1)++false::true::R⟩ := by
  have h := join0 (join0 (resetPrefix a (false::L) R) (sweep (a+2) (false::L) (false::true::R))) (resetLast a L R)
  simpa only [show 6+(a+2)+1=a+9 by omega] using h

theorem resetEnd (a : Nat) (R : List Bool) :
  run0 table (a+9) ⟨2,O (a+2),true::true::R⟩ =
    some ⟨2,O 2,O (a+1)++false::true::R⟩ := by
  have h : run0 table 1 ⟨4,[],O (a+2)++false::true::R⟩ =
    some ⟨2,O 2,O (a+1)++false::true::R⟩ := by rfl
  have hh := join0 (join0 (resetPrefix a [] R) (sweep (a+2) [] (false::true::R))) h
  simpa only [List.append_nil,show 6+(a+2)+1=a+9 by omega] using hh

/-- An unpaired run has length at least three; a paired run has
    length two followed by an arbitrary positive run. -/
inductive Token where
  | large : Nat → Token
  | pair : Nat → Token

def enc : List Token → List Bool
  | [] => []
  | .large k :: xs => false :: (O (k+3) ++ enc xs)
  | .pair k :: xs => false :: (O 2 ++ false :: (O (k+1) ++ enc xs))

def advance : List Token → List Token
  | [] => [.large 0]
  | .large k :: xs => .pair k :: xs
  | .pair k :: xs => .large (k+1) :: advance xs

def result (xs : List Token) : List Bool := true :: (enc (advance xs)).tail

theorem result_split (xs : List Token) : ∃ R, result xs = true::true::R := by
  cases xs with
  | nil => exact ⟨_,rfl⟩
  | cons tok xs => cases tok <;> exact ⟨_,rfl⟩

theorem result_enc (xs : List Token) : false :: (result xs).tail = enc (advance xs) := by
  cases xs with
  | nil => rfl
  | cons tok xs => cases tok <;> rfl

/-- The complete rightward scan and return, with arbitrary untouched left suffix. -/
theorem process (xs : List Token) (a x : Nat) (L : List Bool) :
    ∃ t, 0 < t ∧ run0 table t ⟨2,O (a+2)++L,true::false::(O x++enc xs)⟩ =
      some ⟨2,O (a+x+3)++L,result xs⟩ := by
  induction xs generalizing a x L with
  | nil =>
    refine ⟨7*x+13,by omega,?_⟩
    exact join0 (consumeAll x a L []) (terminal (a+x) L)
  | cons tok xs ih =>
    cases tok with
    | large k =>
      refine ⟨7*x+4+11,by omega,?_⟩
      have h1 := consumeAll x a L (enc (.large k::xs))
      have h2 := bridge (a+x) L (O (k+1)++enc xs)
      have h3 := reset 2 (O (a+x+1)++L) (O k++enc xs)
      exact join0 (join0 h1 h2) h3
    | pair k =>
      have h1 := consumeAll x a L (enc (.pair k::xs))
      have h2 := bridge (a+x) L (false::(O (k+1)++enc xs))
      obtain ⟨t,ht,h3⟩ := ih 2 (k+1) (false::(O (a+x+1)++L))
      obtain ⟨R,hR⟩ := result_split xs
      rw [hR,show 2+(k+1)+3=k+4+2 by omega] at h3
      have h4 := reset (k+4) (O (a+x+1)++L) R
      refine ⟨7*x+4+t+(k+4+9),by omega,?_⟩
      have h := join0 (join0 (join0 h1 h2) h3) h4
      have hr := result_enc xs
      rw [hR] at hr
      rw [show k+4+1=(k+1+3)+1 by omega] at h
      change run0 table (7*x+4+t+(k+4+9)) _ = some ⟨2,O (a+x+3)++L,true::(O (k+1+3)++enc (advance xs))⟩
      rw [← hr]
      exact h

def cfg (n : Nat) (xs : List Token) : Z0 := ⟨2,O 2,O (n+3)++enc xs⟩

theorem growth (n : Nat) (xs : List Token) : ∃ t, 0<t ∧
    run0 table t (cfg n xs) = some (cfg (n+1) (advance xs)) := by
  have h1 := resetEnd 0 (O (n+1)++enc xs)
  obtain ⟨t,ht,h2⟩ := process xs 0 (n+2) []
  obtain ⟨R,hR⟩ := result_split xs
  rw [hR] at h2
  have h3 := resetEnd (n+3) R
  refine ⟨9+t+(n+3+9),by omega,?_⟩
  have h2' : run0 table t ⟨2,O 2,true::false::(O (n+2)++enc xs)⟩ =
      some ⟨2,O (n+5),true::true::R⟩ := by
    simpa only [Nat.zero_add,List.append_nil] using h2
  have h := join0 (join0 h1 h2') h3
  have hr := result_enc xs
  rw [hR] at hr
  unfold cfg
  rw [show n+1+3=n+3+1 by omega,← hr]
  exact h

def tokens : Nat → List Token
  | 0 => []
  | n+1 => advance (tokens n)
def family (n : Nat) : Z0 := cfg n (tokens n)
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
noncomputable def cost (n : Nat) := Classical.choose (growth n (tokens n))
theorem cost_pos (n : Nat) : 0 < cost n := (Classical.choose_spec (growth n (tokens n))).1
theorem step (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) :=
  (Classical.choose_spec (growth n (tokens n))).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 cost entry cost_pos step m hm
#print axioms process
#print axioms growth
#print axioms entry
#print axioms never
end BB6.Agent3Raw120OneRCCounter
