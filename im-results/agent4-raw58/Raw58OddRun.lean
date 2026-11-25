import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4OddRun
open BB6Coverage Agent31Pump
-- 1RB1LA_1RC1LF_0RD0RF_1LD1RE_1RD0RA_---0LA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def ones (n : Nat) := rep [true] n
def word : List Nat → List Bool
  | [] => [true,true,false,true,true,false,true]
  | a::r => ones (2*a+1) ++ false::word r
def A (m : Nat) (r : List Nat) : Z0 := ⟨0,[],false::(ones (2*m+2)++false::word r)⟩
def scan (m k : Nat) (r : List Nat) : Z0 :=
  ⟨4,(word r).tail.headD false :: (ones (2*k+1)++false::ones (2*m+4)),(word r).tail.tail⟩
theorem repAdd (x : List Bool) (a b : Nat) : rep x (a+b) = rep x a ++ rep x b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega]; simp only [rep,ih,List.append_assoc]
theorem onesAdd (a b : Nat) : ones (a+b) = ones a ++ ones b := repAdd _ _ _
theorem twice (k : Nat) : rep [true,true] k = ones (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 2*(k+1)=2+2*k by omega,onesAdd]; rfl
theorem start (m : Nat) (r : List Nat) : ∃ t, 0<t ∧ run0 table t (A m r) = some (scan m 0 r) := by
  have h1 : run0 table 4 (A m r) = some ⟨0,[false,true,true],false::(ones (2*m)++false::word r)⟩ := by rfl
  have h2 := sweepR table 0 [false] [false] [true,true] [true,true] 4 (by intro L R; rfl) m [true,true] (false::word r)
  rw [twice] at h2
  have h3 : run0 table (4*m) ⟨0,[false,true,true],false::(ones (2*m)++false::word r)⟩ =
      some ⟨0,false::ones (2*m+2),false::false::word r⟩ := by
    rw [onesAdd (2*m) 2,show ones 2 = [true,true] by rfl]
    simpa only [List.cons_append,List.nil_append] using h2
  have h4 : run0 table 4 ⟨0,false::ones (2*m+2),false::false::word r⟩ = some (scan m 0 r) := by
    cases r with
    | nil => rfl
    | cons a r => rfl
  exact ⟨4+4*m+4,by omega,join0 (join0 h1 h3) h4⟩
theorem carry (m k : Nat) (r : List Nat) : run0 table 2 (scan m k (0::r)) = some (scan m (k+1) r) := by
  cases r with
  | nil => rfl
  | cons a r => rfl
theorem stop (m k a : Nat) (r : List Nat) :
    run0 table 5 (scan m k ((a+1)::r)) =
      some ⟨0,ones (2*k+1)++false::ones (2*m+4),false::word (a::r)⟩ := by rfl
theorem exhausted (m k : Nat) : run0 table 37 (scan m k []) =
    some ⟨0,ones (2*(k+2)+1)++false::ones (2*m+4),false::word []⟩ := by rfl
theorem sweep (n : Nat) (L R : List Bool) : run0 table n ⟨0,ones n++L,R⟩ = some ⟨0,L,ones n++R⟩ := by
  have h := sweepL table 0 [] [] [true] [true] 1 (by intro L R; rfl) n L R
  simpa only [Nat.one_mul,ones,List.nil_append] using h
theorem turn (L R : List Bool) : run0 table 3 ⟨0,false::L,true::R⟩ = some ⟨0,L,false::true::R⟩ := by rfl
theorem turnEmpty (R : List Bool) : run0 table 3 ⟨0,[],true::R⟩ = some ⟨0,[],false::true::R⟩ := by rfl
theorem finish (m k : Nat) (r : List Nat) : ∃ t, 0<t ∧
    run0 table t ⟨0,ones (2*k+1)++false::ones (2*m+4),false::word r⟩ = some (A (m+1) (k::r)) := by
  have h1 := sweep (2*k+1) (false::ones (2*m+4)) (false::word r)
  have h2 : run0 table 3 ⟨0,false::ones (2*m+4),word (k::r)⟩ = some ⟨0,ones (2*m+4),false::word (k::r)⟩ := by rfl
  have h3 := sweep (2*m+4) [] (false::word (k::r))
  simp only [List.append_nil] at h3
  have h4 : run0 table 3 ⟨0,[],ones (2*m+4)++false::word (k::r)⟩ = some (A (m+1) (k::r)) := by rfl
  exact ⟨_,by omega,join0 (join0 (join0 h1 h2) h3) h4⟩
theorem returns (m k : Nat) (r : List Nat) : ∃ t s, 0<t ∧ run0 table t (scan m k r) = some (A (m+1) s) := by
  induction r generalizing k with
  | nil =>
    obtain ⟨t,ht,h⟩ := finish m (k+2) []
    exact ⟨37+t,[k+2],by omega,join0 (exhausted m k) h⟩
  | cons a r ih =>
    cases a with
    | zero =>
      obtain ⟨t,s,ht,h⟩ := ih (k+1)
      exact ⟨2+t,s,by omega,join0 (carry m k r) h⟩
    | succ a =>
      obtain ⟨t,ht,h⟩ := finish m k (a::r)
      exact ⟨5+t,k::a::r,by omega,join0 (stop m k a r) h⟩
theorem grow (m : Nat) (r : List Nat) : ∃ t s, 0<t ∧ run0 table t (A m r) = some (A (m+1) s) := by
  obtain ⟨t,ht,h1⟩ := start m r
  obtain ⟨u,s,hu,h2⟩ := returns m 0 r
  exact ⟨t+u,s,by omega,join0 h1 h2⟩
theorem arbitrary (n : Nat) : ∃ t m r, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some (A m r) := by
  induction n with
  | zero => exact ⟨56,1,[],by decide,by rfl⟩
  | succ n ih =>
    obtain ⟨t,m,r,ht,hh⟩ := ih
    obtain ⟨u,s,hu,hg⟩ := grow m r
    exact ⟨t+u,m+1,s,by omega,join0 hh hg⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,k,r,ht,hr⟩ := arbitrary n
    exact ⟨t,A k r,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4OddRun
