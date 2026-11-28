import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M905
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw43 B1=0LE/E0=1LA local i905, unique missing C1. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,3⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def p001 : Nat → List Bool
  | 0 => []
  | n+1 => false::false::true::p001 n

def p010 : Nat → List Bool
  | 0 => []
  | n+1 => p010 n ++ [false,true,false]

def word : Nat → List Bool
  | 0 => [true]
  | n+1 => true::false::false::word n

def fshape (n : Nat) : List Bool :=
  [false,false,true,false] ++ p010 n ++ [false,true,true]

def dshape (n : Nat) : List Bool := p010 n ++ [false,true,true]

def phase (n : Nat) : Z0 := ⟨5,[false,true,true],word n⟩

theorem word_seq (n : Nat) : word n = true::p001 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [word,p001,ih]

theorem p010_succ_left (n : Nat) :
    p010 (n+1) = [false,true,false]++p010 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        p010 ((n+1)+1) = p010 (n+1)++[false,true,false] := rfl
        _ = ([false,true,false]++p010 n)++[false,true,false] := by rw [ih]
        _ = [false,true,false]++p010 (n+1) := by
          simp only [p010,List.append_assoc]

/-- The first 4 steps examine the right 1 and a first 001 packet. -/
theorem first_four_zero :
    run0 table 4 (phase 0) =
      some ⟨3,fshape 0,[]⟩ := by rfl

theorem first_four_succ (n : Nat) :
    run0 table 4 (phase (n+1)) =
      some ⟨3,[true,false,true,false,false,true,true],p001 n⟩ := by
  rw [show word (n+1) = [true,false,false,true]++p001 n from by
    rw [word,word_seq n];rfl]
  rfl

/-- D1 B0 C0: consume a right 001 token and extend left by 010. -/
theorem forward_token (L R : List Bool) :
    run0 table 3 ⟨3,true::L,p001 1++R⟩ =
      some ⟨3,true::false::true::false::L,R⟩ := by rfl

/-- Final D1 B0 C0, reading only implicit blank right bits. -/
theorem forward_end (L : List Bool) :
    run0 table 3 ⟨3,true::L,[]⟩ =
      some ⟨3,[false,false,true,false]++L,[]⟩ := by rfl

/-- An arbitrary number of 001 packet moves plus the final blank read. -/
theorem forward_sweep (n : Nat) (L : List Bool) :
    run0 table (3*(n+1)) ⟨3,true::L,p001 n⟩ =
      some ⟨3,[false,false,true,false]++p010 n++L,[]⟩ := by
  induction n generalizing L with
  | zero => exact forward_end L
  | succ n ih =>
      have h1 : run0 table 3 ⟨3,true::L,p001 (n+1)⟩ =
          some ⟨3,true::([false,true,false]++L),p001 n⟩ := by
        simpa only [p001,List.cons_append] using forward_token L (p001 n)
      have h := join0 h1 (ih ([false,true,false]++L))
      have ht : 3*((n+1)+1)=3+3*(n+1) := by omega
      have hp : p010 (n+1) = p010 n++[false,true,false] := rfl
      simpa only [ht,hp,List.append_assoc,List.cons_append] using h

/-- Total forward phase, exactly 3n+4 steps and a blank right ray. -/
theorem forward (n : Nat) :
    run0 table (3*n+4) (phase n) =
      some ⟨3,fshape n,[]⟩ := by
  cases n with
  | zero => exact first_four_zero
  | succ n =>
      have h := join0 (first_four_succ n)
        (forward_sweep n [false,true,false,false,true,true])
      have ht : 3*(n+1)+4=4+3*(n+1) := by omega
      have hp : [false,true,false,false,true,true] =
          [false,true,false]++[false,true,true] := by rfl
      simpa only [ht,fshape,p010,p001,hp,List.append_assoc] using h

/-- Fixed 8-step D0 D0 D1 B1 E0 A0 B1 E1, prepends right 1001. -/
theorem backward_first (L : List Bool) :
    run0 table 8 ⟨3,[false,false,true,false]++L,[]⟩ =
      some ⟨3,L,word 1⟩ := by rfl

/-- Seven-step D0 D1 B1 E0 A0 B1 E1, erase left 010 and prepend 100. -/
theorem backward_token (L R : List Bool) :
    run0 table 7 ⟨3,[false,true,false]++L,R⟩ =
      some ⟨3,L,[true,false,false]++R⟩ := by rfl

/-- Parametric backward packet sweep, with arbitrary saved right counter. -/
theorem backward_sweep (n k : Nat) :
    run0 table (7*n) ⟨3,dshape n,word (k+1)⟩ =
      some ⟨3,dshape 0,word (k+n+1)⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      have hs : dshape (n+1) = [false,true,false]++dshape n := by
        simp only [dshape,p010_succ_left,List.append_assoc]
      have h1 : run0 table 7 ⟨3,dshape (n+1),word (k+1)⟩ =
          some ⟨3,dshape n,word ((k+1)+1)⟩ := by
        rw [hs]
        simpa only [word,List.cons_append] using
          backward_token (dshape n) (word (k+1))
      have h := join0 h1 (ih (k+1))
      have ht : 7*(n+1)=7+7*n := by omega
      have hk : k+(n+1)+1=(k+1)+n+1 := by omega
      simpa only [ht,hk] using h

/-- Fixed final six-step D0 D1 B1 E0 A1 F1, right suffix unchanged. -/
theorem backward_finish (n : Nat) :
    run0 table 6 ⟨3,dshape 0,word (n+1)⟩ =
      some (phase (n+1)) := by rfl

/-- Total backward cost: eight-step prelude, 7n loop, six-step finale. -/
theorem backward (n : Nat) :
    run0 table (7*n+14) ⟨3,fshape n,[]⟩ =
      some (phase (n+1)) := by
  have he : fshape n = [false,false,true,false]++dshape n := by
    rfl
  have h1 : run0 table 8 ⟨3,fshape n,[]⟩ =
      some ⟨3,dshape n,word 1⟩ := by
    rw [he]
    exact backward_first (dshape n)
  have h := join0 (join0 h1 (backward_sweep n 0))
    (backward_finish n)
  have ht : (8+7*n)+6=7*n+14 := by omega
  simpa only [ht,Nat.zero_add] using h

/-- Every n increases by one in exactly 10n+18 raw transitions. -/
theorem growth (n : Nat) :
    run0 table (10*n+18) (phase n) = some (phase (n+1)) := by
  have h := join0 (forward n) (backward n)
  have ht : (3*n+4)+(7*n+14)=10*n+18 := by omega
  simpa only [ht] using h

/-- Authentic blank entry: 10 raw steps reach phase zero. -/
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem live (N : Nat) :
    ∃ t n, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some (phase n) := by
  induction N with
  | zero => exact ⟨10,0,by omega,entry⟩
  | succ N ih =>
      obtain ⟨t,n,ht,h⟩ := ih
      exact ⟨t+(10*n+18),n+1,by omega,join0 h (growth n)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,ht,hr⟩ := live n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some (phase k) :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
      have H := zrun_sound table m hm t s z' hZ
      have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
      rw [hb] at H
      rw [show t=n+(t-n) by omega,run_append] at H
      cases he : run m n blank with
      | none => simp [he] at H
      | some c => rfl

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms forward_sweep
#print axioms backward_sweep
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent38M905
