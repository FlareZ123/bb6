import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M176
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw43 B1=0LE E0=1LA local index 176: F1 uniquely unassigned. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := List.replicate n true

/-- n consecutive right-tape copies of 10, viewed from the head. -/
def pairs : Nat → List Bool
  | 0 => []
  | n+1 => pairs n ++ [true,false]

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  unfold ones
  rw [List.replicate_append_replicate]

theorem pairs_succ_left (n : Nat) :
    pairs (n+1) = true::false::pairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        pairs ((n+1)+1) = pairs (n+1) ++ [true,false] := rfl
        _ = (true::false::pairs n) ++ [true,false] := by rw [ih]
        _ = true::false::(pairs n ++ [true,false]) := by rfl
        _ = true::false::pairs (n+1) := by rfl

/-- Four primitive instructions F0 E1 B0 C1 consume one 10 right block. -/
theorem forward_pair (L R : List Bool) :
    run0 table 4 ⟨5,false::L,true::false::R⟩ =
      some ⟨5,false::true::true::L,R⟩ := by rfl

/-- Two primitive instructions B1 E1 write a right 10 block. -/
theorem backward_pair (L R : List Bool) :
    run0 table 2 ⟨1,true::true::L,R⟩ =
      some ⟨1,L,true::false::R⟩ := by rfl

/-- The reset starts with F0 E0 A0, adding two 1 cells to the left. -/
theorem reset_prefix (n : Nat) :
    run0 table 3 ⟨5,false::ones (2*n),[]⟩ =
      some ⟨1,ones (2*n+2),[]⟩ := by
  have he : ones (2*n+2) = true::true::ones (2*n) := by
    rw [show 2*n+2 = 2+(2*n) by omega,ones_add]
    rfl
  rw [he]
  rfl

/-- Parametric backward B1,E1 sweep, arbitrary tape tails. -/
theorem backward_sweep (n : Nat) (L R : List Bool) :
    run0 table (2*n) ⟨1,ones (2*n)++L,R⟩ =
      some ⟨1,L,pairs n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      have he : ones (2*(n+1)) = true::true::ones (2*n) := by
        rw [show 2*(n+1) = 2+(2*n) by omega,ones_add]
        rfl
      have h1 : run0 table 2 ⟨1,ones (2*(n+1))++L,R⟩ =
          some ⟨1,ones (2*n)++L,true::false::R⟩ := by
        simpa only [he,List.cons_append] using
          backward_pair (ones (2*n)++L) R
      have h := join0 h1 (ih (true::false::R))
      have hn : 2*(n+1) = 2+2*n := by omega
      simpa [hn,pairs,List.append_assoc] using h

/-- B0 C1 finish, returning F0 with two permanent left ones. -/
theorem reset_finish (n : Nat) :
    run0 table 2 ⟨1,[],pairs (n+1)⟩ =
      some ⟨5,false::ones 2,pairs n⟩ := by
  rw [pairs_succ_left]
  rfl

/-- Exact unbounded reset cost 2n+7. -/
theorem reset (n : Nat) :
    run0 table (2*n+7) ⟨5,false::ones (2*n),[]⟩ =
      some ⟨5,false::ones 2,pairs n⟩ := by
  have hmid : run0 table (2*(n+1)) ⟨1,ones (2*n+2),[]⟩ =
      some ⟨1,[],pairs (n+1)⟩ := by
    have he : 2*n+2 = 2*(n+1) := by omega
    simpa only [he,List.append_nil] using backward_sweep (n+1) [] []
  have h := join0 (join0 (reset_prefix n) hmid) (reset_finish n)
  have hn : (3+2*(n+1))+2=2*n+7 := by omega
  simpa only [hn] using h

/-- Exact 4n forward moves across n right blocks, any left tail. -/
theorem forward_sweep (n : Nat) (L : List Bool) :
    run0 table (4*n) ⟨5,false::L,pairs n⟩ =
      some ⟨5,false::ones (2*n)++L,[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
      have h1 : run0 table 4 ⟨5,false::L,pairs (n+1)⟩ =
          some ⟨5,false::true::true::L,pairs n⟩ := by
        rw [pairs_succ_left]
        exact forward_pair L (pairs n)
      have h := join0 h1 (ih (true::true::L))
      have he : ones (2*(n+1)) = ones (2*n) ++ [true,true] := by
        rw [show 2*(n+1) = 2*n+2 by omega,ones_add]
        rfl
      have hn : 4*(n+1) = 4+4*n := by omega
      simpa only [hn,he,List.append_assoc,List.cons_append,List.nil_append] using h

/-- State F on 0, two near-left ones, n right-pair tokens. -/
def phase (n : Nat) : Z0 := ⟨5,false::ones 2,pairs n⟩

/-- An exact growing blank-origin family of F0 sections. -/
theorem growth (n : Nat) :
    run0 table (6*n+9) (phase n) = some (phase (n+1)) := by
  have he : ones (2*n)++ones 2 = ones (2*(n+1)) := by
    rw [←ones_add]
    congr 1
  have h1 : run0 table (4*n) (phase n) =
      some ⟨5,false::ones (2*(n+1)),[]⟩ := by
    simpa only [phase,List.cons_append,he] using forward_sweep n (ones 2)
  have h := join0 h1 (reset (n+1))
  have hn : 4*n+(2*(n+1)+7)=6*n+9 := by omega
  simpa only [hn,phase] using h

/-- Direct exact 41-step blank entry into phase 4. -/
theorem entry :
    run0 table 37 ⟨0,[],[]⟩ = some (phase 3) := by rfl

/-- This is unbounded original-machine execution, not a cutoff. -/
theorem live (N : Nat) :
    ∃ t n, N≤t ∧ run0 table t ⟨0,[],[]⟩=some (phase n) := by
  induction N with
  | zero => exact ⟨37,3,by omega,entry⟩
  | succ N ih =>
      obtain ⟨t,n,ht,h⟩ := ih
      exact ⟨t+(6*n+9),n+1,by omega,join0 h (growth n)⟩

/-- Every one of the 25 total completions of the F1 hole is nonhalting. -/
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

#print axioms reset
#print axioms forward_sweep
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent38M176
