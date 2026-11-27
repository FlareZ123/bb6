import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M59
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw43 B1=0LE E0=1LA local i59, uniquely undefined F1. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | _,_ => none

/-- Zero-one alternating code, near-head-first. -/
def alt : Nat → List Bool
  | 0 => []
  | n+1 => false::true::alt n

theorem alt_succ_right (n : Nat) :
    alt (n+1) = alt n ++ [false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        alt ((n+1)+1) = false::true::alt (n+1) := rfl
        _ = false::true::(alt n ++ [false,true]) := by rw [ih]
        _ = alt (n+1) ++ [false,true] := by rfl

/-- Right word 1(01)^n; one trailing 1 is crucial (not an extra 0). -/
def word (n : Nat) : List Bool := true :: alt n

/-- Left word 11(01)^n1; the scanned cell is a separate initial 0. -/
def front (n : Nat) : List Bool := true::true::(alt n ++ [true])

/-- Exact blank-origin recurrence sections. -/
def phase (n : Nat) : Z0 := ⟨5,false::front 0,word n⟩

/-- Four instructions F0 D1 B0 C1; consume right 10, add one left 01. -/
theorem forward_step (k n : Nat) :
    run0 table 4 ⟨5,false::front k,word (n+1)⟩ =
      some ⟨5,false::front (k+1),word n⟩ := by rfl

/-- Final right 1 is consumed against the implicit blank zero. -/
theorem forward_final (k : Nat) :
    run0 table 4 ⟨5,false::front k,word 0⟩ =
      some ⟨5,false::front (k+1),[]⟩ := by rfl

theorem forward_many (n k : Nat) :
    run0 table (4*n) ⟨5,false::front k,word n⟩ =
      some ⟨5,false::front (k+n),word 0⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      have h := join0 (forward_step k n) (ih (k+1))
      have ht : 4*(n+1)=4+4*n := by omega
      have hk : k+(n+1)=(k+1)+n := by omega
      simpa only [ht,hk] using h

/-- All n right pairs plus the final 1, cost exactly 4(n+1). -/
theorem forward_total (n : Nat) :
    run0 table (4*(n+1)) (phase n) =
      some ⟨5,false::front (n+1),[]⟩ := by
  have h0 : run0 table (4*n) (phase n) =
      some ⟨5,false::front n,word 0⟩ := by
    simpa only [phase,Nat.zero_add] using forward_many n 0
  have h := join0 h0 (forward_final n)
  have ht : 4*(n+1)=4*n+4 := by omega
  simpa only [ht] using h

/-- Reset intermediate D-head shape 0010101(01)^n1. -/
def dshape (n : Nat) : List Bool :=
  false::false::true::false::true::false::true::(alt n ++ [true])

/-- Exact four-instruction reset prefix F0 D1 B0 C0. -/
theorem reset_prefix (n : Nat) :
    run0 table 4 ⟨5,false::front (n+1),[]⟩ =
      some ⟨3,dshape n,[]⟩ := by rfl

/-- Eight instructions D0 D0 D1 B1 E0 A0 B1 E1; one 10 removed
from left, one 01 written to the right, with arbitrary right tail. -/
theorem d_step (n : Nat) (R : List Bool) :
    run0 table 8 ⟨3,dshape (n+1),R⟩ =
      some ⟨3,dshape n,false::true::R⟩ := by rfl

/-- Base sixteen transitions for the last two 10 blocks. -/
theorem d_base (R : List Bool) :
    run0 table 16 ⟨3,dshape 0,R⟩ =
      some ⟨3,[false,false,true,true],alt 2 ++ R⟩ := by rfl

/-- Entire unbounded backward reset: cost 8n+16, exact 01 packets. -/
theorem d_sweep (n : Nat) (R : List Bool) :
    run0 table (8*n+16) ⟨3,dshape n,R⟩ =
      some ⟨3,[false,false,true,true],alt (n+2)++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      have h := join0 (d_step n R) (ih (false::true::R))
      have ht : 8*(n+1)+16=8+(8*n+16) := by omega
      have ha : alt ((n+1)+2)=alt (n+2)++[false,true] := by
        rw [show (n+1)+2=(n+2)+1 by omega,alt_succ_right]
      simpa only [ht,ha,List.append_assoc,List.cons_append,List.nil_append] using h

/-- Final nine instructions D0 D0 D1 B1 E0 A1 A0 B0 C1. -/
theorem reset_finish (R : List Bool) :
    run0 table 9 ⟨3,[false,false,true,true],R⟩ =
      some ⟨5,false::front 0,true::R⟩ := by rfl

/-- Exact 8n+29 backward reset, producing two more 01-pairs. -/
theorem reset (n : Nat) :
    run0 table (8*n+29) ⟨5,false::front (n+1),[]⟩ =
      some (phase (n+2)) := by
  have hmid : run0 table (8*n+16) ⟨3,dshape n,[]⟩ =
      some ⟨3,[false,false,true,true],alt (n+2)⟩ := by
    simpa only [List.append_nil] using d_sweep n []
  have h := join0 (join0 (reset_prefix n) hmid)
    (reset_finish (alt (n+2)))
  have ht : (4+(8*n+16))+9=8*n+29 := by omega
  simpa only [ht,phase,word] using h

/-- Complete positive-cost first-order growth, n to n+2. -/
theorem growth (n : Nat) :
    run0 table (12*n+33) (phase n) = some (phase (n+2)) := by
  have h := join0 (forward_total n) (reset n)
  have ht : 4*(n+1)+(8*n+29)=12*n+33 := by omega
  simpa only [ht] using h

/-- Authentic blank tape enters phase(0) after 12 raw instructions. -/
theorem entry :
    run0 table 12 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem live (N : Nat) :
    ∃ t n, N≤t ∧ run0 table t ⟨0,[],[]⟩=some (phase n) := by
  induction N with
  | zero => exact ⟨12,0,by omega,entry⟩
  | succ N ih =>
      obtain ⟨t,n,ht,h⟩ := ih
      exact ⟨t+(12*n+33),n+2,by omega,join0 h (growth n)⟩

/-- All 25 physical F1 completions have infinite defined blank runs. -/
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

#print axioms forward_step
#print axioms forward_final
#print axioms d_step
#print axioms d_sweep
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent38M59
