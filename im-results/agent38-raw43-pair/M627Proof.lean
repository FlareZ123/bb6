import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M627
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw43 B1=0LE/E0=1LA local i627, F1 uniquely undefined. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none

/-- Left 00111 packets, nearest-head-first. -/
def block : Nat → List Bool
  | 0 => []
  | n+1 => false::false::true::true::true::block n

/-- Right 01010 packets terminated by the finite 10 pair. -/
def word : Nat → List Bool
  | 0 => [true,false]
  | n+1 => false::true::false::true::false::word n

def front (n : Nat) : List Bool := true::true::block n

/-- B-side inner counter after removing the two leading left zeros. -/
def body (n : Nat) : List Bool := (block n).drop 2

def phase (n : Nat) : Z0 := ⟨5,false::front 0,word n⟩

/-- Five literal instructions F0 C0 D0 D1 B1? (state sequence is
machine-defined); one right 01010 packet creates one left 00111 packet. -/
theorem forward_token (k n : Nat) :
    run0 table 5 ⟨5,false::front k,word (n+1)⟩ =
      some ⟨5,false::front (k+1),word n⟩ := by rfl

/-- Final two-step F0 C1 return consumes right 10 against blank. -/
theorem forward_last (k : Nat) :
    run0 table 2 ⟨5,false::front k,word 0⟩ =
      some ⟨5,false::true::true::front k,[]⟩ := by rfl

theorem forward_many (n k : Nat) :
    run0 table (5*n) ⟨5,false::front k,word n⟩ =
      some ⟨5,false::front (k+n),word 0⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      have h := join0 (forward_token k n) (ih (k+1))
      have ht : 5*(n+1)=5+5*n := by omega
      have hk : k+(n+1)=(k+1)+n := by omega
      simpa only [ht,hk] using h

theorem forward_total (n : Nat) :
    run0 table (5*n+2) (phase n) =
      some ⟨5,false::true::true::front n,[]⟩ := by
  have h0 : run0 table (5*n) (phase n) =
      some ⟨5,false::front n,word 0⟩ := by
    simpa only [phase,Nat.zero_add] using forward_many n 0
  exact join0 h0 (forward_last n)

/-- Fixed 21-transition prefix F0 C0 D0 D0 D1 B1 E0 A1 A1 A0
B1 E1 B1 E1 B1 E1 B1 E0 A0 B1 E1. The consumed left zeros
may be either explicit or implicit, so split on n=0. -/
theorem reset_prefix (n : Nat) :
    run0 table 21 ⟨5,false::true::true::front n,[]⟩ =
      some ⟨1,body n,true::false::word 1⟩ := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- B1 E1 B1 E0 A0 B1 E1 is one seven-move 00111→10010 exchange.
The next two zero cells are allowed to be implicit blank (last block). -/
theorem b_token (n k : Nat) :
    run0 table 7 ⟨1,body (n+1),true::false::word (k+1)⟩ =
      some ⟨1,body n,true::false::word (k+2)⟩ := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- All n B loops, with a freely accumulated right counter k. -/
theorem b_sweep (n k : Nat) :
    run0 table (7*n) ⟨1,body n,true::false::word (k+1)⟩ =
      some ⟨1,[],true::false::word (k+n+1)⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      have h := join0 (b_token n k) (ih (k+1))
      have ht : 7*(n+1)=7+7*n := by omega
      have hk : k+(n+1)+1=(k+1)+n+1 := by omega
      simpa only [ht,hk] using h

/-- Final B0 C1 returns to F0. -/
theorem reset_finish (n : Nat) :
    run0 table 2 ⟨1,[],true::false::word (n+1)⟩ =
      some (phase (n+1)) := by rfl

/-- Reset cost 7n+23, regardless of input counter magnitude. -/
theorem reset (n : Nat) :
    run0 table (7*n+23) ⟨5,false::true::true::front n,[]⟩ =
      some (phase (n+1)) := by
  have sweep : run0 table (7*n) ⟨1,body n,true::false::word 1⟩ =
      some ⟨1,[],true::false::word (n+1)⟩ := by
    simpa only [Nat.zero_add] using b_sweep n 0
  have h := join0 (join0 (reset_prefix n) sweep)
    (reset_finish n)
  have ht : (21+7*n)+2=7*n+23 := by omega
  simpa only [ht,Nat.zero_add] using h

/-- Exact positive growth for all n, no cutoff. -/
theorem growth (n : Nat) :
    run0 table (12*n+25) (phase n) = some (phase (n+1)) := by
  have h := join0 (forward_total n) (reset n)
  have ht : (5*n+2)+(7*n+23)=12*n+25 := by omega
  simpa only [ht] using h

/-- Authentic blank entry: 17 primitive transitions reach phase0. -/
theorem entry :
    run0 table 17 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem live (N : Nat) :
    ∃ t n, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some (phase n) := by
  induction N with
  | zero => exact ⟨17,0,by omega,entry⟩
  | succ N ih =>
      obtain ⟨t,n,ht,h⟩ := ih
      exact ⟨t+(12*n+25),n+1,by omega,join0 h (growth n)⟩

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

#print axioms forward_token
#print axioms reset_prefix
#print axioms b_token
#print axioms b_sweep
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent38M627
