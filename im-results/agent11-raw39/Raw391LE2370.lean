import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LE2370
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev O := rep [true]
abbrev Z := rep [false]
def R (n : Nat) := true::true::O n
abbrev Apre := [true,false,false,false]
abbrev Bpre := [true,true,false,false]
abbrev Cpre := [true,true,false,true,true]
def A (P : List Bool) (n : Nat) : Z0 := ⟨3,Apre++P,R n⟩
def B (P : List Bool) (n : Nat) : Z0 := ⟨3,Bpre++P,R n⟩
def C (P : List Bool) (n : Nat) : Z0 := ⟨3,Cpre++P,R n⟩
inductive Pairs : List Bool → Prop
  | nil : Pairs []
  | zero {P} : Pairs P → Pairs (false::false::P)
  | one {P} : Pairs P → Pairs (true::true::P)

private theorem cOne (L T : List Bool) : run0 table 1 ⟨2,true::L,true::T⟩ = some ⟨2,true::false::L,T⟩ := by rfl
private theorem dOne (L T : List Bool) : run0 table 1 ⟨3,false::L,T⟩ = some ⟨3,L,true::T⟩ := by rfl
private theorem cSweep (n : Nat) (L T : List Bool) :
    run0 table n ⟨2,true::L,O n++T⟩ = some ⟨2,true::(Z n++L),T⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.cons_append,Nat.one_mul] using
    sweepR table 2 [true] [] [true] [false] 1 (by intro L T; exact cOne L T) n L T
private theorem dSweep (n : Nat) (L T : List Bool) :
    run0 table n ⟨3,Z n++L,T⟩ = some ⟨3,L,O n++T⟩ := by
  simpa only [List.nil_append,Nat.one_mul] using
    sweepL table 3 [] [] [false] [true] 1 (by simpa only [List.singleton_append,List.nil_append] using dOne) n L T
private theorem turn (L : List Bool) : run0 table 3 ⟨2,true::L,[]⟩ = some ⟨3,false::false::L,[true]⟩ := by rfl
private theorem back (n : Nat) (L : List Bool) :
    run0 table (n+3+(n+2)) ⟨2,true::L,O n⟩ = some ⟨3,L,O (n+3)⟩ := by
  have h1 := cSweep n L []
  rw [List.append_nil] at h1
  have h2 := turn (Z n++L)
  have h3 := dSweep (n+2) L [true]
  have h4 : O (n+2)++[true] = O (n+3) := by rw [rep_snoc]; rfl
  rw [h4] at h3
  exact join0 (join0 h1 h2) h3

private theorem stageA (P : List Bool) (n : Nat) :
    run0 table 5 (A P n) = some ⟨2,true::(Bpre++P),O (n+1)⟩ := by rfl
private theorem stageB (P : List Bool) (n : Nat) :
    run0 table 14 (B P n) = some ⟨2,true::(Cpre++P),O n⟩ := by rfl
abbrev seed := [false,true,false]
def scan (P : List Bool) (j n : Nat) : Z0 := ⟨1,P,O (j+2)++(seed++R n)⟩
private theorem stageC (P : List Bool) (n : Nat) : run0 table 7 (C P n) = some (scan P 0 n) := by rfl
private theorem scanPair (P : List Bool) (j n : Nat) : run0 table 4 (scan (true::true::P) j n) = some (scan P (j+2) n) := by rfl
private theorem zeroOne (P : List Bool) (j n : Nat) :
    run0 table 1 (scan (false::P) j n) = some ⟨2,[true,true]++P,O (j+1)++(seed++R n)⟩ := by rfl
private theorem oddSix (P : List Bool) (j n : Nat) :
    run0 table 6 (scan (true::false::false::P) j n) = some ⟨2,[true,true,true]++P,O (j+2)++(seed++R n)⟩ := by rfl
private theorem nilSix (j n : Nat) :
    run0 table 6 (scan [true] j n) = some ⟨2,[true,true,true],O (j+2)++(seed++R n)⟩ := by rfl
private theorem finish (P T : List Bool) (j : Nat) :
    run0 table 9 ⟨2,true::(Z (j+1)++true::P),seed++true::true::T⟩ = some ⟨2,true::(Apre++(Z j++true::P)),true::true::T⟩ := by rfl
private theorem reset (P : List Bool) (j n : Nat) :
    ∃ t, 0 < t ∧ run0 table t (scan (false::P) j n) = some (A (Z j++true::P) (n+3)) := by
  have h1 := zeroOne P j n
  have h2 := cSweep (j+1) (true::P) (seed++R n)
  have h3 := finish P (O n) j
  have h4 := back (n+2) (Apre++(Z j++true::P))
  exact ⟨1+(j+1)+9+(n+2+3+(n+2+2)),by omega,join0 (join0 (join0 h1 h2) h3) h4⟩
private theorem resetOdd (P : List Bool) (j n : Nat) :
    ∃ t, 0 < t ∧ run0 table t (scan (true::false::false::P) j n) = some (A (Z j++false::true::true::P) (n+3)) := by
  have h1 := oddSix P j n
  have h2 := cSweep (j+2) (true::true::P) (seed++R n)
  have h3 := finish (true::P) (O n) (j+1)
  have h4 := back (n+2) (Apre++(Z (j+1)++true::true::P))
  have e : Z (j+1)++true::true::P = Z j++false::true::true::P := by
    have h := congrArg (fun L : List Bool => L ++ (true::true::P)) (rep_snoc [false] j).symm
    simpa only [List.append_assoc,rep,List.cons_append,List.nil_append] using h
  refine ⟨6+(j+2)+9+(n+2+3+(n+2+2)),by omega,?_⟩
  rw [← e]
  exact join0 (join0 (join0 h1 h2) h3) h4
private theorem resetNil (j n : Nat) :
    ∃ t, 0 < t ∧ run0 table t (scan [true] j n) = some (A (Z j++[false,true,true]) (n+3)) := by
  have h1 := nilSix j n
  have h2 := cSweep (j+2) [true,true] (seed++R n)
  have h3 := finish [true] (O n) (j+1)
  have h4 := back (n+2) (Apre++(Z (j+1)++[true,true]))
  have e : Z (j+1)++[true,true] = Z j++[false,true,true] := by
    have h := congrArg (fun L : List Bool => L ++ [true,true]) (rep_snoc [false] j).symm
    simpa only [List.append_assoc,rep,List.cons_append,List.nil_append] using h
  refine ⟨6+(j+2)+9+(n+2+3+(n+2+2)),by omega,?_⟩
  rw [← e]
  exact join0 (join0 (join0 h1 h2) h3) h4

-- A low single bit followed by duplicated high bits is an unbounded binary word.
inductive Bits : List Bool → Prop
  | bit (b : Bool) {P} : Pairs P → Bits (b::P)
private theorem prefixPairs (k : Nat) {P : List Bool} (h : Pairs P) : Pairs (Z (2*k)++P) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega]
    exact Pairs.zero ih
private theorem zeroPrefix (k : Nat) {P : List Bool} (h : Pairs P) : Bits (Z (2*k)++false::P) := by
  have e : Z (2*k)++false::P = false::(Z (2*k)++P) := by
    have h := congrArg (fun L : List Bool => L++P) (rep_snoc [false] (2*k))
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h
  rw [e]
  exact Bits.bit false (prefixPairs k h)
private theorem carryOne {P : List Bool} (h : Pairs P) (k n : Nat) :
    ∃ t T, 0 < t ∧ Bits T ∧ run0 table t (scan (true::P) (2*k) n) = some (A T (n+3)) := by
  induction h generalizing k with
  | nil =>
    obtain ⟨t,ht,hr⟩ := resetNil (2*k) n
    exact ⟨t,_,ht,zeroPrefix k (Pairs.one Pairs.nil),hr⟩
  | zero h =>
    obtain ⟨t,ht,hr⟩ := resetOdd _ (2*k) n
    exact ⟨t,_,ht,zeroPrefix k (Pairs.one h),hr⟩
  | @one P h ih =>
    obtain ⟨t,T,ht,hT,hr⟩ := ih (k+1)
    have h1 := scanPair (true::P) (2*k) n
    rw [show 2*k+2=2*(k+1) by omega] at h1
    exact ⟨4+t,T,by omega,hT,join0 h1 hr⟩
private theorem carry {P : List Bool} (h : Bits P) (n : Nat) :
    ∃ t T, 0 < t ∧ Bits T ∧ run0 table t (scan P 0 n) = some (A T (n+3)) := by
  cases h with
  | @bit b P hp =>
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := reset P 0 n
      exact ⟨t,_,ht,Bits.bit true hp,hr⟩
    | true => exact carryOne hp 0 n

inductive Good : Z0 → Prop
  | a (P : List Bool) (n : Nat) : Bits P → Good (A P n)
  | b (P : List Bool) (n : Nat) : Bits P → Good (B P n)
  | c (P : List Bool) (n : Nat) : Bits P → Good (C P n)

theorem next {z : Z0} (h : Good z) : ∃ t z', 0 < t ∧ Good z' ∧ run0 table t z = some z' := by
  cases h with
  | a P n h => exact ⟨_,_,by omega,Good.b P (n+2) h,join0 (stageA P n) (back (n+1) (Bpre++P))⟩
  | b P n h => exact ⟨_,_,by omega,Good.c P (n+1) h,join0 (stageB P n) (back n (Cpre++P))⟩
  | c P n h =>
    obtain ⟨t,T,ht,hT,hr⟩ := carry h n
    exact ⟨7+t,_,by omega,Good.a T (n+3) hT,join0 (stageC P n) hr⟩

private theorem entry : run0 table 53 ⟨0,[],[]⟩ = some (A [true] 4) := by rfl

theorem live (n : Nat) : ∃ k z, n ≤ k ∧ Good z ∧ run0 table k ⟨0,[],[]⟩ = some z := by
  induction n with
  | zero => exact ⟨_,_,Nat.zero_le _,Good.a [true] 4 (Bits.bit true Pairs.nil),entry⟩
  | succ n ih =>
    obtain ⟨k,z,hk,hz,hr⟩ := ih
    obtain ⟨t,z',ht,hz',he⟩ := next hz
    exact ⟨k+t,z',by omega,hz',join0 hr he⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,_,hr⟩ := live n
  have hz : (BB6Coverage.Agent50Zipper.zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms next
#print axioms never
end BB6.Agent11Raw391LE2370
