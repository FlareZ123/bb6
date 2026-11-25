import SweepPumping
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace BB6.Agent3Raw120ZeroLBReset
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaf 38, a two-counter alternating-block reset machine. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev P (n : Nat) := rep [true,false] n

theorem unaryPairs (n : Nat) : rep [true,true] n = O (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2*n+1+1 by omega]
    rfl

theorem unarySingle (n : Nat) : rep [true] n = O n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih]; rfl

theorem readPairs (n : Nat) (R : List Bool) :
    run0 table (6*(n+1)) ⟨2,[],P (n+1)++R⟩ =
      some ⟨2,false::O (2*(n+1)),R⟩ := by
  have h1 : run0 table 6 ⟨2,[],true::false::(P n++R)⟩ =
      some ⟨2,[false,true,true],P n++R⟩ := by rfl
  have h2 := sweepR table 2 [false] [] [true,false] [true,true] 6 (by intro L R; rfl) n [true,true] R
  simp only [List.nil_append,List.cons_append,unaryPairs] at h2
  have h := join0 h1 h2
  rw [show 6+6*n=6*(n+1) by omega] at h
  change run0 table _ _ = some ⟨2,false::(O (2*(n+1))),R⟩
  rw [show 2*(n+1)=2*n+2 by omega]
  rw [show [true,true]=O 2 by rfl,List.replicate_append_replicate] at h
  exact h

theorem writePairs (n : Nat) (R : List Bool) :
    run0 table (2*n) ⟨2,O (2*n),R⟩ = some ⟨2,[],P n++R⟩ := by
  have h := sweepL table 2 [] [] [true,true] [true,false] 2 (by intro L R; rfl) n [] R
  simpa only [List.nil_append,List.append_nil,unaryPairs] using h

theorem growLocal (L R : List Bool) :
    run0 table 9 ⟨2,false::true::true::L,true::true::R⟩ =
      some ⟨2,true::true::true::true::L,true::R⟩ := by rfl

theorem resetLocal (L : List Bool) :
    run0 table 10 ⟨2,false::true::true::L,[true]⟩ =
      some ⟨4,true::true::true::true::true::L,[true]⟩ := by rfl

theorem eSweep (n : Nat) :
    run0 table n ⟨4,O n,[true]⟩ = some ⟨4,[],O (n+1)⟩ := by
  have h := sweepL table 4 [] [] [true] [true] 1 (by intro L R; rfl) n [] [true]
  simp only [Nat.one_mul,List.nil_append,List.append_nil,unarySingle] at h
  rw [show [true]=O 1 by rfl,List.replicate_append_replicate] at h
  exact h

theorem resetFinish (R : List Bool) :
    run0 table 22 ⟨1,[],false::true::true::true::true::R⟩ =
      some ⟨2,[],P 2++true::true::true::R⟩ := by rfl

structure Params where
  k : Nat
  b : Nat

def cfg (x : Params) : Z0 := ⟨2,[],P (x.k+2)++O (x.b+1)⟩
def next (x : Params) : Params :=
  match x.b with
  | 0 => ⟨0,2*x.k+6⟩
  | b+1 => ⟨x.k+1,b⟩
def cost (x : Params) : Nat :=
  match x.b with
  | 0 => 8*x.k+52
  | _+1 => 8*x.k+27

theorem advance (x : Params) : run0 table (cost x) (cfg x) = some (cfg (next x)) := by
  rcases x with ⟨k,b⟩
  cases b with
  | succ b =>
    have h1 := readPairs (k+1) (O (b+2))
    have h2 := growLocal (O (2*k+2)) (O b)
    have h3 := writePairs (k+3) (O (b+1))
    rw [show 2*(k+1+1)=2*k+2+1+1 by omega] at h1
    rw [show 2*(k+3)=2*k+2+1+1+1+1 by omega] at h3
    have h := join0 (join0 h1 h2) h3
    rw [show 6*(k+1+1)+9+(2*k+2+1+1+1+1)=8*k+27 by omega] at h
    exact h
  | zero =>
    have h1 := readPairs (k+1) [true]
    rw [show 2*(k+1+1)=2*k+2+1+1 by omega] at h1
    have h2 := resetLocal (O (2*k+2))
    have h3 := eSweep (2*k+7)
    rw [show 2*k+7=2*k+2+1+1+1+1+1 by omega] at h3
    have h4 : run0 table 1 ⟨4,[],O (2*k+8)⟩ =
        some ⟨1,[],false::O (2*k+8)⟩ := by rfl
    have h5 := resetFinish (O (2*k+4))
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    rw [show 6*(k+1+1)+10+(2*k+2+1+1+1+1+1)+1+22=8*k+52 by omega] at h
    change run0 table _ _ = some ⟨2,[],P 2++O (2*k+6+1)⟩
    rw [show 2*k+6+1=2*k+4+1+1+1 by omega]
    exact h

def orbit : Nat → Params | 0 => ⟨0,2⟩ | n+1 => next (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n)
theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 32 (fun n => cost (orbit n)) entry
    (by intro n; unfold cost; split <;> omega) (fun n => advance (orbit n)) m hm
#print axioms never
end BB6.Agent3Raw120ZeroLBReset
