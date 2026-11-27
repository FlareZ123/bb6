import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31Raw55REQuartet
open BB6Coverage BB6Coverage.Agent31Pump
inductive Kind where | a | b | c | d
def table_a : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
def table_b : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
def table_c : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
def table_d : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
def table : Kind → PartialMachine
  | .a => table_a
  | .b => table_b
  | .c => table_c
  | .d => table_d

def z (n : Nat) : List Bool := rep [false] n
def sec (r : List Bool) : Z0 := ⟨0,[false,false],[false,false,false] ++ r⟩
def scan (n : Nat) (r : List Bool) : Z0 := ⟨4,true :: z (n+2) ++ [true,false],r⟩
def cut : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::r => (0,r)
  | true::r => let c := cut r; (c.1+1,c.2)
def next (r : List Bool) : List Bool := z (cut r).1 ++ true::(cut r).2
def cost (r : List Bool) : Nat := 16 + 2*(cut r).1

theorem z_snoc (n : Nat) : z n ++ [false] = z (n+1) := rep_snoc [false] n

theorem prep (k : Kind) (r : List Bool) : run0 (table k) 7 (sec r) = some (scan 0 r) := by cases k <;> rfl

theorem scan_one (k : Kind) (n : Nat) (r : List Bool) :
    run0 (table k) 1 (scan n (true::r)) = some (scan (n+1) r) := by cases k <;> rfl

theorem stop_false (k : Kind) (n : Nat) (r : List Bool) :
    run0 (table k) 2 (scan n (false::r)) = some ⟨5,z (n+3) ++ [true,false],true::r⟩ := by cases k <;> rfl

theorem stop_nil (k : Kind) (n : Nat) :
    run0 (table k) 2 (scan n []) = some ⟨5,z (n+3) ++ [true,false],[true]⟩ := by cases k <;> rfl

theorem drain (k : Kind) (n : Nat) (r : List Bool) :
    run0 (table k) n ⟨5,z n ++ [true,false],r⟩ = some ⟨5,[true,false],z n ++ r⟩ := by
  have h := sweepL (table k) 5 [] [] [false] [false] 1 (by intro L R; cases k <;> rfl) n [true,false] r
  simpa only [Nat.one_mul,List.nil_append,z] using h

theorem finish (k : Kind) (n : Nat) (r : List Bool) :
    run0 (table k) (n+7) ⟨5,z (n+3) ++ [true,false],true::r⟩ = some (sec (z n ++ true::r)) := by
  have h1 := drain k (n+3) (true::r)
  have h2 : run0 (table k) 4 ⟨5,[true,false],z (n+3) ++ true::r⟩ = some (sec (z n ++ true::r)) := by
    cases k <;> rfl
  have h := join0 h1 h2
  rw [show n+3+4=n+7 by omega] at h
  exact h

theorem scan_all (k : Kind) (n : Nat) (r : List Bool) :
    run0 (table k) (n+2*(cut r).1+9) (scan n r) = some (sec (z (n+(cut r).1) ++ true::(cut r).2)) := by
  induction r generalizing n with
  | nil =>
    have h := join0 (stop_nil k n) (finish k n [])
    simpa [cut,show 2+(n+7)=n+9 by omega] using h
  | cons b r ih =>
    cases b with
    | false =>
      have h := join0 (stop_false k n r) (finish k n r)
      simpa [cut,show 2+(n+7)=n+9 by omega] using h
    | true =>
      have h := join0 (scan_one k n r) (ih (n+1))
      simp only [cut]
      rw [show n+((cut r).1+1)=n+1+(cut r).1 by omega]
      rw [show n+2*((cut r).1+1)+9=1+(n+1+2*(cut r).1+9) by omega]
      exact h

theorem epoch (k : Kind) (r : List Bool) : run0 (table k) (cost r) (sec r) = some (sec (next r)) := by
  have h := join0 (prep k r) (scan_all k 0 r)
  unfold cost next
  simp only [Nat.zero_add] at h
  rw [show 16+2*(cut r).1=7+(2*(cut r).1+9) by omega]
  exact h

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => next (orbit n)
theorem first (k : Kind) : run0 (table k) 16 ⟨0,[],[]⟩ = some (sec (orbit 0)) := by cases k <;> rfl

theorem never (k : Kind) (m : Machine) (hm : compatible (table k) m) : NeverHalts m :=
  never_of_growth (table k) (fun n => sec (orbit n)) 16 (fun n => cost (orbit n)) (first k)
    (by intro n; unfold cost; omega) (fun n => epoch k (orbit n)) m hm
#print axioms never
end BB6.Agent31Raw55REQuartet
