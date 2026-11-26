import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent43Raw122Counter17
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev I : List Bool := [false,true,true,false]
abbrev O : List Bool := [true,false,true,true]
abbrev J : List Bool := [true,true,false,false]
abbrev P : List Bool := [false,true,false]

inductive Digit where
  | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7
  deriving DecidableEq

def Digit.bits : Digit → List Bool
  | .d0 => [true,true,false,false]
  | .d1 => [false,true,false,false]
  | .d2 => [true,false,true,false]
  | .d3 => [false,false,true,false]
  | .d4 => [true,true,false,true]
  | .d5 => [false,true,false,true]
  | .d6 => [true,false,true,true]
  | .d7 => [false,false,true,true]

inductive Tail where
  | zero | one
  | digit (d : Digit) (t : Tail)
  deriving DecidableEq

def Tail.bits : Tail → List Bool
  | .zero => [false]
  | .one => [true]
  | .digit d t => d.bits ++ t.bits

def Tail.next : Tail → Tail
  | .zero => .digit .d3 .one
  | .one => .zero
  | .digit .d0 t => .digit .d1 t
  | .digit .d1 t => .digit .d2 t
  | .digit .d2 t => .digit .d3 t
  | .digit .d3 t => .digit .d4 t
  | .digit .d4 t => .digit .d5 t
  | .digit .d5 t => .digit .d6 t
  | .digit .d6 t => .digit .d7 t
  | .digit .d7 t => .digit .d0 t.next

def Tail.cost : Tail → Nat
  | .zero => 16
  | .one => 4
  | .digit .d0 _ | .digit .d2 _ | .digit .d4 _ | .digit .d6 _ => 4
  | .digit .d1 _ | .digit .d5 _ => 12
  | .digit .d3 _ => 16
  | .digit .d7 t => 8 + t.cost + 6

def core (t : Tail) (L : List Bool) : Z0 :=
  ⟨4,t.bits.headD false :: [true,false,true] ++ L,t.bits.tail⟩
def ret (t : Tail) (L : List Bool) : Z0 := ⟨4,[true,true] ++ L,false :: t.bits⟩

theorem core_step (t : Tail) (L : List Bool) :
    run0 table t.cost (core t L) = some (ret t.next L) := by
  induction t generalizing L with
  | zero => rfl
  | one => rfl
  | digit d t ih =>
    cases d with
    | d0 => rfl
    | d1 => rfl
    | d2 => rfl
    | d3 => rfl
    | d4 => rfl
    | d5 => rfl
    | d6 => rfl
    | d7 =>
      have h1 : run0 table 8 (core (.digit .d7 t) L) = some (core t ([true,true,false,true] ++ L)) := by
        cases t <;> rfl
      have h2 := ih ([true,true,false,true] ++ L)
      have h3 : run0 table 6 (ret t.next ([true,true,false,true] ++ L)) = some (ret (.digit .d0 t.next) L) := by rfl
      exact join0 (join0 h1 h2) h3

-- E1 on the left boundary, with a common four-cell prefix repeated k times.
def front (k : Nat) (s : List Bool) : Z0 := ⟨4,[true],P ++ rep I k ++ s⟩
def scan (k : Nat) (s : List Bool) : Z0 := ⟨4,false :: rep O (k+1),s⟩
def back (k : Nat) (s : List Bool) : Z0 := ⟨4,[true,true,true] ++ rep O k,false :: s⟩

theorem start_scan (k : Nat) (s : List Bool) :
    run0 table (5+8*k) (front k s) = some (scan k s) := by
  have h1 : run0 table 5 (front k s) = some ⟨4,[false] ++ O,rep I k ++ s⟩ := by
    rfl
  have h2 := sweepR table 4 [false] [] I O 8 (by intro L R; rfl) k O s
  -- use explicit endpoints to avoid elaboration reducing a symbolic run
  have h2' : run0 table (8*k) ⟨4,[false] ++ O,rep I k ++ s⟩ = some (scan k s) := by
    rw [scan,show rep O (k+1) = rep O k ++ O by rw [rep,rep_snoc]]
    simpa only [List.nil_append,List.singleton_append,List.cons_append] using h2
  exact join0 h1 h2'

theorem finish_back (k : Nat) (s : List Bool) :
    run0 table (6*k+5) (back k s) = some (front k ([false] ++ s)) := by
  have h1 := sweepL table 4 [true,true,true] [false] O J 6 (by intro L R; rfl) k [] s
  have h1' : run0 table (6*k) (back k s) = some ⟨4,[true,true,true],[false] ++ rep J k ++ s⟩ := by
    simpa only [back,List.singleton_append,List.append_nil] using h1
  have h2 : run0 table 5 ⟨4,[true,true,true],[false] ++ rep J k ++ s⟩ = some ⟨4,[true],P ++ [false] ++ rep J k ++ s⟩ := by
    rfl
  have hrot : [false] ++ rep J k = rep I k ++ [false] := rotate false [true,true,false] k
  have h2' : run0 table 5 ⟨4,[true,true,true],[false] ++ rep J k ++ s⟩ = some (front k ([false] ++ s)) := by
    have he : P ++ [false] ++ rep J k ++ s = P ++ rep I k ++ ([false] ++ s) := by
      calc
        _ = P ++ ([false] ++ rep J k) ++ s := by simp only [List.append_assoc]
        _ = _ := by rw [hrot]; simp only [List.append_assoc]
    rw [he] at h2
    exact h2
  exact join0 h1' h2'

def X (k : Nat) (b : Bool) (t : Tail) : Z0 := front k ([true,b] ++ t.bits)
def Y (k : Nat) (b : Bool) (t : Tail) : Z0 := front k ([false,true,false,b] ++ t.bits)

theorem X0 (k : Nat) (t : Tail) : run0 table ((5+8*k)+12+(6*k+5)) (X k false t) = some (Y k true t) := by
  have h1 := start_scan k ([true,false] ++ t.bits)
  have h2 : run0 table 12 (scan k ([true,false] ++ t.bits)) = some (back k ([true,false,true] ++ t.bits)) := by
    rfl
  have h3 := finish_back k ([true,false,true] ++ t.bits)
  exact join0 (join0 h1 h2) h3

theorem YX (k : Nat) (b : Bool) (t : Tail) : run0 table ((5+8*k)+16+(6*k+5)) (Y k b t) = some (X (k+1) b t) := by
  have h1 := start_scan k ([false,true,false,b] ++ t.bits)
  have h2 : run0 table 16 (scan k ([false,true,false,b] ++ t.bits)) = some (back k ([true,true,false,true,b] ++ t.bits)) := by
    rfl
  have h3 : run0 table (6*k+5) (back k ([true,true,false,true,b] ++ t.bits)) = some (X (k+1) b t) := by
    have H := finish_back k ([true,true,false,true,b] ++ t.bits)
    have he : front k ([false] ++ ([true,true,false,true,b] ++ t.bits)) = X (k+1) b t := by
      unfold X
      simp only [front]
      rw [show rep I (k+1) = rep I k ++ I by rw [rep,rep_snoc]]
      simp only [List.append_assoc]
      rfl
    rw [he] at H
    exact H
  exact join0 (join0 h1 h2) h3

theorem X1 (k : Nat) (t : Tail) : run0 table ((5+8*k)+5+t.cost+5+(6*k+5)) (X k true t) = some (Y k false t.next) := by
  have h1 := start_scan k ([true,true] ++ t.bits)
  have h2 : run0 table 5 (scan k ([true,true] ++ t.bits)) = some (core t (rep O (k+1))) := by
    rfl
  have h3 := core_step t (rep O (k+1))
  have h4 : run0 table 5 (ret t.next (rep O (k+1))) = some (back k ([true,false,false] ++ t.next.bits)) := by
    rfl
  have h5 := finish_back k ([true,false,false] ++ t.next.bits)
  exact join0 (join0 (join0 (join0 h1 h2) h3) h4) h5

-- Four boundary returns implement one total digit successor.
def cost (k : Nat) (t : Tail) : Nat := ((5+8*k)+16+(6*k+5)) + ((5+8*(k+1))+12+(6*(k+1)+5)) +
  ((5+8*(k+1))+16+(6*(k+1)+5)) + ((5+8*(k+2))+5+t.cost+5+(6*(k+2)+5))
theorem full (k : Nat) (t : Tail) : run0 table (cost k t) (Y k false t) = some (Y (k+2) false t.next) := by
  exact join0 (join0 (join0 (YX k false t) (X0 (k+1) t)) (YX (k+1) true t)) (X1 (k+2) t)

def iter : Nat → Tail
  | 0 => .digit .d3 .one
  | n+1 => (iter n).next

def family (n : Nat) : Z0 := Y (1+2*n) false (iter n)
theorem entry : run0 table 109 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost (1+2*n) (iter n)) (family n) = some (family (n+1)) := by
  simpa only [family,iter,show 1+2*(n+1)=1+2*n+2 by omega] using full (1+2*n) (iter n)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 109 (fun n => cost (1+2*n) (iter n)) entry
    (by intro n; unfold cost; omega) growth m hm
#print axioms never
end BB6Coverage.Agent43Raw122Counter17
