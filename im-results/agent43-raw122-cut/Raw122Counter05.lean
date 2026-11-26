import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace BB6Coverage.Agent43Raw122Counter05
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

inductive Variant where
  | le0 | lf0 | ld1 | rd1
  deriving DecidableEq

def Variant.c1 : Variant → Move
  | .le0 => ⟨false,false,4⟩
  | .lf0 => ⟨false,false,5⟩
  | .ld1 => ⟨true,false,3⟩
  | .rd1 => ⟨true,true,3⟩

def table (v : Variant) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some v.c1)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev I : List Bool := [true,false]
abbrev O : List Bool := [false,true]
abbrev carry : List Bool := [true,false,true,true,true]

inductive Tail where
  | terminal
  | d0 (t : Tail)
  | d1 (t : Tail)
  | d2 (t : Tail)
  deriving DecidableEq

def Tail.bits : Tail → List Bool
  | .terminal => [false,false,false,true]
  | .d0 t => [false,false,true,false,false] ++ t.bits
  | .d1 t => [false,false,false,false,false] ++ t.bits
  | .d2 t => [false,false,false,true,false] ++ t.bits

def Tail.next : Tail → Tail
  | .terminal => .d0 .terminal
  | .d0 t => .d1 t
  | .d1 t => .d2 t
  | .d2 t => .d0 t.next

def Variant.cost0 : Variant → Nat
  | .le0 | .lf0 => 7
  | .ld1 => 9
  | .rd1 => 11

def Tail.cost (v : Variant) : Tail → Nat
  | .terminal => 21
  | .d0 _ => v.cost0
  | .d1 _ => 11
  | .d2 t => 5 + t.cost v + 5

def core (t : Tail) (L : List Bool) : Z0 := ⟨4,false :: L,t.bits⟩
def ret (t : Tail) (L : List Bool) : Z0 := ⟨5,L,false :: t.bits⟩

theorem core_step (v : Variant) (t : Tail) (L : List Bool) :
    run0 (table v) (t.cost v) (core t L) = some (ret t.next L) := by
  induction t generalizing L with
  | terminal => cases v <;> rfl
  | d0 t => cases v <;> rfl
  | d1 t => cases v <;> rfl
  | d2 t ih =>
    have h1 : run0 (table v) 5 (core (.d2 t) L) = some (core t (carry ++ L)) := by cases v <;> rfl
    have h2 := ih (carry ++ L)
    have h3 : run0 (table v) 5 (ret t.next (carry ++ L)) = some (ret (.d0 t.next) L) := by cases v <;> rfl
    exact join0 (join0 h1 h2) h3

def front (k : Nat) (t : Tail) : Z0 := ⟨4,[],rep I (k+1) ++ t.bits⟩

theorem scan (v : Variant) (k : Nat) (t : Tail) :
    run0 (table v) (2+2*k) (front k t) = some (core t (rep O (k+1))) := by
  have h1 : run0 (table v) 2 (front k t) = some ⟨4,[false] ++ O,rep I k ++ t.bits⟩ := by cases v <;> rfl
  have h2 := sweepR (table v) 4 [false] [] I O 2 (by intro L R; cases v <;> rfl) k O t.bits
  have h2' : run0 (table v) (2*k) ⟨4,[false] ++ O,rep I k ++ t.bits⟩ = some (core t (rep O (k+1))) := by
    rw [core,show rep O (k+1) = rep O k ++ O by rw [rep,rep_snoc]]
    simpa only [List.nil_append,List.singleton_append,List.cons_append] using h2
  exact join0 h1 h2'

theorem finish (v : Variant) (k : Nat) (t : Tail) :
    run0 (table v) (2*(k+1)+1) (ret t (rep O (k+1))) = some (front (k+1) t) := by
  have h1 := sweepL (table v) 5 [] [] O O 2 (by intro L R; cases v <;> rfl) (k+1) [] (false::t.bits)
  have h1' : run0 (table v) (2*(k+1)) (ret t (rep O (k+1))) = some ⟨5,[],rep O (k+1) ++ [false] ++ t.bits⟩ := by
    simpa only [ret,List.nil_append,List.append_nil,List.append_assoc,List.singleton_append] using h1
  have h2 : run0 (table v) 1 ⟨5,[],rep O (k+1) ++ [false] ++ t.bits⟩ = some (front (k+1) t) := by
    have h : [true] ++ rep O (k+1) = rep I (k+1) ++ [true] := rotate true [false] (k+1)
    have hstep : run0 (table v) 1 ⟨5,[],rep O (k+1) ++ [false] ++ t.bits⟩ =
        some ⟨4,[],[true] ++ rep O (k+1) ++ [false] ++ t.bits⟩ := by cases v <;> rfl
    have he : [true] ++ rep O (k+1) ++ [false] ++ t.bits = rep I (k+2) ++ t.bits := by
      rw [h,show rep I (k+2) = rep I (k+1) ++ I by rw [rep,rep_snoc]]
      simp only [List.append_assoc]
      rfl
    rw [he] at hstep
    exact hstep
  exact join0 h1' h2

def cost (v : Variant) (k : Nat) (t : Tail) := (2+2*k)+t.cost v+(2*(k+1)+1)
theorem full (v : Variant) (k : Nat) (t : Tail) :
    run0 (table v) (cost v k t) (front k t) = some (front (k+1) t.next) :=
  join0 (join0 (scan v k t) (core_step v t (rep O (k+1)))) (finish v k t.next)

def iter : Nat → Tail
  | 0 => .terminal
  | n+1 => (iter n).next

def family (n : Nat) : Z0 := front (2+n) (iter n)
def entryTime : Variant → Nat
  | .le0 | .lf0 => 42
  | .ld1 => 44
  | .rd1 => 46

theorem entry (v : Variant) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem growth (v : Variant) (n : Nat) : run0 (table v) (cost v (2+n) (iter n)) (family n) = some (family (n+1)) := by
  simpa only [family,iter,show 2+(n+1)=2+n+1 by omega] using full v (2+n) (iter n)

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (fun n => cost v (2+n) (iter n)) (entry v)
    (by intro n; unfold cost; omega) (growth v) m hm
#print axioms never
end BB6Coverage.Agent43Raw122Counter05
