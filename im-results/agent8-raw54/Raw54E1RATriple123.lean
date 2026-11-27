import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RATriple123
open BB6Coverage BB6Coverage.Agent31Pump

inductive Variant | one | two | three

def table (v : Variant) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨(match v with | .one => false | _ => true),true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,true => some (some (match v with
      | .one => ⟨false,false,1⟩
      | .two => ⟨false,true,1⟩
      | .three => ⟨false,true,3⟩))
  | _,_ => none

def triple : List Bool := [true,true,true]
def width (v : Variant) : Nat := match v with | .one => 7 | _ => 5
def family (n : Nat) : Z0 := ⟨0,[false,false],[true,true] ++ rep triple n⟩
def cost (v : Variant) (n : Nat) : Nat := 9 + width v * (n+1) + 6 + 27*(n+1)

theorem first (v : Variant) : run0 (table v) 7 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem enter (v : Variant) (R : List Bool) :
    run0 (table v) 9 ⟨0,[false,false],[true,true] ++ R⟩ = some ⟨1,[false,true],triple ++ R⟩ := by cases v <;> rfl

theorem transfer (v : Variant) (L R : List Bool) :
    run0 (table v) (width v) ⟨1,[false,true] ++ L,triple ++ R⟩ =
    some ⟨1,[false,true] ++ triple ++ L,R⟩ := by cases v <;> rfl

theorem finish (v : Variant) (L : List Bool) :
    run0 (table v) 6 ⟨1,[false,true] ++ L,[]⟩ = some ⟨0,[false,false] ++ L,[true,true]⟩ := by cases v <;> rfl

theorem drain (v : Variant) (L R : List Bool) :
    run0 (table v) 27 ⟨0,[false,false] ++ triple ++ L,[true,true] ++ R⟩ =
    some ⟨0,[false,false] ++ L,[true,true] ++ triple ++ R⟩ := by cases v <;> rfl

theorem epoch (v : Variant) (n : Nat) :
    run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have h1 := enter v (rep triple n)
  have h2 := sweepR (table v) 1 [false,true] [] triple triple (width v) (transfer v) (n+1) [] []
  simp only [List.nil_append,List.append_nil] at h2
  have h3 := finish v (rep triple (n+1))
  have h4 := sweepL (table v) 0 [false,false] [true,true] triple triple 27 (drain v) (n+1) [] []
  simp only [List.append_nil] at h4
  exact join0 (join0 (join0 h1 h2) h3) h4

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 7 (cost v) (first v) (by intro n; unfold cost; omega) (epoch v) m hm

#print axioms never
end BB6.Agent8Raw54.E1RATriple123
