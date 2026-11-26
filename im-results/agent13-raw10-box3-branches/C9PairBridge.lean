import Frontier
import C9PairTrace
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace BB6.Agent13.C9Bridge
open BB6Coverage

def q (s : Fin 6) : C9Pair.Q :=
  match s.val with
  | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F

def project (z : Config) : C9Pair.Config :=
  ⟨q z.state, fun n => z.tape (z.head-1-(n : Int)), z.tape z.head,
    fun n => z.tape (z.head+1+(n : Int))⟩

def table (short : Bool) : Machine := fun s => match s with
  | (0,false) => some ⟨true,true,1⟩
  | (0,true) => some ⟨false,true,3⟩
  | (1,false) => some ⟨true,false,2⟩
  | (1,true) => some ⟨true,false,1⟩
  | (2,false) => some ⟨false,false,4⟩
  | (2,true) => some ⟨false,false,2⟩
  | (3,false) => some ⟨short,true,5⟩
  | (3,true) => some ⟨true,false,4⟩
  | (4,false) => some ⟨true,true,4⟩
  | (4,true) => some ⟨false,true,0⟩
  | (5,false) => some ⟨true,false,if short then 1 else 0⟩
  | (5,true) => none
  | _ => none

theorem project_applyMove (z : Config) (mv : Move) :
    project (applyMove z mv) = if mv.right then C9Pair.right (q mv.next) mv.write (project z)
      else C9Pair.left (q mv.next) mv.write (project z) := by
  rcases z with ⟨s,h,t⟩
  rcases mv with ⟨w,r,n⟩
  cases r <;> simp only [applyMove,project,C9Pair.left,C9Pair.right,Bool.false_eq_true,ite_false,ite_true,C9Pair.pop]
  · congr 1
    · funext k
      rw [ite_eq_right (by omega)]
      congr 1; omega
    · rw [ite_eq_right (by omega)]
      congr 1; omega
    · funext k; cases k with
      | zero => simp [C9Pair.push] <;> omega
      | succ k =>
        simp only [C9Pair.push,Int.natCast_succ]
        rw [ite_eq_right (by omega)]
        congr 1; omega
  · congr 1
    · funext k; cases k with
      | zero => simp [C9Pair.push] <;> omega
      | succ k =>
        simp only [C9Pair.push,Int.natCast_succ]
        rw [ite_eq_right (by omega)]
        congr 1; omega
    · rw [ite_eq_right (by omega)]
      congr 1; omega
    · funext k
      rw [ite_eq_right (by omega)]
      congr 1; omega

theorem project_step (short : Bool) (z : Config) :
    (rawStep (table short) z).map project = C9Pair.step short (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hbit : t h <;> cases short <;>
    simp only [rawStep,readSlot,hbit,table,Option.map_some,Option.map_none,project_applyMove, Bool.false_eq_true,ite_false,ite_true] <;>
    simp [C9Pair.step,project,q,hbit,C9Pair.left,C9Pair.right] <;> rfl

theorem project_run (short : Bool) (n : Nat) (z : Config) :
    (run (table short) n z).map project = C9Pair.run short n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [C9Pair.run_add short n 1,← ih]
    simp only [run]
    cases h : run (table short) n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some,C9Pair.run,Option.bind_some]
      rw [project_step]
      cases C9Pair.step short (project c) <;> rfl

theorem project_blank : project blank = C9Pair.blank := rfl

def time (short : Bool) : Nat := if short then 3142249302385139 else 3142249368711029

theorem exact_halt (short : Bool) : HaltsAfter (table short) (time short) := by
  have h : ∃ c, C9Pair.run short (time short) C9Pair.blank = some c ∧ C9Pair.step short c = none := by
    cases short
    · exact C9Pair.long_halt
    · exact C9Pair.short_halt
  obtain ⟨c,hc,hs⟩ := h
  have hlive := project_run short (time short) blank
  rw [project_blank,hc] at hlive
  have hhalt := project_run short (time short+1) blank
  rw [project_blank,C9Pair.run_add,hc] at hhalt
  simp only [Option.bind_some,C9Pair.run,hs,Option.bind_none] at hhalt
  constructor
  · cases hh : run (table short) (time short) blank <;> simp [hh] at hlive ⊢
  · cases hh : run (table short) (time short+1) blank <;> simp [hh] at hhalt ⊢

theorem short_halt : HaltsAfter (table true) 3142249302385139 := exact_halt true
theorem long_halt : HaltsAfter (table false) 3142249368711029 := exact_halt false

#print axioms short_halt
#print axioms long_halt
end BB6.Agent13.C9Bridge
