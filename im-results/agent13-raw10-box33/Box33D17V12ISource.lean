import Frontier
import Box33D17V12IInvariant

namespace BB6.Agent13.Box33D17V12I
open BB6Coverage
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def q (s : Fin 6) : MacroI.Q :=
  match s.val with
  | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F

def project (c : Config) : MacroI.C :=
  ⟨q c.state, fun n => c.tape (c.head-1-(n:Int)), fun n => c.tape (c.head+(n:Int))⟩

def codes : List (Fin 25) := [8,24,11,18,1,13,17,3,12,0,4,21]
def decode (v : Fin 25) : Transition :=
  if v.val=0 then none else let j:=v.val-1; some ⟨(j/2)%2==1,j%2==1,⟨j/4,by have := v.isLt; omega⟩⟩
def table : Machine := fun s => decode (codes.getD (2*s.1.val+s.2.toNat) 0)

theorem project_applyMove (c : Config) (m : Move) :
    project (applyMove c m) =
    if m.right then MacroI.right (q m.next) m.write (project c)
    else MacroI.left (q m.next) m.write (project c) := by
  rcases c with ⟨s,h,t⟩
  rcases m with ⟨w,r,n⟩
  cases r <;> simp only [project,applyMove,Bool.false_eq_true,ite_false,ite_true,MacroI.left,MacroI.right,MacroI.cfg]
  · congr 1
    · funext k
      simp only [MacroI.tail,Int.natCast_succ]
      rw [ite_eq_right (by omega)]
      congr 1; omega
    · funext k
      cases k with
      | zero => simp [MacroI.push,show h - 1 ≠ h by omega,show h + -1 = h-1 by omega]
      | succ k =>
        cases k with
        | zero => simp [MacroI.push,show h + -1 + 1 = h by omega]
        | succ k =>
          simp only [MacroI.push,MacroI.tail,Int.natCast_succ]
          rw [ite_eq_right (by omega)]
          congr 1; omega
  · congr 1
    · funext k
      cases k with
      | zero => simp [MacroI.push]
      | succ k =>
        simp only [MacroI.push,Int.natCast_succ]
        rw [ite_eq_right (by omega)]
        congr 1; omega
    · funext k
      simp only [MacroI.tail,Int.natCast_succ]
      rw [ite_eq_right (by omega)]
      congr 1; omega

theorem project_step (c : Config) :
    (rawStep table c).map project = MacroI.step (project c) := by
  have hm : (rawStep table c).map project =
      match table (readSlot c) with
      | none => none
      | some mv => some (if mv.right then MacroI.right (q mv.next) mv.write (project c)
                         else MacroI.left (q mv.next) mv.write (project c)) := by
    unfold rawStep
    cases ht : table (readSlot c) with
    | none => rfl
    | some mv => simp only [Option.map_some,project_applyMove]
  rw [hm]
  rcases c with ⟨s,p,t⟩
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp [project,table,decode,codes,MacroI.step,q,hb] <;> rfl

theorem project_run (n : Nat) (c : Config) :
    (run table n c).map project = MacroI.run n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=n+1 by rfl,MacroI.run_add,←ih]
    simp only [run]
    cases he : run table n c with
    | none => rfl
    | some d =>
      simp only [Option.bind_some,Option.map_some]
      have hs := project_step d
      simpa [MacroI.run] using hs

theorem source_never : NeverHalts table := by
  intro n
  have he := project_run n blank
  change (run table n blank).map project = MacroI.run n (MacroI.cfg .A MacroI.z MacroI.z) at he
  cases hr : run table n blank with
  | none =>
    rw [hr] at he
    exact False.elim (MacroI.neverBlank_I n he.symm)
  | some c => rfl

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact source_never

#print axioms source_never
#print axioms compatible_never
end BB6.Agent13.Box33D17V12I
