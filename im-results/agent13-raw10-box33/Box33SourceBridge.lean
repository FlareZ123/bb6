import Frontier
import Box33UnarySweeper

namespace BB6.Agent13.Box33Source
open BB6Coverage
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def perm (flip : Bool) (s : Fin 6) : Fin 6 :=
  if flip then if s=4 then 5 else if s=5 then 4 else s else s
def q (flip : Bool) (s : Fin 6) : C9Pair.Q :=
  match (perm flip s).val with
  | 0 => .A | 1 => .B | 2 => .C | 3 => .D | 4 => .E | _ => .F
def project (flip : Bool) (z : Config) : C9Pair.Config :=
  ⟨q flip z.state, fun n => z.tape (z.head-1-(n : Int)), z.tape z.head,
    fun n => z.tape (z.head+1+(n : Int))⟩
def base (sweep : Bool) : Machine := fun s => match s with
  | (0,false) => some ⟨true,true,1⟩
  | (0,true) => some ⟨true,true,if sweep then 5 else 4⟩
  | (1,false) => some ⟨true,false,2⟩
  | (1,true) => some ⟨false,false,3⟩
  | (2,false) => some ⟨false,false,0⟩
  | (2,true) => some ⟨false,false,3⟩
  | (3,false) => some ⟨false,true,0⟩
  | (3,true) => some ⟨true,false,5⟩
  | (4,false) => if sweep then none else some ⟨true,true,0⟩
  | (4,true) => if sweep then some ⟨false,true,2⟩ else none
  | (5,false) => some ⟨sweep,true,0⟩
  | (5,true) => if sweep then some ⟨true,true,4⟩ else some ⟨false,false,5⟩
  | _ => none
def table (sweep flip : Bool) : Machine := fun s =>
  (base sweep (perm flip s.1,s.2)).map fun mv => ⟨mv.write,mv.right,perm flip mv.next⟩
def step (sweep : Bool) (c : C9Pair.Config) : Option C9Pair.Config :=
  if sweep then Box33UnarySweeper.step c else Box33BinaryCounter.step c
def localRun (sweep : Bool) (n : Nat) (c : C9Pair.Config) : Option C9Pair.Config :=
  if sweep then Box33UnarySweeper.run n c else Box33BinaryCounter.run n c
theorem localRun_add (sweep : Bool) (m n : Nat) (c : C9Pair.Config) :
    localRun sweep (m+n) c = (localRun sweep m c).bind (localRun sweep n) := by
  cases sweep
  · exact Box33BinaryCounter.run_add m n c
  · exact Box33UnarySweeper.run_add m n c
theorem localRun_one (sweep : Bool) (c : C9Pair.Config) : localRun sweep 1 c = step sweep c := by
  cases sweep <;> simp [localRun,step,Box33BinaryCounter.run,Box33UnarySweeper.run]
theorem project_applyMove (flip : Bool) (z : Config) (mv : Move) :
    project flip (applyMove z mv) = if mv.right then C9Pair.right (q flip mv.next) mv.write (project flip z)
      else C9Pair.left (q flip mv.next) mv.write (project flip z) := by
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
theorem map_step (sweep flip : Bool) (z : Config) :
    (rawStep (table sweep flip) z).map (project flip) =
      match table sweep flip (readSlot z) with
      | none => none
      | some mv => some (if mv.right then C9Pair.right (q flip mv.next) mv.write (project flip z)
                         else C9Pair.left (q flip mv.next) mv.write (project flip z)) := by
  unfold rawStep
  cases h : table sweep flip (readSlot z) with
  | none => rfl
  | some mv => simp only [Option.map_some,project_applyMove]
theorem project_step (sweep flip : Bool) (z : Config) :
    (rawStep (table sweep flip) z).map (project flip) = step sweep (project flip z) := by
  rw [map_step]
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hbit : t h <;> cases sweep <;> cases flip <;>
    simp only [readSlot,project,hbit] <;> rfl
theorem project_run (sweep flip : Bool) (n : Nat) (z : Config) :
    (run (table sweep flip) n z).map (project flip) = localRun sweep n (project flip z) := by
  induction n with
  | zero => cases sweep <;> rfl
  | succ n ih =>
    rw [localRun_add sweep n 1,← ih]
    simp only [run]
    cases h : run (table sweep flip) n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some,localRun_one]
      exact project_step sweep flip c
theorem project_blank (flip : Bool) : project flip blank = Box33UnarySweeper.blank := by
  cases flip <;> rfl
theorem never (sweep flip : Bool) : NeverHalts (table sweep flip) := by
  intro n
  have h := project_run sweep flip n blank
  rw [project_blank] at h
  have hn : localRun sweep n Box33UnarySweeper.blank ≠ none := by
    cases sweep
    · exact Box33BinaryCounter.never_blank n
    · exact Box33UnarySweeper.never_blank n
  cases he : run (table sweep flip) n blank with
  | none => exact False.elim (hn (by simpa [he] using h.symm))
  | some c => rfl
def partialTable (sweep flip : Bool) : PartialMachine := fun s => some (table sweep flip s)
theorem compatible_never (sweep flip : Bool) (m : Machine) (hm : compatible (partialTable sweep flip) m) : NeverHalts m := by
  have he : m = table sweep flip := funext fun s => hm s _ rfl
  rw [he]
  exact never sweep flip
#print axioms never
#print axioms compatible_never
end BB6.Agent13.Box33Source
