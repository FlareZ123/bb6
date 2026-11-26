import Raw11ExtraSeed
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace Raw11ExtraSweep
open Root56 (Config blank)

def start (v : Bool) : Nat := if v then 1346 else 1146

def clock (v : Bool) : Nat → Nat
  | 0 => start v
  | k+1 => clock v k + (stride v*(19+2*k)+turn v+4*(18+2*k)+4)

theorem at_clock (v : Bool) (k : Nat) : run v (clock v k) blank = some (sec (19+2*k)) := by
  induction k with
  | zero =>
    cases v with
    | false => exact seed_no
    | true => exact seed_yes
  | succ k ih =>
    simp only [clock]
    rw [run_add,ih]
    simp only [Option.bind_some]
    have ha := advance v (18+2*k)
    rwa [show 18+2*k+1=19+2*k by omega,show 18+2*k+3=19+2*(k+1) by omega] at ha

theorem clock_ge (v : Bool) (k : Nat) : k ≤ clock v k := by
  induction k with
  | zero => omega
  | succ k ih =>
    change k+1 ≤ clock v k + (stride v*(19+2*k)+turn v+4*(18+2*k)+4)
    omega

theorem never (v : Bool) (n : Nat) : run v n blank ≠ none := by
  intro h
  have hs := at_clock v n
  have hx := run_add v n (clock v n-n) blank
  rw [Nat.add_sub_of_le (clock_ge v n),hs,h] at hx
  contradiction

#print axioms never
end Raw11ExtraSweep
