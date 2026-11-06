import S4Toggle
import Lean.Elab.Tactic.Omega

namespace S4DriftRay
open S4Power S4Octet S4Toggle
set_option maxHeartbeats 0

theorem drift (x : Nat) (S : List Nat) :
    P ([284,1646,1026,x] ++ S) =
      some ([284,1646,1026,x+1024] ++ S) := by
  simp [P,G,H]

theorem run_drift (n x : Nat) (S : List Nat) :
    prun n ([284,1646,1026,x] ++ S) =
      some ([284,1646,1026,x+1024*n] ++ S) := by
  induction n with
  | zero => simp [prun]
  | succ n ih =>
      change (prun n ([284,1646,1026,x]++S)).bind P = _
      rw [ih]
      simp only [Option.bind_some]
      rw [drift]
      have hx : (x+1024*n)+1024 = x+1024*(n+1) := by omega
      simp [hx]

theorem never_halts (x : Nat) (S : List Nat) :
    ¬∃ n, prun n ([284,1646,1026,x] ++ S) = none := by
  rintro ⟨n,hn⟩
  rw [run_drift] at hn
  cases hn

#print axioms drift
#print axioms run_drift
#print axioms never_halts
end S4DriftRay
