import Agent46AutoPump
import Raw41New024Auto
import Raw41New128Auto

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Two *distinct* one-hole partial six-state machines exhibit a common
nonhalting leftward tape-growth orbit at different quadratic times.

All infinite-time claims follow solely from the original Agent46AutoPump
source checker. There is no opaque metaprogram or trust in the simulator.
-/

namespace BB6.Agent36TwinSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
open BB6.Agent47Raw41

def p128 := Raw41New128Auto.Leaf10.table
def p024 := Raw41New024Auto.Leaf10.table
def cert128 := Raw41New128Auto.Leaf10.cert
def cert024 := Raw41New024Auto.Leaf10.cert

def tau128 (n : Nat) : Nat := 5*n*n + 20*n + 25
def tau024 (n : Nat) : Nat := 6*n*n + 23*n + 27

theorem tau128_succ (n : Nat) :
    tau128 (n+1) = tau128 n + (10*n + 25) := by
  simp only [tau128, Nat.mul_succ, Nat.succ_mul, Nat.add_mul, Nat.mul_add]
  omega

theorem tau024_succ (n : Nat) :
    tau024 (n+1) = tau024 n + (12*n + 29) := by
  simp only [tau024, Nat.mul_succ, Nat.succ_mul, Nat.add_mul, Nat.mul_add]
  omega

/-- Two independently synthesized symbolic pumps have an identical
    parameterized zipper family. -/
theorem twin_family :
    cert128.family = cert024.family := by decide +kernel

theorem twin128_orbit (n : Nat) :
    run0 p128 (tau128 n) ⟨0,[],[]⟩ =
      some (cert128.family.eval n) := by
  induction n with
  | zero =>
      simpa [tau128,p128,cert128] using
        (check_first Raw41New128Auto.Leaf10.table
          Raw41New128Auto.Leaf10.cert
          Raw41New128Auto.Leaf10.checked)
  | succ n ih =>
      rw [tau128_succ]
      have step := check_growth
        Raw41New128Auto.Leaf10.table
        Raw41New128Auto.Leaf10.cert
        Raw41New128Auto.Leaf10.checked n
      exact join0 ih (by simpa [p128,cert128] using step)

theorem twin024_orbit (n : Nat) :
    run0 p024 (tau024 n) ⟨0,[],[]⟩ =
      some (cert024.family.eval n) := by
  induction n with
  | zero =>
      simpa [tau024,p024,cert024] using
        (check_first Raw41New024Auto.Leaf10.table
          Raw41New024Auto.Leaf10.cert
          Raw41New024Auto.Leaf10.checked)
  | succ n ih =>
      rw [tau024_succ]
      have step := check_growth
        Raw41New024Auto.Leaf10.table
        Raw41New024Auto.Leaf10.cert
        Raw41New024Auto.Leaf10.checked n
      exact join0 ih (by simpa [p024,cert024] using step)

/-- Nontrivial time dilation: at times 5n²+20n+25 versus
    6n²+23n+27 the two machines reach precisely the same relative
    configurations from a blank tape, for EVERY natural number n. -/
theorem twin_quadratic_synchronization (n : Nat) :
    run0 p128 (tau128 n) ⟨0,[],[]⟩ =
    run0 p024 (tau024 n) ⟨0,[],[]⟩ := by
  rw [twin128_orbit n, twin024_orbit n]
  rw [twin_family]

/-- The time lag grows exactly as the product of successive integers. -/
theorem twin_quadratic_lag (n : Nat) :
    tau024 n = tau128 n + (n+1)*(n+2) := by
  simp only [tau024,tau128,Nat.add_mul,Nat.mul_add]
  omega

#print axioms twin128_orbit
#print axioms twin024_orbit
#print axioms twin_quadratic_synchronization
#print axioms twin_quadratic_lag

end BB6.Agent36TwinSweep
