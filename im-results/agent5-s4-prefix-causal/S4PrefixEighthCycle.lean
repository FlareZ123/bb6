import S4PrefixEighthMass
import Lean.Elab.Tactic.Omega

namespace S4PrefixEighthCycle

open S4PrefixEighthMass S4PrefixCausal S4PrefixSeven S4Toggle

set_option maxRecDepth 250000
set_option maxHeartbeats 0

theorem return8_25036 : return8 25036 = 109210 := by decide
theorem return8_109210 : return8 109210 = 109208 := by decide
theorem return8_109208 : return8 109208 = 109209 := by decide
theorem return8_109209 : return8 109209 = 109206 := by decide
theorem return8_109206 : return8 109206 = 109210 := by decide

theorem return8Iter_period4 (k : Nat) :
    return8Iter (k+5) 25036 = return8Iter (k+1) 25036 := by
  induction k with
  | zero =>
      simp [return8Iter, return8_25036, return8_109210,
        return8_109208, return8_109209, return8_109206]
  | succ k ih =>
      change return8 (return8Iter (k+5) 25036) =
        return8 (return8Iter (k+1) 25036)
      rw [ih]

theorem return8Iter_phase (k : Nat) :
    return8Iter (k+1) 25036 =
      if k%4=0 then 109210 else if k%4=1 then 109208
      else if k%4=2 then 109209 else 109206 := by
  induction k with
  | zero => simp [return8Iter, return8_25036]
  | succ k ih =>
      change return8 (return8Iter (k+1) 25036) = _
      rw [ih]
      have hm : (k+1)%4 = (k%4+1)%4 := by omega
      rw [hm]
      by_cases h0 : k%4=0
      · simp [h0, return8_109210]
      · by_cases h1 : k%4=1
        · simp [h1, return8_109208]
        · by_cases h2 : k%4=2
          · simp [h2, return8_109209]
          · have h3 : k%4=3 := by omega
            simp [h3, return8_109206]

def cycle8PeriodicStart : List Nat := cycle7 ++ [109210]

theorem return8Iter_four : return8Iter 4 109210 = 109210 := by
  simp [return8Iter, return8_109210, return8_109208,
    return8_109209, return8_109206]

theorem prefixRun_20480_cycle :
    prefixRun 20480 cycle8PeriodicStart = cycle8PeriodicStart := by
  have h := prefixRun_blocks 4 109210
  simpa [cycle8PeriodicStart, return8Iter_four] using h

private theorem prefixRun_add_eighth (m n : Nat) (xs : List Nat) :
    prefixRun (m+n) xs = prefixRun n (prefixRun m xs) := by
  induction n with
  | zero => simp [prefixRun]
  | succ n ih =>
      rw [Nat.add_succ]
      change pp (prefixRun (m+n) xs) = pp (prefixRun n (prefixRun m xs))
      rw [ih]

theorem prefixRun_period20480 (n : Nat) :
    prefixRun (n+20480) cycle8PeriodicStart =
      prefixRun n cycle8PeriodicStart := by
  calc
    prefixRun (n+20480) cycle8PeriodicStart =
        prefixRun (20480+n) cycle8PeriodicStart := by rw [Nat.add_comm]
    _ = prefixRun n (prefixRun 20480 cycle8PeriodicStart) :=
        prefixRun_add_eighth 20480 n cycle8PeriodicStart
    _ = prefixRun n cycle8PeriodicStart := by rw [prefixRun_20480_cycle]

private theorem prefixRun_plus_periods (r k : Nat) :
    prefixRun (r+20480*k) cycle8PeriodicStart =
      prefixRun r cycle8PeriodicStart := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, prefixRun_period20480, ih]

theorem prefixRun_mod20480 (n : Nat) :
    prefixRun n cycle8PeriodicStart =
      prefixRun (n%20480) cycle8PeriodicStart := by
  have hn : n%20480 + 20480*(n/20480) = n := by omega
  calc
    prefixRun n cycle8PeriodicStart =
        prefixRun (n%20480 + 20480*(n/20480)) cycle8PeriodicStart := by rw [hn]
    _ = prefixRun (n%20480) cycle8PeriodicStart :=
      prefixRun_plus_periods (n%20480) (n/20480)

theorem root_eight_prefix_from_5457 (n : Nat) (U : List Nat)
    (h : prun (5457+n) seed = some U) :
    U.take 8 = prefixRun n cycle8PeriodicStart := by
  have hindex : 5457+n = 337+(5120+n) := by omega
  have hroot : prun (337+(5120+n)) seed = some U := by
    simpa [hindex] using h
  have hp := S4PrefixEighthMass.root_eight_prefix (5120+n) U hroot
  have hstart : prefixRun 5120 cycle8Start = cycle8PeriodicStart := by
    rw [cycle8Start_eq]
    simpa [cycle8PeriodicStart, return8_25036] using block5120_shape 25036
  calc
    U.take 8 = prefixRun (5120+n) cycle8Start := hp
    _ = prefixRun n (prefixRun 5120 cycle8Start) :=
      prefixRun_add_eighth 5120 n cycle8Start
    _ = prefixRun n cycle8PeriodicStart := by rw [hstart]

theorem root_eight_prefix_mod20480 (n : Nat) (U : List Nat)
    (h : prun (5457+n) seed = some U) :
    U.take 8 = prefixRun (n%20480) cycle8PeriodicStart := by
  rw [root_eight_prefix_from_5457 n U h]
  exact prefixRun_mod20480 n

private theorem stackMass_append_eighth (xs ys : List Nat) :
    stackMass (xs++ys) = stackMass xs + stackMass ys := by
  simp [stackMass, List.sum_append, List.length_append,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem stackMass_take_drop8 (U : List Nat) :
    stackMass U = stackMass (U.take 8) + stackMass (U.drop 8) := by
  have hdecomp : U = U.take 8 ++ U.drop 8 := by
    symm
    exact List.take_append_drop 8 U
  calc
    stackMass U = stackMass (U.take 8 ++ U.drop 8) := congrArg stackMass hdecomp
    _ = stackMass (U.take 8) + stackMass (U.drop 8) :=
      stackMass_append_eighth _ _

theorem root_tail_mass_sum (m : Nat) (U : List Nat)
    (h : prun (5457+20480*m) seed = some U) :
    stackMass cycle8PeriodicStart + stackMass (U.drop 8) =
      2247 + 1024*(5457+20480*m) := by
  have hmass := root_mass (5457+20480*m) U h
  have hprefix0 := root_eight_prefix_mod20480 (20480*m) U h
  have hmod : (20480*m)%20480 = 0 := by omega
  have hprefix : U.take 8 = cycle8PeriodicStart := by
    simpa [hmod, prefixRun] using hprefix0
  have hsplit := stackMass_take_drop8 U
  rw [hprefix] at hsplit
  rw [hsplit] at hmass
  exact hmass

theorem root_tail_mass_step20480 (m : Nat) (U V : List Nat)
    (hU : prun (5457+20480*m) seed = some U)
    (hV : prun (5457+20480*(m+1)) seed = some V) :
    stackMass (V.drop 8) = stackMass (U.drop 8) + 20971520 := by
  have hsumU := root_tail_mass_sum m U hU
  have hsumV := root_tail_mass_sum (m+1) V hV
  have hbase : 2247 + 1024*(5457+20480*(m+1)) =
      (2247 + 1024*(5457+20480*m)) + 20971520 := by omega
  rw [hbase] at hsumV
  omega

#print axioms return8_25036
#print axioms return8_109210
#print axioms return8_109208
#print axioms return8_109209
#print axioms return8_109206
#print axioms return8Iter_period4
#print axioms return8Iter_phase
#print axioms prefixRun_20480_cycle
#print axioms prefixRun_period20480
#print axioms prefixRun_mod20480
#print axioms root_eight_prefix_from_5457
#print axioms root_eight_prefix_mod20480
#print axioms root_tail_mass_sum
#print axioms root_tail_mass_step20480

end S4PrefixEighthCycle
