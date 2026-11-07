import S4SharpWitness
import S4PrefixGate64
import Lean.Elab.Tactic.Omega

/-! Sharp six-digit stopping-gate atlas for the authentic S4 triple-drain
prefix cycle. The finite witness theorems use the unchanged source's G power gate. -/
namespace S4SharpCensus
open S4Power S4Octet S4Toggle S4PrefixCausal S4PrefixGate64 S4Sharp6
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def badScan : Nat → Nat → List Nat → List (Nat × List Nat)
  | 0, _, _ => []
  | n+1, i, xs =>
     if guard6 xs then badScan n (i+1) (pp xs)
     else (i,xs) :: badScan n (i+1) (pp xs)

def badCases : List (Nat × List Nat) :=
  [
    (14,[283,908,2493,4081,13917,3757]),
    (23,[282,967,2129,1857,9553,13780]),
    (33,[281,512,1339,6000,7805,6592]),
    (34,[283,906,982,3491,5648,6120]),
    (36,[280,396,743,4056,3940,5030]),
    (63,[282,965,1732,7418,3642,8153]),
    (98,[283,906,982,3491,5652,24898]),
    (142,[283,908,2493,4081,13921,14197]),
    (161,[281,512,1339,6000,7809,28090]),
    (167,[282,967,2128,1427,3843,14249]),
    (191,[282,965,1732,7418,3644,12294]),
    (193,[281,512,1339,5998,3978,8136]),
    (211,[282,964,974,2637,13534,14347]),
    (215,[282,967,2129,1857,9552,11022]),
    (242,[283,906,984,4292,3251,6300]),
    (270,[283,908,2493,4081,13917,3759]),
    (279,[282,967,2129,1857,9553,13781]),
    (290,[283,906,982,3491,5648,6122]),
    (303,[282,965,1729,2904,4020,11374]),
    (311,[282,967,2129,1856,4258,12658]),
    (343,[282,967,2129,1857,9555,25911]),
    (354,[283,906,982,3491,5652,24896]),
    (356,[280,396,743,4056,3942,14419]),
    (359,[282,967,2128,1427,3841,9130]),
    (417,[281,512,1339,6000,7809,28092]),
    (418,[283,906,982,3491,5650,16871]),
    (423,[282,967,2128,1427,3843,14247]),
    (430,[283,908,2493,4079,5130,8583]),
    (434,[283,906,984,4292,3253,9551]),
    (447,[282,965,1732,7418,3644,12290]),
    (449,[281,512,1339,5998,3978,8134]),
    (471,[282,967,2129,1857,9552,11024]),
    (484,[280,396,743,4056,3944,19646]),
    (495,[282,965,1729,2904,4018,9343]),
    (499,[282,964,974,2633,2942,4622]),
    (511,[282,965,1732,7418,3640,3578]),
    (513,[281,512,1339,5998,3976,3777]),
    (526,[283,908,2493,4081,13917,3755]),
    (548,[280,396,743,4056,3940,5034]),
    (567,[282,967,2129,1856,4258,12660]),
    (575,[282,965,1732,7418,3642,8151]),
    (599,[282,967,2129,1857,9555,25909]),
    (612,[280,396,743,4056,3942,14421]),
    (627,[282,964,974,2633,2946,16240]),
    (631,[282,967,2129,1856,4256,9321]),
    (654,[283,908,2493,4081,13921,14193]),
    (673,[281,512,1339,6000,7809,28088]),
    (674,[283,906,982,3491,5650,16869]),
    (686,[283,908,2493,4079,5130,8585]),
    (705,[281,512,1339,5998,3978,8138]),
    (751,[282,965,1729,2904,4018,9345]),
    (754,[283,906,984,4292,3251,6298]),
    (755,[282,964,974,2633,2942,4620]),
    (759,[282,967,2129,1856,4254,3510]),
    (801,[281,512,1339,6000,7805,6594]),
    (855,[282,967,2129,1857,9555,25913]),
    (871,[282,967,2128,1427,3841,9134]),
    (887,[282,967,2129,1856,4256,9323]),
    (930,[283,906,982,3491,5650,16873]),
    (946,[283,906,984,4292,3253,9555]),
    (959,[282,965,1732,7418,3644,12292]),
    (979,[282,964,974,2637,13534,14349]),
    (996,[280,396,743,4056,3944,19648]),
    (1006,[283,908,2493,4079,5132,14664]),
    (1007,[282,965,1729,2904,4018,9341]),
    (1010,[283,906,984,4292,3251,6296]),
    (1015,[282,967,2129,1856,4254,3512]),
    (1023,[282,965,1732,7418,3640,3576])
  ]

private theorem prefix_shift (d : Nat) (xs : List Nat) :
  prefixRun (d+1) xs = prefixRun d (pp xs) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change pp (prefixRun (d+1) xs) = pp (prefixRun d (pp xs))
    rw [ih]

theorem scan_contains (n idx : Nat) (xs : List Nat) (d : Nat)
    (hd : d < n) (hguard : guard6 (prefixRun d xs) = false) :
    (idx+d, prefixRun d xs) ∈ badScan n idx xs := by
  induction n generalizing idx xs d with
  | zero => omega
  | succ n ih =>
      cases d with
      | zero =>
          have hx : guard6 xs = false := by simpa [prefixRun] using hguard
          simp [badScan, hx, prefixRun]
      | succ d =>
          have hlt : d < n := by omega
          have heq : prefixRun (d+1) xs = prefixRun d (pp xs) := prefix_shift d xs
          have hguard' : guard6 (prefixRun d (pp xs)) = false := by
            simpa only [heq] using hguard
          have ht := ih (idx+1) (pp xs) d hlt hguard'
          have hpair : (idx+(d+1), prefixRun (d+1) xs) =
                       ((idx+1)+d, prefixRun d (pp xs)) := by
            rw [heq]; congr 1; omega
          rw [hpair]
          by_cases hb : guard6 xs = true
          · simpa [badScan,hb] using ht
          · have hf : guard6 xs = false := by cases hh : guard6 xs <;> simp_all
            simp [badScan,hf,ht]

/-- Every table entry has a source-proved one-digit synthetic halt witness. -/
theorem cases_have_witness
   (r : Nat × List Nat) (hr : r∈badCases) :
   ∃ t : Nat, P (r.2++[t])=none := by
  simp only [badCases,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · cases h
    exact ⟨2106, S4Sharp6.bad_0014⟩
  · cases h
    exact ⟨6696, S4Sharp6.bad_0023⟩
  · cases h
    exact ⟨2070, S4Sharp6.bad_0033⟩
  · cases h
    exact ⟨3160, S4Sharp6.bad_0034⟩
  · cases h
    exact ⟨3755, S4Sharp6.bad_0036⟩
  · cases h
    exact ⟨2125, S4Sharp6.bad_0063⟩
  · cases h
    exact ⟨1962, S4Sharp6.bad_0098⟩
  · cases h
    exact ⟨5077, S4Sharp6.bad_0142⟩
  · cases h
    exact ⟨15896, S4Sharp6.bad_0161⟩
  · cases h
    exact ⟨7798, S4Sharp6.bad_0167⟩
  · cases h
    exact ⟨54, S4Sharp6.bad_0191⟩
  · cases h
    exact ⟨2255, S4Sharp6.bad_0193⟩
  · cases h
    exact ⟨5360, S4Sharp6.bad_0211⟩
  · cases h
    exact ⟨6328, S4Sharp6.bad_0215⟩
  · cases h
    exact ⟨3569, S4Sharp6.bad_0242⟩
  · cases h
    exact ⟨2105, S4Sharp6.bad_0270⟩
  · cases h
    exact ⟨104, S4Sharp6.bad_0279⟩
  · cases h
    exact ⟨3159, S4Sharp6.bad_0290⟩
  · cases h
    exact ⟨877, S4Sharp6.bad_0303⟩
  · cases h
    exact ⟨40, S4Sharp6.bad_0311⟩
  · cases h
    exact ⟨630, S4Sharp6.bad_0343⟩
  · cases h
    exact ⟨1963, S4Sharp6.bad_0354⟩
  · cases h
    exact ⟨7252, S4Sharp6.bad_0356⟩
  · cases h
    exact ⟨2166, S4Sharp6.bad_0359⟩
  · cases h
    exact ⟨15895, S4Sharp6.bad_0417⟩
  · cases h
    exact ⟨5976, S4Sharp6.bad_0418⟩
  · cases h
    exact ⟨7799, S4Sharp6.bad_0423⟩
  · cases h
    exact ⟨1890, S4Sharp6.bad_0430⟩
  · cases h
    exact ⟨1943, S4Sharp6.bad_0434⟩
  · cases h
    exact ⟨56, S4Sharp6.bad_0447⟩
  · cases h
    exact ⟨2256, S4Sharp6.bad_0449⟩
  · cases h
    exact ⟨6327, S4Sharp6.bad_0471⟩
  · cases h
    exact ⟨4638, S4Sharp6.bad_0484⟩
  · cases h
    exact ⟨1893, S4Sharp6.bad_0495⟩
  · cases h
    exact ⟨583, S4Sharp6.bad_0499⟩
  · cases h
    exact ⟨317, S4Sharp6.bad_0511⟩
  · cases h
    exact ⟨339, S4Sharp6.bad_0513⟩
  · cases h
    exact ⟨2107, S4Sharp6.bad_0526⟩
  · cases h
    exact ⟨3753, S4Sharp6.bad_0548⟩
  · cases h
    exact ⟨39, S4Sharp6.bad_0567⟩
  · cases h
    exact ⟨2126, S4Sharp6.bad_0575⟩
  · cases h
    exact ⟨631, S4Sharp6.bad_0599⟩
  · cases h
    exact ⟨7251, S4Sharp6.bad_0612⟩
  · cases h
    exact ⟨7061, S4Sharp6.bad_0627⟩
  · cases h
    exact ⟨1709, S4Sharp6.bad_0631⟩
  · cases h
    exact ⟨5079, S4Sharp6.bad_0654⟩
  · cases h
    exact ⟨15897, S4Sharp6.bad_0673⟩
  · cases h
    exact ⟨5977, S4Sharp6.bad_0674⟩
  · cases h
    exact ⟨1889, S4Sharp6.bad_0686⟩
  · cases h
    exact ⟨2254, S4Sharp6.bad_0705⟩
  · cases h
    exact ⟨1892, S4Sharp6.bad_0751⟩
  · cases h
    exact ⟨3570, S4Sharp6.bad_0754⟩
  · cases h
    exact ⟨584, S4Sharp6.bad_0755⟩
  · cases h
    exact ⟨519, S4Sharp6.bad_0759⟩
  · cases h
    exact ⟨2069, S4Sharp6.bad_0801⟩
  · cases h
    exact ⟨629, S4Sharp6.bad_0855⟩
  · cases h
    exact ⟨2164, S4Sharp6.bad_0871⟩
  · cases h
    exact ⟨1708, S4Sharp6.bad_0887⟩
  · cases h
    exact ⟨5975, S4Sharp6.bad_0930⟩
  · cases h
    exact ⟨1941, S4Sharp6.bad_0946⟩
  · cases h
    exact ⟨55, S4Sharp6.bad_0959⟩
  · cases h
    exact ⟨5359, S4Sharp6.bad_0979⟩
  · cases h
    exact ⟨4637, S4Sharp6.bad_0996⟩
  · cases h
    exact ⟨7041, S4Sharp6.bad_1006⟩
  · cases h
    exact ⟨1894, S4Sharp6.bad_1007⟩
  · cases h
    exact ⟨3571, S4Sharp6.bad_1010⟩
  · cases h
    exact ⟨518, S4Sharp6.bad_1015⟩
  · cases h
    exact ⟨318, S4Sharp6.bad_1023⟩

/-- Exhaustive 1024-step finite transducer scan; kernel evaluated without axioms. -/
theorem scanExact : badScan 1024 0 phase = badCases := by decide

/-- Full biconditional: the mod-64 guard is exactly the set of six-digit cyclic
    prefixes safe for every possible finite suffix. -/
theorem exact_phase
   (i : Nat) (hi : i<1024) :
   (∀ S : List Nat, P (prefixRun i phase ++ S) ≠ none) ↔
     guard6 (prefixRun i phase)=true := by
  constructor
  · intro hall
    cases hg : guard6 (prefixRun i phase) with
    | true => rfl
    | false =>
        have hmem : (i, prefixRun i phase) ∈ badCases := by
          have hscan := scan_contains 1024 0 phase i hi hg
          simpa only [scanExact, Nat.zero_add] using hscan
        obtain ⟨t, hhalt⟩ := cases_have_witness _ hmem
        exact False.elim ((hall [t]) hhalt)
  · intro hsafe S
    exact P_safe64 (prefixRun i phase) S
      (by simpa [prefixRun_length,phase]) hsafe

private theorem phase_mod1024 (n : Nat) :
    prefixRun n phase = prefixRun (n%1024) phase := by
  have hperiod (m : Nat) : prefixRun (m+1024) phase = prefixRun m phase := by
    rw [show m+1024=1024+m by omega,prefixRun_add,period1024]
  have hperiods (r k : Nat) : prefixRun (r+1024*k) phase = prefixRun r phase := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ,←Nat.add_assoc,hperiod,ih]
  have hn : n=n%1024+1024*(n/1024) := by omega
  calc
    prefixRun n phase = prefixRun (n%1024+1024*(n/1024)) phase := congrArg (fun t => prefixRun t phase) hn
    _ = prefixRun (n%1024) phase := hperiods _ _

/-- Exact safety classification at every cycle time, modulo 1024. -/
theorem exact_phase_all_times (n : Nat) :
  (∀ T : List Nat, P (prefixRun n phase ++ T) ≠ none) ↔
    guard6 (prefixRun (n%1024) phase) = true := by
  rw [phase_mod1024]
  exact exact_phase (n%1024) (Nat.mod_lt n (by omega))

/-- A genuine first failure after the 143-step synchronization must occur at
    a prefix with a one-digit synthetic halting completion. This remains
    conditional on the actual full-tail orbit. -/
theorem genuine_failure_has_synthetic_completion (n : Nat) (U : List Nat)
  (hroot : prun (143+n) seed = some U) (hfail : P U = none) :
  ∃ t : Nat, P (prefixRun (n%1024) phase ++ [t]) = none := by
  have hbad : guard6 (prefixRun (n%1024) phase)=false :=
    rooted_failure_implies_bad_guard n U hroot hfail
  have hlt : n%1024<1024 := Nat.mod_lt n (by omega)
  have hmem : (n%1024, prefixRun (n%1024) phase) ∈ badCases := by
    have hs := scan_contains 1024 0 phase (n%1024) hlt hbad
    simpa only [scanExact,Nat.zero_add] using hs
  exact cases_have_witness _ hmem

#print axioms exact_phase_all_times
#print axioms genuine_failure_has_synthetic_completion
#print axioms exact_phase
#print axioms cases_have_witness
#print axioms scan_contains
#print axioms scanExact
end S4SharpCensus
