import NearPowerGenerate
import NearPowerTreeSource
import FatalFamilyWindow

namespace BB6.Agent41NearPower
open BB6.Agent41FatalInverse BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- Connect the compressed initial state to the exact family coordinates. -/
theorem fatalState_rep (k : Nat) (hk : 7≤k) : Represents (fatalState (k+1)) (targetX k) (targetY k) := by
  have hp := pow_margin k hk
  have hb := base_power k
  have ho := pow_three_odd (k+1)
  have hY := targetY_formula k hk
  have hp' : 3^(k+1)=3*3^k := by rw [Nat.pow_succ]; omega
  have hcast : ((3^(k+1):Nat):Int)=(3:Int)^(k+1) := Int.natCast_pow 3 (k+1)
  unfold Represents fatalState targetX
  simp only [Int.ofNat_one,Int.one_mul,Int.reduceNeg,Int.natCast_succ]
  rw [←hcast]
  omega

def cert5288 : Cert := Cert.fork (-7067) (-21137) Cert.stop
  (Cert.fork (-7068) (-7066) Cert.stop
    (Cert.fork (-23489) (-9415) Cert.stop
      (Cert.fork (-9035) (-23101) Cert.stop
        (Cert.fork (-10860) (-10858)
          (Cert.fork (-7160) (-7158)
            (Cert.fork (-5924) (-5930) Cert.stop Cert.stop)
            (Cert.fork (-27785) (-13719) Cert.stop Cert.stop))
          (Cert.fork (-25401) (-11335)
            (Cert.fork (-8487) (-22545)
              (Cert.fork (-16909) (-2847)
                (Cert.fork (-5663) (-19709) Cert.stop
                  (Cert.fork (-23624) (-23614)
                    (Cert.fork (-11416) (-11422)
                      (Cert.fork (-7344) (-7346)
                        (Cert.fork (-5984) (-5994)
                          (Cert.fork (-5540) (-5534) Cert.stop Cert.stop)
                          Cert.stop) Cert.stop) Cert.stop)
                    (Cert.fork (-32313) (-18263)
                      (Cert.fork (-10799) (-24849)
                        (Cert.fork (-17673) (-3627)
                          (Cert.fork (-5915) (-19957)
                            (Cert.fork (-16041) (-1995) Cert.stop
                              (Cert.fork (-30235) (-44253)
                                (Cert.fork (-24137) (-10119)
                                  (Cert.fork (-8083) (-22101)
                                    (Cert.fork (-16749) (-2731) Cert.stop
                                      (Cert.fork (-29427) (-43453)
                                        (Cert.fork (-23877) (-9851) Cert.stop Cert.stop)
                                        (Cert.fork (-15424) (-15438)
                                          (Cert.fork (-8692) (-8690)
                                            (Cert.fork (-6444) (-6458) Cert.stop Cert.stop)
                                            Cert.stop)
                                          Cert.stop)))
                                    Cert.stop) Cert.stop) Cert.stop))
                            (Cert.fork (-27224) (-27222) Cert.stop Cert.stop))
                          Cert.stop) Cert.stop) Cert.stop))
                  (Cert.fork (-28521) (-14475) Cert.stop Cert.stop)))
                Cert.stop) Cert.stop)
            (Cert.fork (-10931) (-24993) Cert.stop Cert.stop))))))

def certHuge : Cert := Cert.fork
  (-13333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333611)
  (-39999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999729)
  Cert.stop Cert.stop

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checked5288 : check (fatalState 5288) cert5288=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checkedHuge : check (fatalState (10^100)) certHuge=true := by decide +kernel

/-- A nontrivial reverse tree with depth 23 excludes every root index. -/
theorem excluded5288 (i : Nat) : run i≠some (.D (targetX 5287) (targetY 5287)) :=
  check_excludes cert5288 _ _ _ (fatalState_rep 5287 (by decide)) checked5288 i

/-- Even a target with exponent 10^100 can be excluded without constructing its counters. -/
theorem excludedHuge (i : Nat) : run i≠some (.D (targetX (10^100-1)) (targetY (10^100-1))) := by
  have h := fatalState_rep (10^100-1) (by decide +kernel)
  have he : 10^100-1+1=10^100 := by decide +kernel
  rw [he] at h
  exact check_excludes certHuge _ _ _ h checkedHuge i

#print axioms fatalState_rep
#print axioms checked5288
#print axioms checkedHuge
#print axioms excluded5288
#print axioms excludedHuge
end BB6.Agent41NearPower
