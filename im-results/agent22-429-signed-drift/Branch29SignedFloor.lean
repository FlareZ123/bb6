import SignedSource
import Lean.Elab.Tactic.Omega

/-!
# Source-rooted terminal-burst floor from closed signed inverse trees

The exact 29(mod32) last-reset terminal equation is
  128q + 3n + 131 = 3*2^(n+2), n>=18.
It forces n=127+128k and q+(3k+4)=3*2^(n-5).

For the first one thousand k, a single kernel-reduced finite list
establishes closed signed inverse trees at depth28. Applying the
source-connected finite-precision theorem in SignedSource (with e=20,
n-5>=122 and size bound) rules out all such last-reset candidates.
Consequently a genuine blank-reachable terminal-burst prestate must
have n>=128127. This is a necessary lower bound on that feeder, not
a #429 nonhalting or BB(6) result.
-/

namespace BB429Branch29SignedFloor
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def signedAt (k : Nat) : Bool :=
  Signed429.signedCert 28 (29-32*(((3*k+4):Nat):Int))
    (55-64*(((3*k+4):Nat):Int))

private theorem prefix1000 :
    (List.range 1000).all (fun k => signedAt k) = true := by
  decide +kernel

/-- All authentically blank-root-reachable branch29 final-burst sources
obey the necessary length bound n>=128127. -/
theorem rooted_branch29_final_burst_floor128127
    (q n : Nat) (hn : 18≤n)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    128127 ≤ n := by
  by_cases hbig : 128127 ≤ n
  · exact hbig
  · have hshort : n < 128127 := by omega
    have hpow : 2^(n+2)=128*2^(n-5) := by
      have hsplit : n+2=7+(n-5) := by omega
      rw [hsplit,Nat.pow_add]
    have heq' : 128*q+3*n+131=384*2^(n-5) := by
      rw [hpow] at heq
      omega
    have hmod : (128*q+3*n+131)%128=0 := by
      rw [heq']
      omega
    let k := n/128
    have hnmod : n%128=127 := by omega
    have hnform : n=128*k+127 := by dsimp [k]; omega
    have hk : k<1000 := by omega
    let c := 3*k+4
    have hq : q+c=3*2^(n-5) := by
      dsimp [c]
      omega
    have hcert : Signed429.signedCert 28
        (29-32*(c:Int)) (55-64*(c:Int))=true := by
      change signedAt k = true
      exact (List.all_eq_true.mp prefix1000) k (List.mem_range.mpr hk)
    have hsize : 128*(c:Int)-97+11*(28:Int)≤(2:Int)^20 := by
      have hh : (2:Int)^20=1048576 := by decide
      rw [hh]
      dsimp [c]
      omega
    have hex := Signed429.branch29_cert_excluded q c 28 20 (n-5)
      (by dsimp [c]; omega) (by decide) (by omega)
      hsize hq hcert
    exact False.elim (hex hroot)

#print axioms rooted_branch29_final_burst_floor128127
end BB429Branch29SignedFloor
