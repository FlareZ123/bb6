import SignedSource
import Lean.Elab.Tactic.Omega

/-!
# Source-connected one-million-plus terminal-burst floor on #429 branch29

The exact Diophantine condition n>=18, 128q+3n+131=3*2^(n+2)
forces n=127+128k and q+(3k+4)=3*2^(n-5).

Ten independently kernel-reduced chunks of one thousand k-values
certify the exact Signed429.signedCert 32 Boolean. The source-connected
finite-precision lifting theorem then excludes every k<10000: e=26,
d=32, precision 2d+e=90<=n-5 and 2^e exceeds the symbolic size bound.

This establishes the necessary blank-root final-burst floor n>=1280127.
It is no claim of halting or of the exact six-state Busy Beaver value.
-/

namespace BB429Branch29SignedFloor10k
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def signedAt (k : Nat) : Bool :=
  Signed429.signedCert 32 (29-32*(((3*k+4):Nat):Int))
    (55-64*(((3*k+4):Nat):Int))

private theorem chunk0 :
    (List.range 1000).all (fun j => signedAt (0*1000+j)) = true := by
  decide +kernel

private theorem chunk1 :
    (List.range 1000).all (fun j => signedAt (1*1000+j)) = true := by
  decide +kernel

private theorem chunk2 :
    (List.range 1000).all (fun j => signedAt (2*1000+j)) = true := by
  decide +kernel

private theorem chunk3 :
    (List.range 1000).all (fun j => signedAt (3*1000+j)) = true := by
  decide +kernel

private theorem chunk4 :
    (List.range 1000).all (fun j => signedAt (4*1000+j)) = true := by
  decide +kernel

private theorem chunk5 :
    (List.range 1000).all (fun j => signedAt (5*1000+j)) = true := by
  decide +kernel

private theorem chunk6 :
    (List.range 1000).all (fun j => signedAt (6*1000+j)) = true := by
  decide +kernel

private theorem chunk7 :
    (List.range 1000).all (fun j => signedAt (7*1000+j)) = true := by
  decide +kernel

private theorem chunk8 :
    (List.range 1000).all (fun j => signedAt (8*1000+j)) = true := by
  decide +kernel

private theorem chunk9 :
    (List.range 1000).all (fun j => signedAt (9*1000+j)) = true := by
  decide +kernel

private theorem prefix10000 (k : Nat) (hk : k < 10000) :
    signedAt k = true := by
  let i := k/1000
  let j := k%1000
  have hsplit : k=1000*i+j := by dsimp [i,j]; omega
  have hi : i<10 := by omega
  have hj : j<1000 := by dsimp [j]; omega
  have hcases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
  · have hq : k=0*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk0) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=1*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk1) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=2*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk2) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=3*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk3) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=4*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk4) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=5*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk5) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=6*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk6) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=7*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk7) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=8*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk8) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert
  · have hq : k=9*1000+j := by omega
    have hcert := (List.all_eq_true.mp chunk9) j (List.mem_range.mpr hj)
    simpa only [hq] using hcert

/-- Every blank-reachable #429 branch29 final-burst source subject
to the exact reset equation has final-burst length at least 1280127. -/
theorem rooted_branch29_final_burst_floor1280127
    (q n : Nat) (hn : 18≤n)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    1280127 ≤ n := by
  by_cases hbig : 1280127 ≤ n
  · exact hbig
  · have hshort : n < 1280127 := by omega
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
    have hk : k<10000 := by omega
    let c := 3*k+4
    have hq : q+c=3*2^(n-5) := by
      dsimp [c]
      omega
    have hcert : Signed429.signedCert 32
        (29-32*(c:Int)) (55-64*(c:Int))=true := by
      change signedAt k = true
      exact prefix10000 k hk
    have hsize : 128*(c:Int)-97+11*(32:Int)≤(2:Int)^26 := by
      have hh : (2:Int)^26=67108864 := by decide
      rw [hh]
      dsimp [c]
      omega
    have hex := Signed429.branch29_cert_excluded q c 32 26 (n-5)
      (by dsimp [c]; omega) (by decide) (by omega)
      hsize hq hcert
    exact False.elim (hex hroot)

#print axioms rooted_branch29_final_burst_floor1280127
end BB429Branch29SignedFloor10k
