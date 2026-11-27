import SignedSource
import Branch29Roster31
import Lean.Elab.Tactic.Omega

/-!
# Source-sound terminal burst lower bound 128,000,127 for branch29
Combines a true blank-root 31/2048 residue invariant with 31 finite
kernel-checkable signed inverse-tree certificates, each for a whole
arithmetic progression of burst index k and any unbounded input q.
Every k<1,000,000 satisfying the necessary modulo-2048 filter has
signed tree depth at most 48. The finite precision theorem lifts all
these complete signed trees to genuine large dyadic targets.
-/
namespace BB429Branch29SignedFloor1M
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def admissibleK : List Nat := [63,126,254,278,319,383,398,463,639,719,767,870,894,1023,1046,1071,1126,1174,1199,1231,1327,1382,1430,1599,1638,1678,1855,1934,1967,2046,2047]

private def signedAt (k : Nat) : Bool :=
  Signed429.signedCert 48 (29-32*(((3*k+4):Nat):Int))
    (55-64*(((3*k+4):Nat):Int))

private theorem residue_decision :
    (List.range 2048).all (fun r =>
      decide ((∃ s ∈ BB429Branch29Roster31.surviving2048,
        (s+3*r+4)%2048=0) → r∈admissibleK)) = true := by
  decide +kernel

private theorem k_allowed (q k : Nat) (hqmod : q%2048 ∈ BB429Branch29Roster31.surviving2048)
    (hsum : (q+3*k+4)%2048=0) : k%2048 ∈ admissibleK := by
  have hr : k%2048<2048 := Nat.mod_lt _ (by decide)
  have hpart := (List.all_eq_true.mp residue_decision) (k%2048)
    (List.mem_range.mpr hr)
  have hfinite : (∃ s ∈ BB429Branch29Roster31.surviving2048,
          (s+3*(k%2048)+4)%2048=0) → k%2048∈admissibleK :=
    of_decide_eq_true hpart
  apply hfinite
  refine ⟨q%2048,hqmod,?_⟩
  omega

private theorem chunk63 :
    (List.range 489).all (fun j => signedAt (2048*j+63)) = true := by
  decide +kernel

private theorem chunk126 :
    (List.range 489).all (fun j => signedAt (2048*j+126)) = true := by
  decide +kernel

private theorem chunk254 :
    (List.range 489).all (fun j => signedAt (2048*j+254)) = true := by
  decide +kernel

private theorem chunk278 :
    (List.range 489).all (fun j => signedAt (2048*j+278)) = true := by
  decide +kernel

private theorem chunk319 :
    (List.range 489).all (fun j => signedAt (2048*j+319)) = true := by
  decide +kernel

private theorem chunk383 :
    (List.range 489).all (fun j => signedAt (2048*j+383)) = true := by
  decide +kernel

private theorem chunk398 :
    (List.range 489).all (fun j => signedAt (2048*j+398)) = true := by
  decide +kernel

private theorem chunk463 :
    (List.range 489).all (fun j => signedAt (2048*j+463)) = true := by
  decide +kernel

private theorem chunk639 :
    (List.range 489).all (fun j => signedAt (2048*j+639)) = true := by
  decide +kernel

private theorem chunk719 :
    (List.range 489).all (fun j => signedAt (2048*j+719)) = true := by
  decide +kernel

private theorem chunk767 :
    (List.range 489).all (fun j => signedAt (2048*j+767)) = true := by
  decide +kernel

private theorem chunk870 :
    (List.range 489).all (fun j => signedAt (2048*j+870)) = true := by
  decide +kernel

private theorem chunk894 :
    (List.range 489).all (fun j => signedAt (2048*j+894)) = true := by
  decide +kernel

private theorem chunk1023 :
    (List.range 489).all (fun j => signedAt (2048*j+1023)) = true := by
  decide +kernel

private theorem chunk1046 :
    (List.range 489).all (fun j => signedAt (2048*j+1046)) = true := by
  decide +kernel

private theorem chunk1071 :
    (List.range 489).all (fun j => signedAt (2048*j+1071)) = true := by
  decide +kernel

private theorem chunk1126 :
    (List.range 489).all (fun j => signedAt (2048*j+1126)) = true := by
  decide +kernel

private theorem chunk1174 :
    (List.range 489).all (fun j => signedAt (2048*j+1174)) = true := by
  decide +kernel

private theorem chunk1199 :
    (List.range 489).all (fun j => signedAt (2048*j+1199)) = true := by
  decide +kernel

private theorem chunk1231 :
    (List.range 489).all (fun j => signedAt (2048*j+1231)) = true := by
  decide +kernel

private theorem chunk1327 :
    (List.range 489).all (fun j => signedAt (2048*j+1327)) = true := by
  decide +kernel

private theorem chunk1382 :
    (List.range 489).all (fun j => signedAt (2048*j+1382)) = true := by
  decide +kernel

private theorem chunk1430 :
    (List.range 489).all (fun j => signedAt (2048*j+1430)) = true := by
  decide +kernel

private theorem chunk1599 :
    (List.range 489).all (fun j => signedAt (2048*j+1599)) = true := by
  decide +kernel

private theorem chunk1638 :
    (List.range 489).all (fun j => signedAt (2048*j+1638)) = true := by
  decide +kernel

private theorem chunk1678 :
    (List.range 489).all (fun j => signedAt (2048*j+1678)) = true := by
  decide +kernel

private theorem chunk1855 :
    (List.range 489).all (fun j => signedAt (2048*j+1855)) = true := by
  decide +kernel

private theorem chunk1934 :
    (List.range 489).all (fun j => signedAt (2048*j+1934)) = true := by
  decide +kernel

private theorem chunk1967 :
    (List.range 489).all (fun j => signedAt (2048*j+1967)) = true := by
  decide +kernel

private theorem chunk2046 :
    (List.range 489).all (fun j => signedAt (2048*j+2046)) = true := by
  decide +kernel

private theorem chunk2047 :
    (List.range 489).all (fun j => signedAt (2048*j+2047)) = true := by
  decide +kernel

private theorem signed_at_of_allowed (k : Nat) (hk : k < 1000000)
    (hres : k%2048 ∈ admissibleK) : signedAt k = true := by
  have hj : k/2048 < 489 := by omega
  have hcases : k%2048=63 ∨ k%2048=126 ∨ k%2048=254 ∨ k%2048=278 ∨ k%2048=319 ∨ k%2048=383 ∨ k%2048=398 ∨ k%2048=463 ∨ k%2048=639 ∨ k%2048=719 ∨ k%2048=767 ∨ k%2048=870 ∨ k%2048=894 ∨ k%2048=1023 ∨ k%2048=1046 ∨ k%2048=1071 ∨ k%2048=1126 ∨ k%2048=1174 ∨ k%2048=1199 ∨ k%2048=1231 ∨ k%2048=1327 ∨ k%2048=1382 ∨ k%2048=1430 ∨ k%2048=1599 ∨ k%2048=1638 ∨ k%2048=1678 ∨ k%2048=1855 ∨ k%2048=1934 ∨ k%2048=1967 ∨ k%2048=2046 ∨ k%2048=2047 := by
    simpa only [admissibleK, List.mem_cons, List.not_mem_nil, or_false] using hres
  rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30
  · have hkform : k=2048*(k/2048)+63 := by omega
    have hh := (List.all_eq_true.mp chunk63) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+126 := by omega
    have hh := (List.all_eq_true.mp chunk126) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+254 := by omega
    have hh := (List.all_eq_true.mp chunk254) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+278 := by omega
    have hh := (List.all_eq_true.mp chunk278) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+319 := by omega
    have hh := (List.all_eq_true.mp chunk319) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+383 := by omega
    have hh := (List.all_eq_true.mp chunk383) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+398 := by omega
    have hh := (List.all_eq_true.mp chunk398) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+463 := by omega
    have hh := (List.all_eq_true.mp chunk463) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+639 := by omega
    have hh := (List.all_eq_true.mp chunk639) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+719 := by omega
    have hh := (List.all_eq_true.mp chunk719) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+767 := by omega
    have hh := (List.all_eq_true.mp chunk767) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+870 := by omega
    have hh := (List.all_eq_true.mp chunk870) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+894 := by omega
    have hh := (List.all_eq_true.mp chunk894) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1023 := by omega
    have hh := (List.all_eq_true.mp chunk1023) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1046 := by omega
    have hh := (List.all_eq_true.mp chunk1046) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1071 := by omega
    have hh := (List.all_eq_true.mp chunk1071) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1126 := by omega
    have hh := (List.all_eq_true.mp chunk1126) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1174 := by omega
    have hh := (List.all_eq_true.mp chunk1174) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1199 := by omega
    have hh := (List.all_eq_true.mp chunk1199) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1231 := by omega
    have hh := (List.all_eq_true.mp chunk1231) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1327 := by omega
    have hh := (List.all_eq_true.mp chunk1327) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1382 := by omega
    have hh := (List.all_eq_true.mp chunk1382) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1430 := by omega
    have hh := (List.all_eq_true.mp chunk1430) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1599 := by omega
    have hh := (List.all_eq_true.mp chunk1599) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1638 := by omega
    have hh := (List.all_eq_true.mp chunk1638) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1678 := by omega
    have hh := (List.all_eq_true.mp chunk1678) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1855 := by omega
    have hh := (List.all_eq_true.mp chunk1855) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1934 := by omega
    have hh := (List.all_eq_true.mp chunk1934) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+1967 := by omega
    have hh := (List.all_eq_true.mp chunk1967) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+2046 := by omega
    have hh := (List.all_eq_true.mp chunk2046) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh
  · have hkform : k=2048*(k/2048)+2047 := by omega
    have hh := (List.all_eq_true.mp chunk2047) (k/2048) (List.mem_range.mpr hj)
    rw [hkform]
    exact hh

/-- A complete true-blank-root necessary lower bound on the
branch29 final burst under its exact terminal equation. -/
theorem rooted_branch29_final_burst_floor128000127
    (q n : Nat) (hn : 18≤n)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    128000127 ≤ n := by
  by_cases hbig : 128000127 ≤ n
  · exact hbig
  · have hshort : n < 128000127 := by omega
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
    have hk : k<1000000 := by omega
    let c := 3*k+4
    have hq : q+c=3*2^(n-5) := by
      dsimp [c]
      omega
    have hpdiv' : 2^11 ∣ 2^(n-5) := Nat.pow_dvd_pow 2 (by omega)
    have hpdiv : 2048 ∣ 2^(n-5) := by simpa using hpdiv'
    have hpmod : (2^(n-5))%2048=0 := Nat.mod_eq_zero_of_dvd hpdiv
    have hsum : (q+3*k+4)%2048=0 := by dsimp [c] at hq; omega
    have hroster := BB429Branch29Roster31.rooted_29_q_31_mod2048 q hroot
    have hallowed : k%2048∈admissibleK :=
      k_allowed q k hroster.2 hsum
    have hnonzero : 0 ∉ admissibleK := by decide
    have hkpos : 1≤k := by
      have hz : k%2048≠0 := by intro h; exact hnonzero (h ▸ hallowed)
      omega
    have hcert : Signed429.signedCert 48
        (29-32*(c:Int)) (55-64*(c:Int))=true := by
      change signedAt k = true
      exact signed_at_of_allowed k hk hallowed
    have hsize : 128*(c:Int)-97+11*(48:Int)≤(2:Int)^30 := by
      have hh : (2:Int)^30=1073741824 := by decide
      rw [hh]
      dsimp [c]
      omega
    have hex := Signed429.branch29_cert_excluded q c 48 30 (n-5)
      (by dsimp [c]; omega) (by decide) (by omega)
      hsize hq hcert
    exact False.elim (hex hroot)

#print axioms rooted_branch29_final_burst_floor128000127
end BB429Branch29SignedFloor1M
