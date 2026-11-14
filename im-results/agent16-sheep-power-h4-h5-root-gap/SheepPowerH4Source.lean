import Std
import SheepEvenReachInverse
import SpecialSourceNoPower
import ResidueGap
import EvenSourceBridge

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-!
# Source-level fourth 3-adic stratum exclusion for Sheep

For m outside the six direct-parent congruence classes, the authentic
blank-even orbit from 10 cannot reach 2^(54*m).  The proof starts from the
original even-section inverse split, excludes the exceptional source, and
uses a complete finite-cycle classification of every generic source
valuation h<=4 and every low 2-adic valuation a.  The high-a tail is excluded
by the signed-power residue gap.

This is the original-source counterpart of the arithmetic Gate4 certificate
in the Agent16 h4/h5 root-gap dossier.
-/

namespace SheepPowerH4Source

theorem pow_mod_period (m period r k : Nat)
    (hm : 1 < m) (hp : 2^period % m = 1) :
    2^(r + period*k) % m = 2^r % m := by
  have hpow : (2^period)^k % m = 1 := by
    rw [Nat.pow_mod, hp]
    simp [Nat.mod_eq_of_lt hm]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hpow]
  simp

theorem reduce_hit (m base shift cycle t : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(54*cycle)%m=1) :
    (2^(54*t+base)+shift)%m =
      (2^(54*(t%cycle)+base)+shift)%m := by
  have hk : t=t%cycle+cycle*(t/cycle) := by
    have hdiv := Nat.mod_add_div t cycle
    omega
  have heq : 54*t+base =
      (54*(t%cycle)+base)+(54*cycle)*(t/cycle) := by
    calc
      54*t+base = 54*(t%cycle+cycle*(t/cycle))+base := by rw [←hk]
      _ = _ := by ring
  have hpowers : 2^(54*t+base)%m =
      2^(54*(t%cycle)+base)%m := by
    rw [heq, pow_mod_period m (54*cycle)
      (54*(t%cycle)+base) (t/cycle) hm hp]
  simp only [Nat.add_mod, Nat.mod_mod, hpowers]

theorem no_generic (m base shift C cycle t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(54*cycle)%m=1)
    (hc : ∀ x : Fin cycle,
      (2^(54*x.val+base)+shift)%m ≠ C%m)
    (heq : m*v+C=2^(54*t+base)+shift) : False := by
  have hh : (2^(54*(t%cycle)+base)+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh

theorem only_class (m base shift C cycle good t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(54*cycle)%m=1)
    (hc : ∀ x : Fin cycle,
      (2^(54*x.val+base)+shift)%m=C%m → x.val=good)
    (heq : m*v+C=2^(54*t+base)+shift) :
    t%cycle=good := by
  have hh : (2^(54*(t%cycle)+base)+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh

private theorem stable_gap (D S A : Nat)
    (hA : 2 ≤ A) (hD : 0 < D)
    (hbase : 1 < D*(2*A-3)+S ∧ D*(2*A-3)+S < 2^A)
    (hdbl : 2*D ≤ 2^A) :
    ∀ a : Nat, A ≤ a →
    1 < D*(2*a-3)+S ∧ D*(2*a-3)+S < 2^a ∧ 2*D ≤ 2^a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    by_cases heq : a=A
    · subst a
      exact ⟨hbase.1, hbase.2, hdbl⟩
    have hh : A≤a-1 := by omega
    have hlt : a-1<a := by omega
    have hprev := ih (a-1) hlt hh
    have hrepl : a-1+1=a := by omega
    have haexpr : 2*(a-1+1)-3 = 2*a-3 := by omega
    have hp : 2^a = 2*2^(a-1) := by
      calc
        2^a = 2^((a-1)+1) := by rw [hrepl]
        _ = 2*2^(a-1) := by rw [Nat.pow_succ]; omega
    have hk : D*(2*a-3)+S = (D*(2*(a-1)-3)+S)+2*D := by
      have hsub : 2*a-3 = (2*(a-1)-3)+2 := by omega
      rw [hsub, Nat.mul_add]
      omega
    rw [hk, hp]
    constructor
    · omega
    constructor
    · omega
    · omega

theorem high_cutoff (h a : Nat) (hh : h ≤ 4)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a) :
    1 < 3^h*(2*a-3)+2^(h+1) ∧
    3^h*(2*a-3)+2^(h+1) < 2^a := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 from by omega)
    with h0|h1|h2|h3|h4
  · subst h
    have hA : 2 ≤ a := by simpa using ha
    have hg := stable_gap 1 2 2 (by decide) (by decide)
      (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 5 ≤ a := by simpa using ha
    have hg := stable_gap 3 4 5 (by decide) (by decide)
      (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 7 ≤ a := by simpa using ha
    have hg := stable_gap 9 8 7 (by decide) (by decide)
      (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 9 ≤ a := by simpa using ha
    have hg := stable_gap 27 16 9 (by decide) (by decide)
      (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 11 ≤ a := by simpa using ha
    have hg := stable_gap 81 32 11 (by decide) (by decide)
      (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩

private theorem odd_three_pow (h : Nat) : ((3:Int)^h)%2=1 := by
  induction h with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ, Int.mul_emod, ih]
    decide

theorem no_high_source (h a t v : Nat) (hh : h ≤ 4)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(54*t+h+1)+3*3^h) : False := by
  have hgap := high_cutoff h a hh ha
  have ha2 : 2≤a := by split at ha <;> omega
  let K : Int := (3:Int)^h*(2*(a:Int)-3)+(2:Int)^(h+1)
  have hK_eq : K = ((3^h*(2*a-3)+2^(h+1):Nat):Int) := by
    dsimp [K]
    have hsub : (↑(2*a-3):Int) = 2*(a:Int)-3 := by omega
    rw [←hsub]
  have hKlow : 1 < K := by
    rw [hK_eq]
    exact_mod_cast hgap.1
  have hKhigh : K < (2:Int)^a := by
    rw [hK_eq]
    exact_mod_cast hgap.2
  have hKodd : K%2=1 := by
    dsimp [K]
    have hodd := odd_three_pow h
    have heven : ((2:Int)^(h+1))%2=0 := by
      rw [Int.pow_succ, Int.mul_emod]
      simp
    have hlinodd : (2*(a:Int)-3)%2=1 := by omega
    rw [Int.add_emod, Int.mul_emod, hodd, hlinodd, heven]
    decide
  have heq_int : (3:Int)^h*((2:Int)^(a+1)+1)*(v:Int) +
      2*(a:Int)*(3:Int)^h + (2:Int)^(h+1)
      = (2:Int)^(54*t+h+1)+3*(3:Int)^h := by
    exact_mod_cast heq
  have hdiv : ((2:Int)^(a+1)+1) ∣ (2:Int)^(54*t+h+1)-K := by
    refine ⟨(3:Int)^h*(v:Int), ?_⟩
    dsimp [K]
    let D : Int := (3:Int)^h
    let B : Int := ((2:Int)^(a+1)+1)
    let N : Int := (2:Int)^(54*t+h+1)
    let S : Int := (2:Int)^(h+1)
    have hmul : D*(2*(a:Int)-3) = 2*(a:Int)*D-3*D := by
      dsimp [D]
      rw [Int.mul_sub]
      have h1 : (3:Int)^h*(2*(a:Int))= 2*(a:Int)*(3:Int)^h := by ac_rfl
      rw [h1]
      have h2 : (3:Int)^h*3=3*(3:Int)^h := by ac_rfl
      rw [h2]
    have hmul2 : D*B*(v:Int)=B*(D*(v:Int)) := by ac_rfl
    have heq2 : D*B*(v:Int)+2*(a:Int)*D+S=N+3*D := by
      simpa only [D, B, N, S] using heq_int
    calc
      N-(D*(2*(a:Int)-3)+S) = D*B*(v:Int) := by
        rw [hmul]
        omega
      _ = B*(D*(v:Int)) := hmul2
  exact (SheepOddGap.no_power_signed_small_odd a K hKlow hKodd hKhigh
    (54*t+h+1)).1 hdiv

theorem no_h0_a1 (t v : Nat)
    (heq : 5*v+4=2^(54*t+1)+3) : False := by
  exact no_generic 5 1 3 4 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h1_a1 (t v : Nat)
    (heq : 15*v+10=2^(54*t+2)+9) : t%2=1 := by
  exact only_class 15 2 9 10 2 1 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h1_a2 (t v : Nat)
    (heq : 27*v+16=2^(54*t+2)+9) : False := by
  exact no_generic 27 2 9 16 1 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h1_a3 (t v : Nat)
    (heq : 51*v+22=2^(54*t+2)+9) : t%4=2 := by
  exact only_class 51 2 9 22 4 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h1_a4 (t v : Nat)
    (heq : 99*v+28=2^(54*t+2)+9) : False := by
  exact no_generic 99 2 9 28 5 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a1 (t v : Nat)
    (heq : 45*v+26=2^(54*t+3)+27) : False := by
  exact no_generic 45 3 27 26 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a2 (t v : Nat)
    (heq : 81*v+44=2^(54*t+3)+27) : False := by
  exact no_generic 81 3 27 44 1 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a3 (t v : Nat)
    (heq : 153*v+62=2^(54*t+3)+27) : False := by
  exact no_generic 153 3 27 62 4 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a4 (t v : Nat)
    (heq : 297*v+80=2^(54*t+3)+27) : False := by
  exact no_generic 297 3 27 80 5 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a5 (t v : Nat)
    (heq : 585*v+98=2^(54*t+3)+27) : False := by
  exact no_generic 585 3 27 98 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h2_a6 (t v : Nat)
    (heq : 1161*v+116=2^(54*t+3)+27) : False := by
  exact no_generic 1161 3 27 116 7 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h3_a1 (t v : Nat)
    (heq : 135*v+70=2^(54*t+4)+81) : t%2=1 := by
  exact only_class 135 4 81 70 2 1 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a2 (t v : Nat)
    (heq : 243*v+124=2^(54*t+4)+81) : False := by
  exact no_generic 243 4 81 124 3 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a3 (t v : Nat)
    (heq : 459*v+178=2^(54*t+4)+81) : False := by
  exact no_generic 459 4 81 178 4 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a4 (t v : Nat)
    (heq : 891*v+232=2^(54*t+4)+81) : False := by
  exact no_generic 891 4 81 232 5 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a5 (t v : Nat)
    (heq : 1755*v+286=2^(54*t+4)+81) : False := by
  exact no_generic 1755 4 81 286 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h3_a6 (t v : Nat)
    (heq : 3483*v+340=2^(54*t+4)+81) : t%7=2 := by
  exact only_class 3483 4 81 340 7 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a7 (t v : Nat)
    (heq : 6939*v+394=2^(54*t+4)+81) : False := by
  exact no_generic 6939 4 81 394 8 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h3_a8 (t v : Nat)
    (heq : 13851*v+448=2^(54*t+4)+81) : False := by
  exact no_generic 13851 4 81 448 9 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a1 (t v : Nat)
    (heq : 405*v+194=2^(54*t+5)+243) : False := by
  exact no_generic 405 5 243 194 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h4_a2 (t v : Nat)
    (heq : 729*v+356=2^(54*t+5)+243) : t%9=8 := by
  exact only_class 729 5 243 356 9 8 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a3 (t v : Nat)
    (heq : 1377*v+518=2^(54*t+5)+243) : False := by
  exact no_generic 1377 5 243 518 4 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem only_h4_a4 (t v : Nat)
    (heq : 2673*v+680=2^(54*t+5)+243) : t%15=7 := by
  exact only_class 2673 5 243 680 15 7 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a5 (t v : Nat)
    (heq : 5265*v+842=2^(54*t+5)+243) : False := by
  exact no_generic 5265 5 243 842 2 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a6 (t v : Nat)
    (heq : 10449*v+1004=2^(54*t+5)+243) : False := by
  exact no_generic 10449 5 243 1004 7 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a7 (t v : Nat)
    (heq : 20817*v+1166=2^(54*t+5)+243) : False := by
  exact no_generic 20817 5 243 1166 8 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a8 (t v : Nat)
    (heq : 41553*v+1328=2^(54*t+5)+243) : False := by
  exact no_generic 41553 5 243 1328 9 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a9 (t v : Nat)
    (heq : 83025*v+1490=2^(54*t+5)+243) : False := by
  exact no_generic 83025 5 243 1490 10 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_h4_a10 (t v : Nat)
    (heq : 165969*v+1652=2^(54*t+5)+243) : False := by
  exact no_generic 165969 5 243 1652 33 t v
    (by norm_num) (by norm_num) (by norm_num) (by decide) heq

theorem no_generic_forbidden (h a t v : Nat)
    (hh : h ≤ 4) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a≤2*h+2)
    (ht2 : t%2≠1) (ht4 : t%4≠2) (ht7 : t%7≠2)
    (ht9 : t%9≠8) (ht15 : t%15≠7)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(54*t+h+1)+3*3^h) : False := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 from by omega)
    with h0|h1|h2|h3|h4
  · subst h
    have ha1 : a=1 := hzero rfl
    subst a
    have hrow : 5*v+4=2^(54*t+1)+3 := by
      simpa [Nat.add_assoc] using heq
    exact no_h0_a1 t v hrow
  · subst h
    have haBound : a≤4 := by
      have hp := hpos (by omega)
      omega
    interval_cases a
    · have hrow : 15*v+10=2^(54*t+2)+9 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%2=1 := only_h1_a1 t v hrow
      omega
    · have hrow : 27*v+16=2^(54*t+2)+9 := by
        simpa [Nat.add_assoc] using heq
      exact no_h1_a2 t v hrow
    · have hrow : 51*v+22=2^(54*t+2)+9 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%4=2 := only_h1_a3 t v hrow
      omega
    · have hrow : 99*v+28=2^(54*t+2)+9 := by
        simpa [Nat.add_assoc] using heq
      exact no_h1_a4 t v hrow
  · subst h
    have haBound : a≤6 := by
      have hp := hpos (by omega)
      omega
    interval_cases a
    · have hrow : 45*v+26=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a1 t v hrow
    · have hrow : 81*v+44=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a2 t v hrow
    · have hrow : 153*v+62=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a3 t v hrow
    · have hrow : 297*v+80=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a4 t v hrow
    · have hrow : 585*v+98=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a5 t v hrow
    · have hrow : 1161*v+116=2^(54*t+3)+27 := by
        simpa [Nat.add_assoc] using heq
      exact no_h2_a6 t v hrow
  · subst h
    have haBound : a≤8 := by
      have hp := hpos (by omega)
      omega
    interval_cases a
    · have hrow : 135*v+70=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%2=1 := only_h3_a1 t v hrow
      omega
    · have hrow : 243*v+124=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a2 t v hrow
    · have hrow : 459*v+178=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a3 t v hrow
    · have hrow : 891*v+232=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a4 t v hrow
    · have hrow : 1755*v+286=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a5 t v hrow
    · have hrow : 3483*v+340=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%7=2 := only_h3_a6 t v hrow
      omega
    · have hrow : 6939*v+394=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a7 t v hrow
    · have hrow : 13851*v+448=2^(54*t+4)+81 := by
        simpa [Nat.add_assoc] using heq
      exact no_h3_a8 t v hrow
  · subst h
    have haBound : a≤10 := by
      have hp := hpos (by omega)
      omega
    interval_cases a
    · have hrow : 405*v+194=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a1 t v hrow
    · have hrow : 729*v+356=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%9=8 := only_h4_a2 t v hrow
      omega
    · have hrow : 1377*v+518=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a3 t v hrow
    · have hrow : 2673*v+680=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      have hclass : t%15=7 := only_h4_a4 t v hrow
      omega
    · have hrow : 5265*v+842=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a5 t v hrow
    · have hrow : 10449*v+1004=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a6 t v hrow
    · have hrow : 20817*v+1166=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a7 t v hrow
    · have hrow : 41553*v+1328=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a8 t v hrow
    · have hrow : 83025*v+1490=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a9 t v hrow
    · have hrow : 165969*v+1652=2^(54*t+5)+243 := by
        simpa [Nat.add_assoc] using heq
      exact no_h4_a10 t v hrow

theorem no_generic_all_a (h a t v : Nat)
    (hh : h ≤ 4) (ha : 1 ≤ a)
    (ht2 : t%2≠1) (ht4 : t%4≠2) (ht7 : t%7≠2)
    (ht9 : t%9≠8) (ht15 : t%15≠7)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(54*t+h+1)+3*3^h) : False := by
  by_cases high : (if h=0 then 2 else 2*h+3) ≤ a
  · exact no_high_source h a t v hh high heq
  · have hzero : h=0 → a=1 := by
      intro hz
      subst h
      simp at high
      omega
    have hpos : 0<h → a≤2*h+2 := by
      intro hp
      have hnz : h≠0 := by omega
      simp [hnz] at high
      omega
    exact no_generic_forbidden h a t v hh ha hzero hpos
      ht2 ht4 ht7 ht9 ht15 heq

/-- The fourth 3-adic stratum's direct-parent-free exponent gate. -/
def Gate4 (m : Nat) : Prop :=
  m%3≠0 ∧ m%2≠1 ∧ m%4≠2 ∧ m%7≠2 ∧ m%9≠8 ∧ m%15≠7

theorem target_hidden_le4 (m h u : Nat) (hm3 : m%3≠0)
    (heq : 2^(54*m)=1+3^h*u) : h≤4 := by
  by_contra hh
  have h5 : 5≤h := by omega
  have hdiv : 243 ∣ 3^h*u := by
    refine ⟨3^(h-5)*u, ?_⟩
    have hsplit : h=5+(h-5) := by omega
    rw [hsplit, Nat.pow_add]
    norm_num
    ring
  have hmod : 2^(54*m)%243=1 := by
    rw [heq, Nat.add_mod]
    have hz : (3^h*u)%243=0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [hz]
    norm_num
  have hperiod : 2^162%243=1 := by norm_num
  have hred : 2^(54*m)%243=2^((54*m)%162)%243 :=
    pow_mod_reduce 243 162 (54*m) (by norm_num) hperiod
  have hexp : (54*m)%162=54*(m%3) := by omega
  rw [hred, hexp] at hmod
  have hmres : m%3=1 ∨ m%3=2 := by omega
  rcases hmres with hm1|hm2
  · rw [hm1] at hmod
    norm_num at hmod
  · rw [hm2] at hmod
    norm_num at hmod

theorem blank_even_cannot_hit_gate4 (m : Nat) (hm : Gate4 m) :
    ¬ SheepEvenReach 10 (2^(54*m)) := by
  rcases hm with ⟨hm3,hm2,hm4,hm7,hm9,hm15⟩
  intro hreach
  rcases SheepEvenReachInverse.blank_even_inverse_cases hreach with hspec | hgen
  · rcases hspec with ⟨a,h,u,ha,hfactor,hu,hx,hy⟩
    exact Agent17SheepSpecial.special_no_even_power a h u (54*m)
      ha hfactor hu hy.symm
  · rcases hgen with ⟨a,h,v,u,ha,hv,hvo,huo,hx,heq,hy⟩
    have hh : h≤4 := target_hidden_le4 m h u hm3 hy
    exact no_generic_all_a h a m v hh ha hm2 hm4 hm7 hm9 hm15 heq

theorem blank_even_cannot_hit_gate4_raw (m : Nat) (hm : Gate4 m) :
    ¬ BB6.SheepSource.SheepHaltsAtPower (54*m) := by
  intro hhalt
  exact blank_even_cannot_hit_gate4 m hm
    (EvenSourceBridge.sheep_halting_to_even_reach hhalt)

#print axioms target_hidden_le4
#print axioms no_high_source
#print axioms no_generic_all_a
#print axioms blank_even_cannot_hit_gate4
#print axioms blank_even_cannot_hit_gate4_raw

end SheepPowerH4Source
