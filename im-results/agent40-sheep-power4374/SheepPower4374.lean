import Std
import SheepOddGap
import SheepEvenReachInverse
import EvenSourceBridge

#eval Nat.powMod 2 4 243
#eval Nat.powMod 2 4374 243
#eval Nat.powMod 2 (4+4374*0) 243
example : Nat.powMod 2 4 243 = 16 := by decide
example : Nat.powMod 2 4374 243 = 1 := by decide

set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace BB6.Agent40.SheepPower4374

/-- Reduction of a power exponent modulo a certified multiplicative period. -/
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
    (hp : 2^(4374*cycle)%m=1) :
    (2^(base+4374*t)+shift)%m =
      (2^(base+4374*(t%cycle))+shift)%m := by
  have hk : t=t%cycle+cycle*(t/cycle) := by
    have hdiv := Nat.mod_add_div t cycle
    omega
  have heq : base+4374*t =
      (base+4374*(t%cycle))+(4374*cycle)*(t/cycle) := by
    calc
      base+4374*t = base+4374*(t%cycle+cycle*(t/cycle)) := by rw [←hk]
      _ = _ := by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have hpowers :
      2^(base+4374*t)%m = 2^(base+4374*(t%cycle))%m := by
    rw [heq, pow_mod_period m (4374*cycle)
      (base+4374*(t%cycle)) (t/cycle) hm hp]
  simp only [Nat.add_mod, Nat.mod_mod, hpowers]

theorem no_generic (m base shift C cycle t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(4374*cycle)%m=1)
    (hc : ∀ x : Fin cycle,
      (Nat.powMod 2 (base+4374*x.val) m+shift)%m ≠ C%m)
    (heq : m*v+C=2^(base+4374*t)+shift) : False := by
  have hh :
      (2^(base+4374*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  have hh' : (Nat.powMod 2 (base+4374*(t%cycle)) m + shift)%m=C%m := by
    simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using hh
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh'

theorem only_class (m base shift C cycle good t v : Nat)
    (hm : 1 < m) (hq : 0 < cycle)
    (hp : 2^(4374*cycle)%m=1)
    (hc : ∀ x : Fin cycle,
      (Nat.powMod 2 (base+4374*x.val) m+shift)%m=C%m → x.val=good)
    (heq : m*v+C=2^(base+4374*t)+shift) :
    t%cycle=good := by
  have hh :
      (2^(base+4374*(t%cycle))+shift)%m=C%m := by
    rw [←reduce_hit m base shift cycle t hm hq hp, ←heq]
    exact Nat.mul_add_mod_self_left _ _ _
  have hh' : (Nat.powMod 2 (base+4374*(t%cycle)) m + shift)%m=C%m := by
    simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using hh
  exact hc ⟨t%cycle, Nat.mod_lt t hq⟩ hh'


theorem no_h0_a1 (t v : Nat)
    (heq : 5*v+4=2^(1+4374*t)+3) : False := by
  exact no_generic 5 1 3 4 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (1+4374*x.val) 5+3)%5
          ≠ 4%5 from by decide))
    heq


theorem only_h1_a1 (t v : Nat)
    (heq : 15*v+10=2^(2+4374*t)+9) : t%2=1 := by
  exact only_class 15 2 9 10 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (2+4374*x.val) 15+9)%15
          = 10%15 → x.val=1 from by decide))
    heq


theorem no_h1_a2 (t v : Nat)
    (heq : 27*v+16=2^(2+4374*t)+9) : False := by
  exact no_generic 27 2 9 16 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (2+4374*x.val) 27+9)%27
          ≠ 16%27 from by decide))
    heq


theorem only_h1_a3 (t v : Nat)
    (heq : 51*v+22=2^(2+4374*t)+9) : t%4=2 := by
  exact only_class 51 2 9 22 4 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (2+4374*x.val) 51+9)%51
          = 22%51 → x.val=2 from by decide))
    heq


theorem no_h1_a4 (t v : Nat)
    (heq : 99*v+28=2^(2+4374*t)+9) : False := by
  exact no_generic 99 2 9 28 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (2+4374*x.val) 99+9)%99
          ≠ 28%99 from by decide))
    heq


theorem no_h2_a1 (t v : Nat)
    (heq : 45*v+26=2^(3+4374*t)+27) : False := by
  exact no_generic 45 3 27 26 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (3+4374*x.val) 45+27)%45
          ≠ 26%45 from by decide))
    heq


theorem no_h2_a2 (t v : Nat)
    (heq : 81*v+44=2^(3+4374*t)+27) : False := by
  exact no_generic 81 3 27 44 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+4374*x.val) 81+27)%81
          ≠ 44%81 from by decide))
    heq


theorem no_h2_a3 (t v : Nat)
    (heq : 153*v+62=2^(3+4374*t)+27) : False := by
  exact no_generic 153 3 27 62 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (3+4374*x.val) 153+27)%153
          ≠ 62%153 from by decide))
    heq


theorem no_h2_a4 (t v : Nat)
    (heq : 297*v+80=2^(3+4374*t)+27) : False := by
  exact no_generic 297 3 27 80 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (3+4374*x.val) 297+27)%297
          ≠ 80%297 from by decide))
    heq


theorem no_h2_a5 (t v : Nat)
    (heq : 585*v+98=2^(3+4374*t)+27) : False := by
  exact no_generic 585 3 27 98 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (3+4374*x.val) 585+27)%585
          ≠ 98%585 from by decide))
    heq


theorem no_h2_a6 (t v : Nat)
    (heq : 1161*v+116=2^(3+4374*t)+27) : False := by
  exact no_generic 1161 3 27 116 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (3+4374*x.val) 1161+27)%1161
          ≠ 116%1161 from by decide))
    heq


theorem only_h3_a1 (t v : Nat)
    (heq : 135*v+70=2^(4+4374*t)+81) : t%2=1 := by
  exact only_class 135 4 81 70 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (4+4374*x.val) 135+81)%135
          = 70%135 → x.val=1 from by decide))
    heq


theorem no_h3_a2 (t v : Nat)
    (heq : 243*v+124=2^(4+4374*t)+81) : False := by
  exact no_generic 243 4 81 124 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+4374*x.val) 243+81)%243
          ≠ 124%243 from by decide))
    heq


theorem no_h3_a3 (t v : Nat)
    (heq : 459*v+178=2^(4+4374*t)+81) : False := by
  exact no_generic 459 4 81 178 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (4+4374*x.val) 459+81)%459
          ≠ 178%459 from by decide))
    heq


theorem no_h3_a4 (t v : Nat)
    (heq : 891*v+232=2^(4+4374*t)+81) : False := by
  exact no_generic 891 4 81 232 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (4+4374*x.val) 891+81)%891
          ≠ 232%891 from by decide))
    heq


theorem no_h3_a5 (t v : Nat)
    (heq : 1755*v+286=2^(4+4374*t)+81) : False := by
  exact no_generic 1755 4 81 286 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (4+4374*x.val) 1755+81)%1755
          ≠ 286%1755 from by decide))
    heq


theorem only_h3_a6 (t v : Nat)
    (heq : 3483*v+340=2^(4+4374*t)+81) : t%7=4 := by
  exact only_class 3483 4 81 340 7 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (4+4374*x.val) 3483+81)%3483
          = 340%3483 → x.val=4 from by decide))
    heq


theorem no_h3_a7 (t v : Nat)
    (heq : 6939*v+394=2^(4+4374*t)+81) : False := by
  exact no_generic 6939 4 81 394 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (4+4374*x.val) 6939+81)%6939
          ≠ 394%6939 from by decide))
    heq


theorem no_h3_a8 (t v : Nat)
    (heq : 13851*v+448=2^(4+4374*t)+81) : False := by
  exact no_generic 13851 4 81 448 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+4374*x.val) 13851+81)%13851
          ≠ 448%13851 from by decide))
    heq


theorem no_h4_a1 (t v : Nat)
    (heq : 405*v+194=2^(5+4374*t)+243) : False := by
  exact no_generic 405 5 243 194 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (5+4374*x.val) 405+243)%405
          ≠ 194%405 from by decide))
    heq


theorem no_h4_a2 (t v : Nat)
    (heq : 729*v+356=2^(5+4374*t)+243) : False := by
  exact no_generic 729 5 243 356 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+4374*x.val) 729+243)%729
          ≠ 356%729 from by decide))
    heq


theorem no_h4_a3 (t v : Nat)
    (heq : 1377*v+518=2^(5+4374*t)+243) : False := by
  exact no_generic 1377 5 243 518 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (5+4374*x.val) 1377+243)%1377
          ≠ 518%1377 from by decide))
    heq


theorem no_h4_a4 (t v : Nat)
    (heq : 2673*v+680=2^(5+4374*t)+243) : False := by
  exact no_generic 2673 5 243 680 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (5+4374*x.val) 2673+243)%2673
          ≠ 680%2673 from by decide))
    heq


theorem no_h4_a5 (t v : Nat)
    (heq : 5265*v+842=2^(5+4374*t)+243) : False := by
  exact no_generic 5265 5 243 842 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (5+4374*x.val) 5265+243)%5265
          ≠ 842%5265 from by decide))
    heq


theorem no_h4_a6 (t v : Nat)
    (heq : 10449*v+1004=2^(5+4374*t)+243) : False := by
  exact no_generic 10449 5 243 1004 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (5+4374*x.val) 10449+243)%10449
          ≠ 1004%10449 from by decide))
    heq


theorem no_h4_a7 (t v : Nat)
    (heq : 20817*v+1166=2^(5+4374*t)+243) : False := by
  exact no_generic 20817 5 243 1166 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (5+4374*x.val) 20817+243)%20817
          ≠ 1166%20817 from by decide))
    heq


theorem no_h4_a8 (t v : Nat)
    (heq : 41553*v+1328=2^(5+4374*t)+243) : False := by
  exact no_generic 41553 5 243 1328 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+4374*x.val) 41553+243)%41553
          ≠ 1328%41553 from by decide))
    heq


theorem no_h4_a9 (t v : Nat)
    (heq : 83025*v+1490=2^(5+4374*t)+243) : False := by
  exact no_generic 83025 5 243 1490 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (5+4374*x.val) 83025+243)%83025
          ≠ 1490%83025 from by decide))
    heq


theorem no_h4_a10 (t v : Nat)
    (heq : 165969*v+1652=2^(5+4374*t)+243) : False := by
  exact no_generic 165969 5 243 1652 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (5+4374*x.val) 165969+243)%165969
          ≠ 1652%165969 from by decide))
    heq


theorem only_h5_a1 (t v : Nat)
    (heq : 1215*v+550=2^(6+4374*t)+729) : t%2=1 := by
  exact only_class 1215 6 729 550 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (6+4374*x.val) 1215+729)%1215
          = 550%1215 → x.val=1 from by decide))
    heq


theorem no_h5_a2 (t v : Nat)
    (heq : 2187*v+1036=2^(6+4374*t)+729) : False := by
  exact no_generic 2187 6 729 1036 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+4374*x.val) 2187+729)%2187
          ≠ 1036%2187 from by decide))
    heq


theorem no_h5_a3 (t v : Nat)
    (heq : 4131*v+1522=2^(6+4374*t)+729) : False := by
  exact no_generic 4131 6 729 1522 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (6+4374*x.val) 4131+729)%4131
          ≠ 1522%4131 from by decide))
    heq


theorem no_h5_a4 (t v : Nat)
    (heq : 8019*v+2008=2^(6+4374*t)+729) : False := by
  exact no_generic 8019 6 729 2008 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (6+4374*x.val) 8019+729)%8019
          ≠ 2008%8019 from by decide))
    heq


theorem no_h5_a5 (t v : Nat)
    (heq : 15795*v+2494=2^(6+4374*t)+729) : False := by
  exact no_generic 15795 6 729 2494 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (6+4374*x.val) 15795+729)%15795
          ≠ 2494%15795 from by decide))
    heq


theorem no_h5_a6 (t v : Nat)
    (heq : 31347*v+2980=2^(6+4374*t)+729) : False := by
  exact no_generic 31347 6 729 2980 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (6+4374*x.val) 31347+729)%31347
          ≠ 2980%31347 from by decide))
    heq


theorem no_h5_a7 (t v : Nat)
    (heq : 62451*v+3466=2^(6+4374*t)+729) : False := by
  exact no_generic 62451 6 729 3466 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (6+4374*x.val) 62451+729)%62451
          ≠ 3466%62451 from by decide))
    heq


theorem no_h5_a8 (t v : Nat)
    (heq : 124659*v+3952=2^(6+4374*t)+729) : False := by
  exact no_generic 124659 6 729 3952 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+4374*x.val) 124659+729)%124659
          ≠ 3952%124659 from by decide))
    heq


theorem no_h5_a9 (t v : Nat)
    (heq : 249075*v+4438=2^(6+4374*t)+729) : False := by
  exact no_generic 249075 6 729 4438 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (6+4374*x.val) 249075+729)%249075
          ≠ 4438%249075 from by decide))
    heq


theorem no_h5_a10 (t v : Nat)
    (heq : 497907*v+4924=2^(6+4374*t)+729) : False := by
  exact no_generic 497907 6 729 4924 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (6+4374*x.val) 497907+729)%497907
          ≠ 4924%497907 from by decide))
    heq


theorem no_h5_a11 (t v : Nat)
    (heq : 995571*v+5410=2^(6+4374*t)+729) : False := by
  exact no_generic 995571 6 729 5410 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (6+4374*x.val) 995571+729)%995571
          ≠ 5410%995571 from by decide))
    heq


theorem no_h5_a12 (t v : Nat)
    (heq : 1990899*v+5896=2^(6+4374*t)+729) : False := by
  exact no_generic 1990899 6 729 5896 13 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 13,
        (Nat.powMod 2 (6+4374*x.val) 1990899+729)%1990899
          ≠ 5896%1990899 from by decide))
    heq


theorem no_h6_a1 (t v : Nat)
    (heq : 3645*v+1586=2^(7+4374*t)+2187) : False := by
  exact no_generic 3645 7 2187 1586 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (7+4374*x.val) 3645+2187)%3645
          ≠ 1586%3645 from by decide))
    heq


theorem no_h6_a2 (t v : Nat)
    (heq : 6561*v+3044=2^(7+4374*t)+2187) : False := by
  exact no_generic 6561 7 2187 3044 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (7+4374*x.val) 6561+2187)%6561
          ≠ 3044%6561 from by decide))
    heq


theorem no_h6_a3 (t v : Nat)
    (heq : 12393*v+4502=2^(7+4374*t)+2187) : False := by
  exact no_generic 12393 7 2187 4502 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (7+4374*x.val) 12393+2187)%12393
          ≠ 4502%12393 from by decide))
    heq


theorem no_h6_a4 (t v : Nat)
    (heq : 24057*v+5960=2^(7+4374*t)+2187) : False := by
  exact no_generic 24057 7 2187 5960 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (7+4374*x.val) 24057+2187)%24057
          ≠ 5960%24057 from by decide))
    heq


theorem no_h6_a5 (t v : Nat)
    (heq : 47385*v+7418=2^(7+4374*t)+2187) : False := by
  exact no_generic 47385 7 2187 7418 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (7+4374*x.val) 47385+2187)%47385
          ≠ 7418%47385 from by decide))
    heq


theorem no_h6_a6 (t v : Nat)
    (heq : 94041*v+8876=2^(7+4374*t)+2187) : False := by
  exact no_generic 94041 7 2187 8876 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (7+4374*x.val) 94041+2187)%94041
          ≠ 8876%94041 from by decide))
    heq


theorem no_h6_a7 (t v : Nat)
    (heq : 187353*v+10334=2^(7+4374*t)+2187) : False := by
  exact no_generic 187353 7 2187 10334 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (7+4374*x.val) 187353+2187)%187353
          ≠ 10334%187353 from by decide))
    heq


theorem no_h6_a8 (t v : Nat)
    (heq : 373977*v+11792=2^(7+4374*t)+2187) : False := by
  exact no_generic 373977 7 2187 11792 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (7+4374*x.val) 373977+2187)%373977
          ≠ 11792%373977 from by decide))
    heq


theorem no_h6_a9 (t v : Nat)
    (heq : 747225*v+13250=2^(7+4374*t)+2187) : False := by
  exact no_generic 747225 7 2187 13250 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (7+4374*x.val) 747225+2187)%747225
          ≠ 13250%747225 from by decide))
    heq


theorem no_h6_a10 (t v : Nat)
    (heq : 1493721*v+14708=2^(7+4374*t)+2187) : False := by
  exact no_generic 1493721 7 2187 14708 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (7+4374*x.val) 1493721+2187)%1493721
          ≠ 14708%1493721 from by decide))
    heq


theorem no_h6_a11 (t v : Nat)
    (heq : 2986713*v+16166=2^(7+4374*t)+2187) : False := by
  exact no_generic 2986713 7 2187 16166 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (7+4374*x.val) 2986713+2187)%2986713
          ≠ 16166%2986713 from by decide))
    heq


theorem no_h6_a12 (t v : Nat)
    (heq : 5972697*v+17624=2^(7+4374*t)+2187) : False := by
  exact no_generic 5972697 7 2187 17624 13 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 13,
        (Nat.powMod 2 (7+4374*x.val) 5972697+2187)%5972697
          ≠ 17624%5972697 from by decide))
    heq


theorem no_h6_a13 (t v : Nat)
    (heq : 11944665*v+19082=2^(7+4374*t)+2187) : False := by
  exact no_generic 11944665 7 2187 19082 14 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 14,
        (Nat.powMod 2 (7+4374*x.val) 11944665+2187)%11944665
          ≠ 19082%11944665 from by decide))
    heq


theorem no_h6_a14 (t v : Nat)
    (heq : 23888601*v+20540=2^(7+4374*t)+2187) : False := by
  exact no_generic 23888601 7 2187 20540 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (7+4374*x.val) 23888601+2187)%23888601
          ≠ 20540%23888601 from by decide))
    heq


theorem only_h7_a1 (t v : Nat)
    (heq : 10935*v+4630=2^(8+4374*t)+6561) : t%2=1 := by
  exact only_class 10935 8 6561 4630 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (8+4374*x.val) 10935+6561)%10935
          = 4630%10935 → x.val=1 from by decide))
    heq


theorem no_h7_a2 (t v : Nat)
    (heq : 19683*v+9004=2^(8+4374*t)+6561) : False := by
  exact no_generic 19683 8 6561 9004 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (8+4374*x.val) 19683+6561)%19683
          ≠ 9004%19683 from by decide))
    heq


theorem no_h7_a3 (t v : Nat)
    (heq : 37179*v+13378=2^(8+4374*t)+6561) : False := by
  exact no_generic 37179 8 6561 13378 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (8+4374*x.val) 37179+6561)%37179
          ≠ 13378%37179 from by decide))
    heq


theorem no_h7_a4 (t v : Nat)
    (heq : 72171*v+17752=2^(8+4374*t)+6561) : False := by
  exact no_generic 72171 8 6561 17752 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (8+4374*x.val) 72171+6561)%72171
          ≠ 17752%72171 from by decide))
    heq


theorem no_h7_a5 (t v : Nat)
    (heq : 142155*v+22126=2^(8+4374*t)+6561) : False := by
  exact no_generic 142155 8 6561 22126 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (8+4374*x.val) 142155+6561)%142155
          ≠ 22126%142155 from by decide))
    heq


theorem no_h7_a6 (t v : Nat)
    (heq : 282123*v+26500=2^(8+4374*t)+6561) : False := by
  exact no_generic 282123 8 6561 26500 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (8+4374*x.val) 282123+6561)%282123
          ≠ 26500%282123 from by decide))
    heq


theorem no_h7_a7 (t v : Nat)
    (heq : 562059*v+30874=2^(8+4374*t)+6561) : False := by
  exact no_generic 562059 8 6561 30874 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (8+4374*x.val) 562059+6561)%562059
          ≠ 30874%562059 from by decide))
    heq


theorem no_h7_a8 (t v : Nat)
    (heq : 1121931*v+35248=2^(8+4374*t)+6561) : False := by
  exact no_generic 1121931 8 6561 35248 9 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (8+4374*x.val) 1121931+6561)%1121931
          ≠ 35248%1121931 from by decide))
    heq


theorem no_h7_a9 (t v : Nat)
    (heq : 2241675*v+39622=2^(8+4374*t)+6561) : False := by
  exact no_generic 2241675 8 6561 39622 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (8+4374*x.val) 2241675+6561)%2241675
          ≠ 39622%2241675 from by decide))
    heq


theorem no_h7_a10 (t v : Nat)
    (heq : 4481163*v+43996=2^(8+4374*t)+6561) : False := by
  exact no_generic 4481163 8 6561 43996 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (8+4374*x.val) 4481163+6561)%4481163
          ≠ 43996%4481163 from by decide))
    heq


theorem no_h7_a11 (t v : Nat)
    (heq : 8960139*v+48370=2^(8+4374*t)+6561) : False := by
  exact no_generic 8960139 8 6561 48370 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (8+4374*x.val) 8960139+6561)%8960139
          ≠ 48370%8960139 from by decide))
    heq


theorem no_h7_a12 (t v : Nat)
    (heq : 17918091*v+52744=2^(8+4374*t)+6561) : False := by
  exact no_generic 17918091 8 6561 52744 13 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 13,
        (Nat.powMod 2 (8+4374*x.val) 17918091+6561)%17918091
          ≠ 52744%17918091 from by decide))
    heq


theorem no_h7_a13 (t v : Nat)
    (heq : 35833995*v+57118=2^(8+4374*t)+6561) : False := by
  exact no_generic 35833995 8 6561 57118 14 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 14,
        (Nat.powMod 2 (8+4374*x.val) 35833995+6561)%35833995
          ≠ 57118%35833995 from by decide))
    heq


theorem no_h7_a14 (t v : Nat)
    (heq : 71665803*v+61492=2^(8+4374*t)+6561) : False := by
  exact no_generic 71665803 8 6561 61492 15 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 15,
        (Nat.powMod 2 (8+4374*x.val) 71665803+6561)%71665803
          ≠ 61492%71665803 from by decide))
    heq


theorem no_h7_a15 (t v : Nat)
    (heq : 143329419*v+65866=2^(8+4374*t)+6561) : False := by
  exact no_generic 143329419 8 6561 65866 16 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 16,
        (Nat.powMod 2 (8+4374*x.val) 143329419+6561)%143329419
          ≠ 65866%143329419 from by decide))
    heq


theorem no_h7_a16 (t v : Nat)
    (heq : 286656651*v+70240=2^(8+4374*t)+6561) : False := by
  exact no_generic 286656651 8 6561 70240 17 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 17,
        (Nat.powMod 2 (8+4374*x.val) 286656651+6561)%286656651
          ≠ 70240%286656651 from by decide))
    heq


theorem no_h8_a1 (t v : Nat)
    (heq : 32805*v+13634=2^(9+4374*t)+19683) : False := by
  exact no_generic 32805 9 19683 13634 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (9+4374*x.val) 32805+19683)%32805
          ≠ 13634%32805 from by decide))
    heq


theorem only_h8_a2 (t v : Nat)
    (heq : 59049*v+26756=2^(9+4374*t)+19683) : t%9=5 := by
  exact only_class 59049 9 19683 26756 9 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (9+4374*x.val) 59049+19683)%59049
          = 26756%59049 → x.val=5 from by decide))
    heq


theorem no_h8_a3 (t v : Nat)
    (heq : 111537*v+39878=2^(9+4374*t)+19683) : False := by
  exact no_generic 111537 9 19683 39878 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (9+4374*x.val) 111537+19683)%111537
          ≠ 39878%111537 from by decide))
    heq


theorem no_h8_a4 (t v : Nat)
    (heq : 216513*v+53000=2^(9+4374*t)+19683) : False := by
  exact no_generic 216513 9 19683 53000 15 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 15,
        (Nat.powMod 2 (9+4374*x.val) 216513+19683)%216513
          ≠ 53000%216513 from by decide))
    heq


theorem no_h8_a5 (t v : Nat)
    (heq : 426465*v+66122=2^(9+4374*t)+19683) : False := by
  exact no_generic 426465 9 19683 66122 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (9+4374*x.val) 426465+19683)%426465
          ≠ 66122%426465 from by decide))
    heq


theorem no_h8_a6 (t v : Nat)
    (heq : 846369*v+79244=2^(9+4374*t)+19683) : False := by
  exact no_generic 846369 9 19683 79244 21 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 21,
        (Nat.powMod 2 (9+4374*x.val) 846369+19683)%846369
          ≠ 79244%846369 from by decide))
    heq


theorem no_h8_a7 (t v : Nat)
    (heq : 1686177*v+92366=2^(9+4374*t)+19683) : False := by
  exact no_generic 1686177 9 19683 92366 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (9+4374*x.val) 1686177+19683)%1686177
          ≠ 92366%1686177 from by decide))
    heq


theorem no_h8_a8 (t v : Nat)
    (heq : 3365793*v+105488=2^(9+4374*t)+19683) : False := by
  exact no_generic 3365793 9 19683 105488 27 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 27,
        (Nat.powMod 2 (9+4374*x.val) 3365793+19683)%3365793
          ≠ 105488%3365793 from by decide))
    heq


theorem no_h8_a9 (t v : Nat)
    (heq : 6725025*v+118610=2^(9+4374*t)+19683) : False := by
  exact no_generic 6725025 9 19683 118610 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (9+4374*x.val) 6725025+19683)%6725025
          ≠ 118610%6725025 from by decide))
    heq


theorem no_h8_a10 (t v : Nat)
    (heq : 13443489*v+131732=2^(9+4374*t)+19683) : False := by
  exact no_generic 13443489 9 19683 131732 33 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 33,
        (Nat.powMod 2 (9+4374*x.val) 13443489+19683)%13443489
          ≠ 131732%13443489 from by decide))
    heq


theorem no_h8_a11 (t v : Nat)
    (heq : 26880417*v+144854=2^(9+4374*t)+19683) : False := by
  exact no_generic 26880417 9 19683 144854 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (9+4374*x.val) 26880417+19683)%26880417
          ≠ 144854%26880417 from by decide))
    heq


theorem no_h8_a12 (t v : Nat)
    (heq : 53754273*v+157976=2^(9+4374*t)+19683) : False := by
  exact no_generic 53754273 9 19683 157976 39 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 39,
        (Nat.powMod 2 (9+4374*x.val) 53754273+19683)%53754273
          ≠ 157976%53754273 from by decide))
    heq


theorem no_h8_a13 (t v : Nat)
    (heq : 107501985*v+171098=2^(9+4374*t)+19683) : False := by
  exact no_generic 107501985 9 19683 171098 14 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 14,
        (Nat.powMod 2 (9+4374*x.val) 107501985+19683)%107501985
          ≠ 171098%107501985 from by decide))
    heq


theorem no_h8_a14 (t v : Nat)
    (heq : 214997409*v+184220=2^(9+4374*t)+19683) : False := by
  exact no_generic 214997409 9 19683 184220 45 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 45,
        (Nat.powMod 2 (9+4374*x.val) 214997409+19683)%214997409
          ≠ 184220%214997409 from by decide))
    heq


theorem no_h8_a15 (t v : Nat)
    (heq : 429988257*v+197342=2^(9+4374*t)+19683) : False := by
  exact no_generic 429988257 9 19683 197342 16 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 16,
        (Nat.powMod 2 (9+4374*x.val) 429988257+19683)%429988257
          ≠ 197342%429988257 from by decide))
    heq


theorem no_h8_a16 (t v : Nat)
    (heq : 859969953*v+210464=2^(9+4374*t)+19683) : False := by
  exact no_generic 859969953 9 19683 210464 51 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 51,
        (Nat.powMod 2 (9+4374*x.val) 859969953+19683)%859969953
          ≠ 210464%859969953 from by decide))
    heq


theorem no_h8_a17 (t v : Nat)
    (heq : 1719933345*v+223586=2^(9+4374*t)+19683) : False := by
  exact no_generic 1719933345 9 19683 223586 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (9+4374*x.val) 1719933345+19683)%1719933345
          ≠ 223586%1719933345 from by decide))
    heq


theorem no_h8_a18 (t v : Nat)
    (heq : 3439860129*v+236708=2^(9+4374*t)+19683) : False := by
  exact no_generic 3439860129 9 19683 236708 57 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 57,
        (Nat.powMod 2 (9+4374*x.val) 3439860129+19683)%3439860129
          ≠ 236708%3439860129 from by decide))
    heq


set_option linter.unusedSimpArgs false

/-- The complete generic-source residue census for j=4374*t. -/
private theorem generic_gate_case_0 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 0) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  have ha1 : a=1 := hzero rfl
  subst a
  exfalso
  apply no_h0_a1 t v
  have hexp : 4374*t+0+1 = 1+4374*t := by omega
  rw [hexp] at heq
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
  omega

private theorem generic_gate_case_1 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 1) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 from by omega) with a1|a2|a3|a4

  · subst a
    have hgate : t%2=1 := by
      apply only_h1_a1 t v
      have hexp : 4374*t+1+1 = 2+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h1_a2 t v
    have hexp : 4374*t+1+1 = 2+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    have hgate : t%4=2 := by
      apply only_h1_a3 t v
      have hexp : 4374*t+1+1 = 2+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h1_a4 t v
    have hexp : 4374*t+1+1 = 2+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_2 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 2) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 from by omega) with a1|a2|a3|a4|a5|a6

  · subst a
    exfalso
    apply no_h2_a1 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h2_a2 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h2_a3 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h2_a4 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h2_a5 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h2_a6 t v
    have hexp : 4374*t+2+1 = 3+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_3 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 3) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8

  · subst a
    have hgate : t%2=1 := by
      apply only_h3_a1 t v
      have hexp : 4374*t+3+1 = 4+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h3_a2 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h3_a3 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h3_a4 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h3_a5 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    have hgate : t%7=4 := by
      apply only_h3_a6 t v
      have hexp : 4374*t+3+1 = 4+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h3_a7 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h3_a8 t v
    have hexp : 4374*t+3+1 = 4+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_4 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 4) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10

  · subst a
    exfalso
    apply no_h4_a1 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a2 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a3 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a4 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a5 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a6 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a7 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a8 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a9 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h4_a10 t v
    have hexp : 4374*t+4+1 = 5+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_5 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 5) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12

  · subst a
    have hgate : t%2=1 := by
      apply only_h5_a1 t v
      have hexp : 4374*t+5+1 = 6+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h5_a2 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a3 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a4 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a5 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a6 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a7 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a8 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a9 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a10 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a11 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h5_a12 t v
    have hexp : 4374*t+5+1 = 6+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_6 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 6) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12|a13|a14

  · subst a
    exfalso
    apply no_h6_a1 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a2 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a3 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a4 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a5 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a6 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a7 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a8 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a9 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a10 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a11 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a12 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a13 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h6_a14 t v
    have hexp : 4374*t+6+1 = 7+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_7 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 7) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 ∨ a=15 ∨ a=16 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12|a13|a14|a15|a16

  · subst a
    have hgate : t%2=1 := by
      apply only_h7_a1 t v
      have hexp : 4374*t+7+1 = 8+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h7_a2 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a3 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a4 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a5 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a6 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a7 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a8 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a9 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a10 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a11 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a12 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a13 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a14 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a15 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h7_a16 t v
    have hexp : 4374*t+7+1 = 8+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

private theorem generic_gate_case_8 (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h)
    (hcase : h = 8) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  subst h
  rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 ∨ a=15 ∨ a=16 ∨ a=17 ∨ a=18 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12|a13|a14|a15|a16|a17|a18

  · subst a
    exfalso
    apply no_h8_a1 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    have hgate : t%9=5 := by
      apply only_h8_a2 t v
      have hexp : 4374*t+8+1 = 9+4374*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    omega

  · subst a
    exfalso
    apply no_h8_a3 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a4 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a5 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a6 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a7 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a8 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a9 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a10 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a11 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a12 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a13 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a14 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a15 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a16 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a17 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

  · subst a
    exfalso
    apply no_h8_a18 t v
    have hexp : 4374*t+8+1 = 9+4374*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega

theorem all_generic_gates (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h) :
    (h=1 ∧ a=1 ∧ t%2=1) ∨
    (h=1 ∧ a=3 ∧ t%4=2) ∨
    (h=3 ∧ a=6 ∧ t%7=4) ∨
    (h=8 ∧ a=2 ∧ t%9=5) ∨
    (h=3 ∧ a=1 ∧ t%2=1) ∨
    (h=5 ∧ a=1 ∧ t%2=1) ∨
    (h=7 ∧ a=1 ∧ t%2=1) := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8
    from by omega) with h0|h1|h2|h3|h4|h5|h6|h7|h8
  · exact generic_gate_case_0 h a t v hh ha hzero hpos heq h0
  · exact generic_gate_case_1 h a t v hh ha hzero hpos heq h1
  · exact generic_gate_case_2 h a t v hh ha hzero hpos heq h2
  · exact generic_gate_case_3 h a t v hh ha hzero hpos heq h3
  · exact generic_gate_case_4 h a t v hh ha hzero hpos heq h4
  · exact generic_gate_case_5 h a t v hh ha hzero hpos heq h5
  · exact generic_gate_case_6 h a t v hh ha hzero hpos heq h6
  · exact generic_gate_case_7 h a t v hh ha hzero hpos heq h7
  · exact generic_gate_case_8 h a t v hh ha hzero hpos heq h8
#print axioms all_generic_gates

/-- No generic incoming edge exists in the root-free residue classes. -/
theorem no_generic_forbidden (h a t v : Nat)
    (hh : h ≤ 8) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (ht4 : t%4=0) (ht7 : t%7≠4) (ht9 : t%9≠5)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h) : False := by
  rcases all_generic_gates h a t v hh ha hzero hpos heq with
    h1 | h2 | h3 | h4 | h5 | h6 | h7
  all_goals omega

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
    have hp : 2^a=2*2^(a-1) := by
      calc
        2^a=2^((a-1)+1) := by rw [hrepl]
        _=2*2^(a-1) := by rw [Nat.pow_succ]; omega
    have hk : D*(2*a-3)+S =
        (D*(2*(a-1)-3)+S)+2*D := by
      have hsub : 2*a-3=(2*(a-1)-3)+2 := by omega
      rw [hsub,Nat.mul_add]
      omega
    rw [hk,hp]
    constructor
    · omega
    constructor
    · omega
    · omega

/-- Signed-power interval for every hidden length h<=8. -/
theorem high_cutoff (h a : Nat) (hh : h≤8)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a) :
    1 < 3^h*(2*a-3)+2^(h+1) ∧
    3^h*(2*a-3)+2^(h+1) < 2^a := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8
    from by omega) with h0|h1|h2|h3|h4|h5|h6|h7|h8

  · subst h
    have hA : 2≤a := by simpa using ha
    have hg := stable_gap 1 2 2
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 5≤a := by simpa using ha
    have hg := stable_gap 3 4 5
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 7≤a := by simpa using ha
    have hg := stable_gap 9 8 7
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 9≤a := by simpa using ha
    have hg := stable_gap 27 16 9
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 11≤a := by simpa using ha
    have hg := stable_gap 81 32 11
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 13≤a := by simpa using ha
    have hg := stable_gap 243 64 13
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 15≤a := by simpa using ha
    have hg := stable_gap 729 128 15
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 17≤a := by simpa using ha
    have hg := stable_gap 2187 256 17
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩

  · subst h
    have hA : 19≤a := by simpa using ha
    have hg := stable_gap 6561 512 19
      (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1,hg.2.1⟩


private theorem odd_three_pow (h : Nat) : ((3:Int)^h)%2=1 := by
  induction h with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ, Int.mul_emod, ih]
    decide

/-- All generic source valuations above the signed-power cutoffs are impossible. -/
theorem no_high_source (h a t v : Nat) (hh : h≤8)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h) : False := by
  have hgap := high_cutoff h a hh ha
  have ha2 : 2≤a := by split at ha <;> omega
  let K : Int := (3:Int)^h*(2*(a:Int)-3)+(2:Int)^(h+1)
  have hK_eq : K = ((↑(3^h*(2*a-3)+2^(h+1):Nat):Int)) := by
    dsimp [K]
    have hsub : (↑(2*a-3):Int) = 2*(a:Int)-3 := by omega
    rw [←hsub]
  have hKlow : 1<K := by
    rw [hK_eq]
    exact_mod_cast hgap.1
  have hKhigh : K < (2:Int)^a := by
    rw [hK_eq]
    exact_mod_cast hgap.2
  have hKodd : K%2=1 := by
    dsimp [K]
    have hodd := odd_three_pow h
    have heven : ((2:Int)^(h+1))%2=0 := by
      rw [Int.pow_succ,Int.mul_emod]
      simp
    have hlinodd : (2*(a:Int)-3)%2=1 := by omega
    rw [Int.add_emod,Int.mul_emod,hodd,hlinodd,heven]
    decide
  have heq_int :
      (3:Int)^h*((2:Int)^(a+1)+1)*(v:Int) +
        2*(a:Int)*(3:Int)^h + (2:Int)^(h+1) =
        (2:Int)^(4374*t+h+1)+3*(3:Int)^h := by
    exact_mod_cast heq
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^(4374*t+h+1)-K := by
    refine ⟨(3:Int)^h*(v:Int), ?_⟩
    dsimp [K]
    let D : Int := (3:Int)^h
    let B : Int := ((2:Int)^(a+1)+1)
    let N : Int := (2:Int)^(4374*t+h+1)
    let S : Int := (2:Int)^(h+1)
    have hmul : D*(2*(a:Int)-3)=2*(a:Int)*D-3*D := by
      dsimp [D]
      rw [Int.mul_sub]
      have h1 : (3:Int)^h*(2*(a:Int))=2*(a:Int)*(3:Int)^h := by ac_rfl
      rw [h1]
      have h2 : (3:Int)^h*3=3*(3:Int)^h := by ac_rfl
      rw [h2]
    have hmul2 : D*B*(v:Int)=B*(D*(v:Int)) := by ac_rfl
    have heq2 : D*B*(v:Int)+2*(a:Int)*D+S=N+3*D := by
      simpa only [D,B,N,S] using heq_int
    calc
      N-(D*(2*(a:Int)-3)+S) = D*B*(v:Int) := by
        rw [hmul]
        omega
      _ = B*(D*(v:Int)) := hmul2
  exact (SheepOddGap.no_power_signed_small_odd a K
    hKlow hKodd hKhigh (4374*t+h+1)).1 hdiv

/-- Complete generic-source exclusion for all a, not merely bounded a. -/
theorem no_generic_all_a (h a t v : Nat)
    (hh : h≤8) (ha : 1≤a)
    (ht4 : t%4=0) (ht7 : t%7≠4) (ht9 : t%9≠5)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(4374*t+h+1)+3*3^h) : False := by
  by_cases high : (if h=0 then 2 else 2*h+3)≤a
  · exact no_high_source h a t v hh high heq
  · have hzero : h=0 → a=1 := by
      intro hz
      subst h
      simp at high
      omega
    have hpos : 0<h → a≤2*h+2 := by
      intro hhpos
      have hnz : h≠0 := by omega
      simp only [hnz, ↓reduceIte] at high
      omega
    exact no_generic_forbidden h a t v hh ha hzero hpos ht4 ht7 ht9 heq

private theorem target_mod19683_not_one (t : Nat) (ht : t%3≠0) :
    2^(4374*t)%19683 ≠ 1 := by
  have hp : 2^(4374*3)%19683=1 := by
    rw [←Nat.powMod_def]
    decide
  have hdiv : t=t%3+3*(t/3) := by
    have h := Nat.mod_add_div t 3
    omega
  have heq : 4374*t=4374*(t%3)+(4374*3)*(t/3) := by omega
  have hper := pow_mod_period 19683 (4374*3)
    (4374*(t%3)) (t/3) (by decide) hp
  rw [heq,hper]
  rcases (show t%3=1 ∨ t%3=2 from by omega) with h1|h2
  · rw [h1]
    rw [←Nat.powMod_def]
    decide
  · rw [h2]
    rw [←Nat.powMod_def]
    decide

/-- A genuine inverse edge into 2^(4374*t) has hidden length at most eight. -/
theorem target_hidden_le8 (t h u : Nat) (ht : t%3≠0)
    (hy : 2^(4374*t)=1+3^h*u) : h≤8 := by
  by_cases hsmall : h≤8
  · exact hsmall
  have hh : 9≤h := by omega
  have hd : 19683 ∣ 3^h := by
    have hrepl : h=9+(h-9) := by omega
    rw [hrepl,Nat.pow_add]
    refine ⟨3^(h-9), ?_⟩
    simp [show (3:Nat)^9=19683 by decide]
  have hmul : (3^h*u)%19683=0 := by
    have h0 : 3^h%19683=0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mul_mod,h0]
    simp
  have hy_mod : 2^(4374*t)%19683=1 := by
    rw [hy,Nat.add_mod,hmul]
  exact False.elim (target_mod19683_not_one t ht hy_mod)

private theorem exp_dominates8 (n : Nat) (hn : 480≤n) :
    6561*(n+9)+256 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : n=480
    · subst n
      decide
    have hprev : 480≤n-1 := by omega
    have hlt : n-1<n := by omega
    have ip := ih (n-1) hlt hprev
    have hs : n=n-1+1 := by omega
    have hp : 2^n=2*2^(n-1) := by
      calc
        2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) hs
        _=2*2^(n-1) := by rw [Nat.pow_succ]; omega
    rw [hp]
    omega

/-- Uniform exclusion of the exceptional odd-part-three source, for h<=8. -/
private theorem no_special_band
    (j h a e D S : Nat)
    (hj : 4374≤j) (hD : D≤6561) (hS : S≤256)
    (hebound : e≤h+6)
    (he_low : 2^e<3*D) (he_high : 3*D<2^(e+1))
    (heq : 3*D*2^a+D*(a+2)+S=2^(j+h)) : False := by
  let z := j+h-e
  have hzEq : j+h=e+z := by dsimp [z]; omega
  have hzBound : 481≤z := by dsimp [z]; omega
  by_cases hz : z≤a
  · have hpow : 2^z≤2^a := Nat.pow_le_pow_right (by decide) hz
    have hmpos : 0<2^z := Nat.pow_pos (by decide)
    have hp : 2^(j+h)=2^e*2^z := by
      calc
        2^(j+h)=2^(e+z) := congrArg (fun m : Nat => 2^m) hzEq
        _=2^e*2^z := Nat.pow_add ..
    have hmul1 : 2^e*2^z<3*D*2^z :=
      Nat.mul_lt_mul_of_pos_right he_low hmpos
    have hmul2 : 3*D*2^z≤3*D*2^a :=
      Nat.mul_le_mul_left (3*D) hpow
    omega
  · have haw : a≤z-1 := by omega
    let w := z-1
    have hw : 480≤w := by dsimp [w]; omega
    have hEq : j+h=(e+1)+w := by dsimp [w]; omega
    have hp : 2^(j+h)=2^(e+1)*2^w := by
      calc
        2^(j+h)=2^((e+1)+w) := congrArg (fun m : Nat => 2^m) hEq
        _=2^(e+1)*2^w := Nat.pow_add ..
    have hpow : 2^a≤2^w := Nat.pow_le_pow_right (by decide) haw
    have hmul : 3*D*2^a≤3*D*2^w :=
      Nat.mul_le_mul_left (3*D) hpow
    have hsmall1 : D*(a+2)≤D*(w+9) :=
      Nat.mul_le_mul_left D (by omega)
    have hsmall2 : D*(w+9)≤6561*(w+9) :=
      Nat.mul_le_mul_right (w+9) hD
    have hsmall3 := exp_dominates8 w hw
    have hq : D*(a+2)+S<2^w := by omega
    have hcoef : 3*D+1≤2^(e+1) := by omega
    have htotal : (3*D+1)*2^w≤2^(e+1)*2^w :=
      Nat.mul_le_mul_right (2^w) hcoef
    have hsum : 3*D*2^w+2^w=(3*D+1)*2^w := by
      rw [Nat.add_mul]
      omega
    omega

/-- No exceptional source with odd part three can enter any eighth-stratum target. -/
theorem no_special_all_a (h a t : Nat)
    (hh : h≤8) (ht : 1≤t)
    (heq : 3^h*(3*2^a+a+2)+2^h=2^(4374*t+h)) : False := by
  have hj : 4374≤4374*t := by omega
  have htri : 3^h*(3*2^a+a+2)=3*(3^h)*2^a+3^h*(a+2) := by
    have hsum : 3*2^a+a+2=(3*2^a)+(a+2) := by omega
    rw [hsum,Nat.mul_add]
    have hac : 3^h*(3*2^a)=3*(3^h)*2^a := by ac_rfl
    rw [hac]
  have hsrc : 3*(3^h)*2^a+3^h*(a+2)+2^h=2^(4374*t+h) := by omega
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8
    from by omega) with h0|h1|h2|h3|h4|h5|h6|h7|h8

  · subst h
    exact no_special_band (4374*t) 0 a 1 1 1
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 1 a 3 3 2
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 2 a 4 9 4
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 3 a 6 27 8
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 4 a 7 81 16
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 5 a 9 243 32
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 6 a 11 729 64
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 7 a 12 2187 128
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)

  · subst h
    exact no_special_band (4374*t) 8 a 14 6561 256
      hj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] using hsrc)


#print axioms no_special_all_a

/-- Every possible last edge into an eighth-stratum target is excluded. -/
theorem no_inverse_source_cases (t h a u v : Nat)
    (ht : 1≤t) (ht3 : t%3≠0) (ha : 1≤a)
    (ht4 : t%4=0) (ht7 : t%7≠4) (ht9 : t%9≠5)
    (hy : 2^(4374*t)=1+3^h*u)
    (heq :
      (3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
        =2^(4374*t+h+1)+3*3^h) ∨
      (3^h*(3*2^a+a+2)+2^h=2^(4374*t+h))) : False := by
  have hh : h≤8 := target_hidden_le8 t h u ht3 hy
  rcases heq with hgen|hspe
  · exact no_generic_all_a h a t v hh ha ht4 ht7 ht9 hgen
  · exact no_special_all_a h a t hh ht hspe

#print axioms no_inverse_source_cases

/-- Authentic blank-even root exclusion in the eighth 3-adic stratum. -/
theorem blank_even_cannot_hit_eighth (t : Nat)
    (ht : 1≤t) (ht3 : t%3≠0)
    (ht4 : t%4=0) (ht7 : t%7≠4) (ht9 : t%9≠5) :
    ¬ SheepEven.EvenReach 10 (2^(4374*t)) := by
  intro hreach
  have hneq : 2^(4374*t)≠10 := by
    have hn : 4≤4374*t := by omega
    have hpow : 2^4≤2^(4374*t) :=
      Nat.pow_le_pow_right (by decide) hn
    omega
  have hy : 1*(2^(4374*t))+0=2^(4374*t) := by omega
  rcases SheepEvenReachInverse.blank_even_inverse_cases hreach hneq hy with
    ⟨x,a,h,v,u,hprefix,ha,hv,hvodd,huodd,hxdef,hydef,heq⟩ |
    ⟨x,a,h,u,hprefix,ha,huodd,hxdef,hydef,heq⟩
  · have hgen :
      3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
        =2^(4374*t+h+1)+3*3^h := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u v ht ht3 ha ht4 ht7 ht9 hydef
      (Or.inl hgen)
  · have hspe :
      3^h*(3*2^a+a+2)+2^h=2^(4374*t+h) := by
      simpa only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.mul_one] using heq
    exact no_inverse_source_cases t h a u 0 ht ht3 ha ht4 ht7 ht9 hydef
      (Or.inr hspe)

#print axioms blank_even_cannot_hit_eighth

/-- Exact family of exponent indices excluded by the new last-edge theorem. -/
def EighthStratumExcluded (j : Nat) : Prop :=
  ∃ t : Nat, j=4374*t ∧ 1≤t ∧ t%3≠0 ∧
    t%4=0 ∧ t%7≠4 ∧ t%9≠5

theorem eighth_stratum_unreachable (j : Nat)
    (h : EighthStratumExcluded j) :
    ¬ SheepEven.EvenReach 10 (2^j) := by
  rcases h with ⟨t,rfl,ht,ht3,ht4,ht7,ht9⟩
  exact blank_even_cannot_hit_eighth t ht ht3 ht4 ht7 ht9

/-- The original machine's halt criterion can omit this entire eighth-stratum
    family of powers, because none has a legal final edge from the blank root. -/
theorem raw_halts_iff_nonexcluded_power :
    BusyBeaver.IsHalt BB6.Agent22.SheepSource.Source.target ↔
      ∃ j : Nat, 2≤j ∧
        ¬ EighthStratumExcluded j ∧ SheepEven.EvenReach 10 (2^j) := by
  rw [BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power]
  constructor
  · rintro ⟨j,hj,hr⟩
    refine ⟨j,hj,?_,hr⟩
    intro hs
    exact eighth_stratum_unreachable j hs hr
  · rintro ⟨j,hj,_,hr⟩
    exact ⟨j,hj,hr⟩

#print axioms raw_halts_iff_nonexcluded_power
end BB6.Agent40.SheepPower4374
