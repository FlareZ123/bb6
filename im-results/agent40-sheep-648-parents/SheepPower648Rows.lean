import SheepPower648Core
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower648

theorem no_h0_a1 (t v : Nat)
    (heq : 5*v+4=2^(1+648*t)+3) : False := by
  exact no_generic 5 1 3 4 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (1+648*x.val) 5+3)%5 ≠ 4%5 from by decide))
    heq

theorem no_h1_a1 (t v : Nat)
    (heq : 15*v+10=2^(2+648*t)+9) : False := by
  exact no_generic 15 2 9 10 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (2+648*x.val) 15+9)%15 ≠ 10%15 from by decide))
    heq

theorem no_h1_a2 (t v : Nat)
    (heq : 27*v+16=2^(2+648*t)+9) : False := by
  exact no_generic 27 2 9 16 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (2+648*x.val) 27+9)%27 ≠ 16%27 from by decide))
    heq

theorem no_h1_a3 (t v : Nat)
    (heq : 51*v+22=2^(2+648*t)+9) : False := by
  exact no_generic 51 2 9 22 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (2+648*x.val) 51+9)%51 ≠ 22%51 from by decide))
    heq

theorem no_h1_a4 (t v : Nat)
    (heq : 99*v+28=2^(2+648*t)+9) : False := by
  exact no_generic 99 2 9 28 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (2+648*x.val) 99+9)%99 ≠ 28%99 from by decide))
    heq

theorem no_h2_a1 (t v : Nat)
    (heq : 45*v+26=2^(3+648*t)+27) : False := by
  exact no_generic 45 3 27 26 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+648*x.val) 45+27)%45 ≠ 26%45 from by decide))
    heq

theorem no_h2_a2 (t v : Nat)
    (heq : 81*v+44=2^(3+648*t)+27) : False := by
  exact no_generic 81 3 27 44 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+648*x.val) 81+27)%81 ≠ 44%81 from by decide))
    heq

theorem no_h2_a3 (t v : Nat)
    (heq : 153*v+62=2^(3+648*t)+27) : False := by
  exact no_generic 153 3 27 62 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+648*x.val) 153+27)%153 ≠ 62%153 from by decide))
    heq

theorem no_h2_a4 (t v : Nat)
    (heq : 297*v+80=2^(3+648*t)+27) : False := by
  exact no_generic 297 3 27 80 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (3+648*x.val) 297+27)%297 ≠ 80%297 from by decide))
    heq

theorem no_h2_a5 (t v : Nat)
    (heq : 585*v+98=2^(3+648*t)+27) : False := by
  exact no_generic 585 3 27 98 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+648*x.val) 585+27)%585 ≠ 98%585 from by decide))
    heq

theorem no_h2_a6 (t v : Nat)
    (heq : 1161*v+116=2^(3+648*t)+27) : False := by
  exact no_generic 1161 3 27 116 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (3+648*x.val) 1161+27)%1161 ≠ 116%1161 from by decide))
    heq

theorem no_h3_a1 (t v : Nat)
    (heq : 135*v+70=2^(4+648*t)+81) : False := by
  exact no_generic 135 4 81 70 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+648*x.val) 135+81)%135 ≠ 70%135 from by decide))
    heq

theorem no_h3_a2 (t v : Nat)
    (heq : 243*v+124=2^(4+648*t)+81) : False := by
  exact no_generic 243 4 81 124 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+648*x.val) 243+81)%243 ≠ 124%243 from by decide))
    heq

theorem no_h3_a3 (t v : Nat)
    (heq : 459*v+178=2^(4+648*t)+81) : False := by
  exact no_generic 459 4 81 178 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+648*x.val) 459+81)%459 ≠ 178%459 from by decide))
    heq

theorem no_h3_a4 (t v : Nat)
    (heq : 891*v+232=2^(4+648*t)+81) : False := by
  exact no_generic 891 4 81 232 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (4+648*x.val) 891+81)%891 ≠ 232%891 from by decide))
    heq

theorem no_h3_a5 (t v : Nat)
    (heq : 1755*v+286=2^(4+648*t)+81) : False := by
  exact no_generic 1755 4 81 286 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+648*x.val) 1755+81)%1755 ≠ 286%1755 from by decide))
    heq

theorem only_h3_a6 (t v : Nat)
    (heq : 3483*v+340=2^(4+648*t)+81) : t%7=6 := by
  exact only_class 3483 4 81 340 7 6 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (4+648*x.val) 3483+81)%3483 = 340%3483 → x.val=6 from by decide))
    heq

theorem no_h3_a7 (t v : Nat)
    (heq : 6939*v+394=2^(4+648*t)+81) : False := by
  exact no_generic 6939 4 81 394 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (4+648*x.val) 6939+81)%6939 ≠ 394%6939 from by decide))
    heq

theorem no_h3_a8 (t v : Nat)
    (heq : 13851*v+448=2^(4+648*t)+81) : False := by
  exact no_generic 13851 4 81 448 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (4+648*x.val) 13851+81)%13851 ≠ 448%13851 from by decide))
    heq

theorem no_h4_a1 (t v : Nat)
    (heq : 405*v+194=2^(5+648*t)+243) : False := by
  exact no_generic 405 5 243 194 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+648*x.val) 405+243)%405 ≠ 194%405 from by decide))
    heq

theorem no_h4_a2 (t v : Nat)
    (heq : 729*v+356=2^(5+648*t)+243) : False := by
  exact no_generic 729 5 243 356 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (5+648*x.val) 729+243)%729 ≠ 356%729 from by decide))
    heq

theorem no_h4_a3 (t v : Nat)
    (heq : 1377*v+518=2^(5+648*t)+243) : False := by
  exact no_generic 1377 5 243 518 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+648*x.val) 1377+243)%1377 ≠ 518%1377 from by decide))
    heq

theorem no_h4_a4 (t v : Nat)
    (heq : 2673*v+680=2^(5+648*t)+243) : False := by
  exact no_generic 2673 5 243 680 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (5+648*x.val) 2673+243)%2673 ≠ 680%2673 from by decide))
    heq

theorem no_h4_a5 (t v : Nat)
    (heq : 5265*v+842=2^(5+648*t)+243) : False := by
  exact no_generic 5265 5 243 842 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+648*x.val) 5265+243)%5265 ≠ 842%5265 from by decide))
    heq

theorem no_h4_a6 (t v : Nat)
    (heq : 10449*v+1004=2^(5+648*t)+243) : False := by
  exact no_generic 10449 5 243 1004 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (5+648*x.val) 10449+243)%10449 ≠ 1004%10449 from by decide))
    heq

theorem no_h4_a7 (t v : Nat)
    (heq : 20817*v+1166=2^(5+648*t)+243) : False := by
  exact no_generic 20817 5 243 1166 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (5+648*x.val) 20817+243)%20817 ≠ 1166%20817 from by decide))
    heq

theorem no_h4_a8 (t v : Nat)
    (heq : 41553*v+1328=2^(5+648*t)+243) : False := by
  exact no_generic 41553 5 243 1328 9 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (5+648*x.val) 41553+243)%41553 ≠ 1328%41553 from by decide))
    heq

theorem no_h4_a9 (t v : Nat)
    (heq : 83025*v+1490=2^(5+648*t)+243) : False := by
  exact no_generic 83025 5 243 1490 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (5+648*x.val) 83025+243)%83025 ≠ 1490%83025 from by decide))
    heq

theorem no_h4_a10 (t v : Nat)
    (heq : 165969*v+1652=2^(5+648*t)+243) : False := by
  exact no_generic 165969 5 243 1652 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (5+648*x.val) 165969+243)%165969 ≠ 1652%165969 from by decide))
    heq

theorem no_h5_a1 (t v : Nat)
    (heq : 1215*v+550=2^(6+648*t)+729) : False := by
  exact no_generic 1215 6 729 550 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+648*x.val) 1215+729)%1215 ≠ 550%1215 from by decide))
    heq

theorem only_h5_a2 (t v : Nat)
    (heq : 2187*v+1036=2^(6+648*t)+729) : t%9=1 := by
  exact only_class 2187 6 729 1036 9 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (6+648*x.val) 2187+729)%2187 = 1036%2187 → x.val=1 from by decide))
    heq

theorem no_h5_a3 (t v : Nat)
    (heq : 4131*v+1522=2^(6+648*t)+729) : False := by
  exact no_generic 4131 6 729 1522 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+648*x.val) 4131+729)%4131 ≠ 1522%4131 from by decide))
    heq

theorem only_h5_a4 (t v : Nat)
    (heq : 8019*v+2008=2^(6+648*t)+729) : t%15=14 := by
  exact only_class 8019 6 729 2008 15 14 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 15,
        (Nat.powMod 2 (6+648*x.val) 8019+729)%8019 = 2008%8019 → x.val=14 from by decide))
    heq

theorem no_h5_a5 (t v : Nat)
    (heq : 15795*v+2494=2^(6+648*t)+729) : False := by
  exact no_generic 15795 6 729 2494 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+648*x.val) 15795+729)%15795 ≠ 2494%15795 from by decide))
    heq

theorem no_h5_a6 (t v : Nat)
    (heq : 31347*v+2980=2^(6+648*t)+729) : False := by
  exact no_generic 31347 6 729 2980 21 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 21,
        (Nat.powMod 2 (6+648*x.val) 31347+729)%31347 ≠ 2980%31347 from by decide))
    heq

theorem no_h5_a7 (t v : Nat)
    (heq : 62451*v+3466=2^(6+648*t)+729) : False := by
  exact no_generic 62451 6 729 3466 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (6+648*x.val) 62451+729)%62451 ≠ 3466%62451 from by decide))
    heq

theorem no_h5_a8 (t v : Nat)
    (heq : 124659*v+3952=2^(6+648*t)+729) : False := by
  exact no_generic 124659 6 729 3952 27 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 27,
        (Nat.powMod 2 (6+648*x.val) 124659+729)%124659 ≠ 3952%124659 from by decide))
    heq

theorem no_h5_a9 (t v : Nat)
    (heq : 249075*v+4438=2^(6+648*t)+729) : False := by
  exact no_generic 249075 6 729 4438 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (6+648*x.val) 249075+729)%249075 ≠ 4438%249075 from by decide))
    heq

theorem no_h5_a10 (t v : Nat)
    (heq : 497907*v+4924=2^(6+648*t)+729) : False := by
  exact no_generic 497907 6 729 4924 33 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 33,
        (Nat.powMod 2 (6+648*x.val) 497907+729)%497907 ≠ 4924%497907 from by decide))
    heq

theorem no_h5_a11 (t v : Nat)
    (heq : 995571*v+5410=2^(6+648*t)+729) : False := by
  exact no_generic 995571 6 729 5410 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (6+648*x.val) 995571+729)%995571 ≠ 5410%995571 from by decide))
    heq

theorem no_h5_a12 (t v : Nat)
    (heq : 1990899*v+5896=2^(6+648*t)+729) : False := by
  exact no_generic 1990899 6 729 5896 39 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 39,
        (Nat.powMod 2 (6+648*x.val) 1990899+729)%1990899 ≠ 5896%1990899 from by decide))
    heq

#print axioms no_h5_a12
#print axioms only_h3_a6
#print axioms only_h5_a2
#print axioms only_h5_a4
end SheepPower648
