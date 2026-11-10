import SheepPower486Core
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower486

theorem no_h0_a1 (t v : Nat)
    (heq : 5*v+4=2^(1+486*t)+3) : False := by
  exact no_generic 5 1 3 4 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (1+486*x.val) 5+3)%5 ≠ 4%5 from by decide))
    heq

theorem only_h1_a1 (t v : Nat)
    (heq : 15*v+10=2^(2+486*t)+9) : t%2=1 := by
  exact only_class 15 2 9 10 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (2+486*x.val) 15+9)%15 = 10%15 → x.val=1 from by decide))
    heq

theorem no_h1_a2 (t v : Nat)
    (heq : 27*v+16=2^(2+486*t)+9) : False := by
  exact no_generic 27 2 9 16 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (2+486*x.val) 27+9)%27 ≠ 16%27 from by decide))
    heq

theorem only_h1_a3 (t v : Nat)
    (heq : 51*v+22=2^(2+486*t)+9) : t%4=2 := by
  exact only_class 51 2 9 22 4 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (2+486*x.val) 51+9)%51 = 22%51 → x.val=2 from by decide))
    heq

theorem no_h1_a4 (t v : Nat)
    (heq : 99*v+28=2^(2+486*t)+9) : False := by
  exact no_generic 99 2 9 28 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (2+486*x.val) 99+9)%99 ≠ 28%99 from by decide))
    heq

theorem no_h2_a1 (t v : Nat)
    (heq : 45*v+26=2^(3+486*t)+27) : False := by
  exact no_generic 45 3 27 26 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (3+486*x.val) 45+27)%45 ≠ 26%45 from by decide))
    heq

theorem no_h2_a2 (t v : Nat)
    (heq : 81*v+44=2^(3+486*t)+27) : False := by
  exact no_generic 81 3 27 44 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (3+486*x.val) 81+27)%81 ≠ 44%81 from by decide))
    heq

theorem no_h2_a3 (t v : Nat)
    (heq : 153*v+62=2^(3+486*t)+27) : False := by
  exact no_generic 153 3 27 62 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (3+486*x.val) 153+27)%153 ≠ 62%153 from by decide))
    heq

theorem no_h2_a4 (t v : Nat)
    (heq : 297*v+80=2^(3+486*t)+27) : False := by
  exact no_generic 297 3 27 80 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (3+486*x.val) 297+27)%297 ≠ 80%297 from by decide))
    heq

theorem no_h2_a5 (t v : Nat)
    (heq : 585*v+98=2^(3+486*t)+27) : False := by
  exact no_generic 585 3 27 98 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (3+486*x.val) 585+27)%585 ≠ 98%585 from by decide))
    heq

theorem no_h2_a6 (t v : Nat)
    (heq : 1161*v+116=2^(3+486*t)+27) : False := by
  exact no_generic 1161 3 27 116 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (3+486*x.val) 1161+27)%1161 ≠ 116%1161 from by decide))
    heq

theorem only_h3_a1 (t v : Nat)
    (heq : 135*v+70=2^(4+486*t)+81) : t%2=1 := by
  exact only_class 135 4 81 70 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (4+486*x.val) 135+81)%135 = 70%135 → x.val=1 from by decide))
    heq

theorem no_h3_a2 (t v : Nat)
    (heq : 243*v+124=2^(4+486*t)+81) : False := by
  exact no_generic 243 4 81 124 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+486*x.val) 243+81)%243 ≠ 124%243 from by decide))
    heq

theorem no_h3_a3 (t v : Nat)
    (heq : 459*v+178=2^(4+486*t)+81) : False := by
  exact no_generic 459 4 81 178 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (4+486*x.val) 459+81)%459 ≠ 178%459 from by decide))
    heq

theorem no_h3_a4 (t v : Nat)
    (heq : 891*v+232=2^(4+486*t)+81) : False := by
  exact no_generic 891 4 81 232 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (4+486*x.val) 891+81)%891 ≠ 232%891 from by decide))
    heq

theorem no_h3_a5 (t v : Nat)
    (heq : 1755*v+286=2^(4+486*t)+81) : False := by
  exact no_generic 1755 4 81 286 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (4+486*x.val) 1755+81)%1755 ≠ 286%1755 from by decide))
    heq

theorem only_h3_a6 (t v : Nat)
    (heq : 3483*v+340=2^(4+486*t)+81) : t%7=1 := by
  exact only_class 3483 4 81 340 7 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (4+486*x.val) 3483+81)%3483 = 340%3483 → x.val=1 from by decide))
    heq

theorem no_h3_a7 (t v : Nat)
    (heq : 6939*v+394=2^(4+486*t)+81) : False := by
  exact no_generic 6939 4 81 394 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (4+486*x.val) 6939+81)%6939 ≠ 394%6939 from by decide))
    heq

theorem no_h3_a8 (t v : Nat)
    (heq : 13851*v+448=2^(4+486*t)+81) : False := by
  exact no_generic 13851 4 81 448 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (4+486*x.val) 13851+81)%13851 ≠ 448%13851 from by decide))
    heq

theorem no_h4_a1 (t v : Nat)
    (heq : 405*v+194=2^(5+486*t)+243) : False := by
  exact no_generic 405 5 243 194 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (5+486*x.val) 405+243)%405 ≠ 194%405 from by decide))
    heq

theorem no_h4_a2 (t v : Nat)
    (heq : 729*v+356=2^(5+486*t)+243) : False := by
  exact no_generic 729 5 243 356 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 1,
        (Nat.powMod 2 (5+486*x.val) 729+243)%729 ≠ 356%729 from by decide))
    heq

theorem no_h4_a3 (t v : Nat)
    (heq : 1377*v+518=2^(5+486*t)+243) : False := by
  exact no_generic 1377 5 243 518 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (5+486*x.val) 1377+243)%1377 ≠ 518%1377 from by decide))
    heq

theorem no_h4_a4 (t v : Nat)
    (heq : 2673*v+680=2^(5+486*t)+243) : False := by
  exact no_generic 2673 5 243 680 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (5+486*x.val) 2673+243)%2673 ≠ 680%2673 from by decide))
    heq

theorem no_h4_a5 (t v : Nat)
    (heq : 5265*v+842=2^(5+486*t)+243) : False := by
  exact no_generic 5265 5 243 842 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (5+486*x.val) 5265+243)%5265 ≠ 842%5265 from by decide))
    heq

theorem no_h4_a6 (t v : Nat)
    (heq : 10449*v+1004=2^(5+486*t)+243) : False := by
  exact no_generic 10449 5 243 1004 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (5+486*x.val) 10449+243)%10449 ≠ 1004%10449 from by decide))
    heq

theorem no_h4_a7 (t v : Nat)
    (heq : 20817*v+1166=2^(5+486*t)+243) : False := by
  exact no_generic 20817 5 243 1166 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (5+486*x.val) 20817+243)%20817 ≠ 1166%20817 from by decide))
    heq

theorem no_h4_a8 (t v : Nat)
    (heq : 41553*v+1328=2^(5+486*t)+243) : False := by
  exact no_generic 41553 5 243 1328 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (5+486*x.val) 41553+243)%41553 ≠ 1328%41553 from by decide))
    heq

theorem no_h4_a9 (t v : Nat)
    (heq : 83025*v+1490=2^(5+486*t)+243) : False := by
  exact no_generic 83025 5 243 1490 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (5+486*x.val) 83025+243)%83025 ≠ 1490%83025 from by decide))
    heq

theorem no_h4_a10 (t v : Nat)
    (heq : 165969*v+1652=2^(5+486*t)+243) : False := by
  exact no_generic 165969 5 243 1652 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (5+486*x.val) 165969+243)%165969 ≠ 1652%165969 from by decide))
    heq

theorem only_h5_a1 (t v : Nat)
    (heq : 1215*v+550=2^(6+486*t)+729) : t%2=1 := by
  exact only_class 1215 6 729 550 2 1 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (6+486*x.val) 1215+729)%1215 = 550%1215 → x.val=1 from by decide))
    heq

theorem no_h5_a2 (t v : Nat)
    (heq : 2187*v+1036=2^(6+486*t)+729) : False := by
  exact no_generic 2187 6 729 1036 3 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 3,
        (Nat.powMod 2 (6+486*x.val) 2187+729)%2187 ≠ 1036%2187 from by decide))
    heq

theorem no_h5_a3 (t v : Nat)
    (heq : 4131*v+1522=2^(6+486*t)+729) : False := by
  exact no_generic 4131 6 729 1522 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (6+486*x.val) 4131+729)%4131 ≠ 1522%4131 from by decide))
    heq

theorem no_h5_a4 (t v : Nat)
    (heq : 8019*v+2008=2^(6+486*t)+729) : False := by
  exact no_generic 8019 6 729 2008 5 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 5,
        (Nat.powMod 2 (6+486*x.val) 8019+729)%8019 ≠ 2008%8019 from by decide))
    heq

theorem no_h5_a5 (t v : Nat)
    (heq : 15795*v+2494=2^(6+486*t)+729) : False := by
  exact no_generic 15795 6 729 2494 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (6+486*x.val) 15795+729)%15795 ≠ 2494%15795 from by decide))
    heq

theorem no_h5_a6 (t v : Nat)
    (heq : 31347*v+2980=2^(6+486*t)+729) : False := by
  exact no_generic 31347 6 729 2980 7 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 7,
        (Nat.powMod 2 (6+486*x.val) 31347+729)%31347 ≠ 2980%31347 from by decide))
    heq

theorem no_h5_a7 (t v : Nat)
    (heq : 62451*v+3466=2^(6+486*t)+729) : False := by
  exact no_generic 62451 6 729 3466 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (6+486*x.val) 62451+729)%62451 ≠ 3466%62451 from by decide))
    heq

theorem no_h5_a8 (t v : Nat)
    (heq : 124659*v+3952=2^(6+486*t)+729) : False := by
  exact no_generic 124659 6 729 3952 9 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (6+486*x.val) 124659+729)%124659 ≠ 3952%124659 from by decide))
    heq

theorem no_h5_a9 (t v : Nat)
    (heq : 249075*v+4438=2^(6+486*t)+729) : False := by
  exact no_generic 249075 6 729 4438 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (6+486*x.val) 249075+729)%249075 ≠ 4438%249075 from by decide))
    heq

theorem no_h5_a10 (t v : Nat)
    (heq : 497907*v+4924=2^(6+486*t)+729) : False := by
  exact no_generic 497907 6 729 4924 11 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 11,
        (Nat.powMod 2 (6+486*x.val) 497907+729)%497907 ≠ 4924%497907 from by decide))
    heq

theorem no_h5_a11 (t v : Nat)
    (heq : 995571*v+5410=2^(6+486*t)+729) : False := by
  exact no_generic 995571 6 729 5410 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (6+486*x.val) 995571+729)%995571 ≠ 5410%995571 from by decide))
    heq

theorem no_h5_a12 (t v : Nat)
    (heq : 1990899*v+5896=2^(6+486*t)+729) : False := by
  exact no_generic 1990899 6 729 5896 13 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 13,
        (Nat.powMod 2 (6+486*x.val) 1990899+729)%1990899 ≠ 5896%1990899 from by decide))
    heq

theorem no_h6_a1 (t v : Nat)
    (heq : 3645*v+1586=2^(7+486*t)+2187) : False := by
  exact no_generic 3645 7 2187 1586 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (7+486*x.val) 3645+2187)%3645 ≠ 1586%3645 from by decide))
    heq

theorem only_h6_a2 (t v : Nat)
    (heq : 6561*v+3044=2^(7+486*t)+2187) : t%9=2 := by
  exact only_class 6561 7 2187 3044 9 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 9,
        (Nat.powMod 2 (7+486*x.val) 6561+2187)%6561 = 3044%6561 → x.val=2 from by decide))
    heq

theorem no_h6_a3 (t v : Nat)
    (heq : 12393*v+4502=2^(7+486*t)+2187) : False := by
  exact no_generic 12393 7 2187 4502 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (7+486*x.val) 12393+2187)%12393 ≠ 4502%12393 from by decide))
    heq

theorem no_h6_a4 (t v : Nat)
    (heq : 24057*v+5960=2^(7+486*t)+2187) : False := by
  exact no_generic 24057 7 2187 5960 15 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 15,
        (Nat.powMod 2 (7+486*x.val) 24057+2187)%24057 ≠ 5960%24057 from by decide))
    heq

theorem no_h6_a5 (t v : Nat)
    (heq : 47385*v+7418=2^(7+486*t)+2187) : False := by
  exact no_generic 47385 7 2187 7418 2 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 2,
        (Nat.powMod 2 (7+486*x.val) 47385+2187)%47385 ≠ 7418%47385 from by decide))
    heq

theorem no_h6_a6 (t v : Nat)
    (heq : 94041*v+8876=2^(7+486*t)+2187) : False := by
  exact no_generic 94041 7 2187 8876 21 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 21,
        (Nat.powMod 2 (7+486*x.val) 94041+2187)%94041 ≠ 8876%94041 from by decide))
    heq

theorem no_h6_a7 (t v : Nat)
    (heq : 187353*v+10334=2^(7+486*t)+2187) : False := by
  exact no_generic 187353 7 2187 10334 8 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 8,
        (Nat.powMod 2 (7+486*x.val) 187353+2187)%187353 ≠ 10334%187353 from by decide))
    heq

theorem no_h6_a8 (t v : Nat)
    (heq : 373977*v+11792=2^(7+486*t)+2187) : False := by
  exact no_generic 373977 7 2187 11792 27 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 27,
        (Nat.powMod 2 (7+486*x.val) 373977+2187)%373977 ≠ 11792%373977 from by decide))
    heq

theorem no_h6_a9 (t v : Nat)
    (heq : 747225*v+13250=2^(7+486*t)+2187) : False := by
  exact no_generic 747225 7 2187 13250 10 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 10,
        (Nat.powMod 2 (7+486*x.val) 747225+2187)%747225 ≠ 13250%747225 from by decide))
    heq

theorem no_h6_a10 (t v : Nat)
    (heq : 1493721*v+14708=2^(7+486*t)+2187) : False := by
  exact no_generic 1493721 7 2187 14708 33 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 33,
        (Nat.powMod 2 (7+486*x.val) 1493721+2187)%1493721 ≠ 14708%1493721 from by decide))
    heq

theorem no_h6_a11 (t v : Nat)
    (heq : 2986713*v+16166=2^(7+486*t)+2187) : False := by
  exact no_generic 2986713 7 2187 16166 4 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 4,
        (Nat.powMod 2 (7+486*x.val) 2986713+2187)%2986713 ≠ 16166%2986713 from by decide))
    heq

theorem no_h6_a12 (t v : Nat)
    (heq : 5972697*v+17624=2^(7+486*t)+2187) : False := by
  exact no_generic 5972697 7 2187 17624 39 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 39,
        (Nat.powMod 2 (7+486*x.val) 5972697+2187)%5972697 ≠ 17624%5972697 from by decide))
    heq

theorem no_h6_a13 (t v : Nat)
    (heq : 11944665*v+19082=2^(7+486*t)+2187) : False := by
  exact no_generic 11944665 7 2187 19082 14 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 14,
        (Nat.powMod 2 (7+486*x.val) 11944665+2187)%11944665 ≠ 19082%11944665 from by decide))
    heq

theorem no_h6_a14 (t v : Nat)
    (heq : 23888601*v+20540=2^(7+486*t)+2187) : False := by
  exact no_generic 23888601 7 2187 20540 45 t v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ x : Fin 45,
        (Nat.powMod 2 (7+486*x.val) 23888601+2187)%23888601 ≠ 20540%23888601 from by decide))
    heq

#print axioms no_h6_a14
#print axioms only_h6_a2
end SheepPower486
