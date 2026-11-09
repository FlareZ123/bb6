import SheepPower1296Core
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower1296

theorem no_h0_a1 (k v : Nat)
    (heq : 5*v+4 = 2^(1297+340200*k)+3) : False := by
  exact no_generic_equation
    5 1297 3 4 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1297+340200*t.val) 5+3)%5 ≠ 4%5 from by decide))
    heq

theorem no_h1_a1 (k v : Nat)
    (heq : 15*v+10 = 2^(1298+340200*k)+9) : False := by
  exact no_generic_equation
    15 1298 9 10 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1298+340200*t.val) 15+9)%15 ≠ 10%15 from by decide))
    heq

theorem no_h1_a2 (k v : Nat)
    (heq : 27*v+16 = 2^(1298+340200*k)+9) : False := by
  exact no_generic_equation
    27 1298 9 16 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1298+340200*t.val) 27+9)%27 ≠ 16%27 from by decide))
    heq

theorem no_h1_a3 (k v : Nat)
    (heq : 51*v+22 = 2^(1298+340200*k)+9) : False := by
  exact no_generic_equation
    51 1298 9 22 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1298+340200*t.val) 51+9)%51 ≠ 22%51 from by decide))
    heq

theorem no_h1_a4 (k v : Nat)
    (heq : 99*v+28 = 2^(1298+340200*k)+9) : False := by
  exact no_generic_equation
    99 1298 9 28 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1298+340200*t.val) 99+9)%99 ≠ 28%99 from by decide))
    heq

theorem no_h2_a1 (k v : Nat)
    (heq : 45*v+26 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    45 1299 27 26 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 45+27)%45 ≠ 26%45 from by decide))
    heq

theorem no_h2_a2 (k v : Nat)
    (heq : 81*v+44 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    81 1299 27 44 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 81+27)%81 ≠ 44%81 from by decide))
    heq

theorem no_h2_a3 (k v : Nat)
    (heq : 153*v+62 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    153 1299 27 62 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 153+27)%153 ≠ 62%153 from by decide))
    heq

theorem no_h2_a4 (k v : Nat)
    (heq : 297*v+80 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    297 1299 27 80 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 297+27)%297 ≠ 80%297 from by decide))
    heq

theorem no_h2_a5 (k v : Nat)
    (heq : 585*v+98 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    585 1299 27 98 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 585+27)%585 ≠ 98%585 from by decide))
    heq

theorem no_h2_a6 (k v : Nat)
    (heq : 1161*v+116 = 2^(1299+340200*k)+27) : False := by
  exact no_generic_equation
    1161 1299 27 116 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1299+340200*t.val) 1161+27)%1161 ≠ 116%1161 from by decide))
    heq

theorem no_h3_a1 (k v : Nat)
    (heq : 135*v+70 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    135 1300 81 70 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 135+81)%135 ≠ 70%135 from by decide))
    heq

theorem no_h3_a2 (k v : Nat)
    (heq : 243*v+124 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    243 1300 81 124 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 243+81)%243 ≠ 124%243 from by decide))
    heq

theorem no_h3_a3 (k v : Nat)
    (heq : 459*v+178 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    459 1300 81 178 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 459+81)%459 ≠ 178%459 from by decide))
    heq

theorem no_h3_a4 (k v : Nat)
    (heq : 891*v+232 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    891 1300 81 232 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 891+81)%891 ≠ 232%891 from by decide))
    heq

theorem no_h3_a5 (k v : Nat)
    (heq : 1755*v+286 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    1755 1300 81 286 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 1755+81)%1755 ≠ 286%1755 from by decide))
    heq

theorem no_h3_a6 (k v : Nat)
    (heq : 3483*v+340 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    3483 1300 81 340 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 3483+81)%3483 ≠ 340%3483 from by decide))
    heq

theorem no_h3_a7 (k v : Nat)
    (heq : 6939*v+394 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    6939 1300 81 394 2 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 2,
        (Nat.powMod 2 (1300+340200*t.val) 6939+81)%6939 ≠ 394%6939 from by decide))
    heq

theorem no_h3_a8 (k v : Nat)
    (heq : 13851*v+448 = 2^(1300+340200*k)+81) : False := by
  exact no_generic_equation
    13851 1300 81 448 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1300+340200*t.val) 13851+81)%13851 ≠ 448%13851 from by decide))
    heq

theorem no_h4_a1 (k v : Nat)
    (heq : 405*v+194 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    405 1301 243 194 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 405+243)%405 ≠ 194%405 from by decide))
    heq

theorem no_h4_a2 (k v : Nat)
    (heq : 729*v+356 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    729 1301 243 356 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 729+243)%729 ≠ 356%729 from by decide))
    heq

theorem no_h4_a3 (k v : Nat)
    (heq : 1377*v+518 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    1377 1301 243 518 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 1377+243)%1377 ≠ 518%1377 from by decide))
    heq

theorem no_h4_a4 (k v : Nat)
    (heq : 2673*v+680 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    2673 1301 243 680 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 2673+243)%2673 ≠ 680%2673 from by decide))
    heq

theorem no_h4_a5 (k v : Nat)
    (heq : 5265*v+842 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    5265 1301 243 842 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 5265+243)%5265 ≠ 842%5265 from by decide))
    heq

theorem no_h4_a6 (k v : Nat)
    (heq : 10449*v+1004 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    10449 1301 243 1004 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 10449+243)%10449 ≠ 1004%10449 from by decide))
    heq

theorem no_h4_a7 (k v : Nat)
    (heq : 20817*v+1166 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    20817 1301 243 1166 2 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 2,
        (Nat.powMod 2 (1301+340200*t.val) 20817+243)%20817 ≠ 1166%20817 from by decide))
    heq

theorem no_h4_a8 (k v : Nat)
    (heq : 41553*v+1328 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    41553 1301 243 1328 3 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 3,
        (Nat.powMod 2 (1301+340200*t.val) 41553+243)%41553 ≠ 1328%41553 from by decide))
    heq

theorem no_h4_a9 (k v : Nat)
    (heq : 83025*v+1490 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    83025 1301 243 1490 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1301+340200*t.val) 83025+243)%83025 ≠ 1490%83025 from by decide))
    heq

theorem no_h4_a10 (k v : Nat)
    (heq : 165969*v+1652 = 2^(1301+340200*k)+243) : False := by
  exact no_generic_equation
    165969 1301 243 1652 11 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 11,
        (Nat.powMod 2 (1301+340200*t.val) 165969+243)%165969 ≠ 1652%165969 from by decide))
    heq

theorem no_h5_a1 (k v : Nat)
    (heq : 1215*v+550 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    1215 1302 729 550 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 1215+729)%1215 ≠ 550%1215 from by decide))
    heq

theorem no_h5_a2 (k v : Nat)
    (heq : 2187*v+1036 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    2187 1302 729 1036 3 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 3,
        (Nat.powMod 2 (1302+340200*t.val) 2187+729)%2187 ≠ 1036%2187 from by decide))
    heq

theorem no_h5_a3 (k v : Nat)
    (heq : 4131*v+1522 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    4131 1302 729 1522 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 4131+729)%4131 ≠ 1522%4131 from by decide))
    heq

theorem no_h5_a4 (k v : Nat)
    (heq : 8019*v+2008 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    8019 1302 729 2008 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 8019+729)%8019 ≠ 2008%8019 from by decide))
    heq

theorem no_h5_a5 (k v : Nat)
    (heq : 15795*v+2494 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    15795 1302 729 2494 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 15795+729)%15795 ≠ 2494%15795 from by decide))
    heq

theorem no_h5_a6 (k v : Nat)
    (heq : 31347*v+2980 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    31347 1302 729 2980 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 31347+729)%31347 ≠ 2980%31347 from by decide))
    heq

theorem no_h5_a7 (k v : Nat)
    (heq : 62451*v+3466 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    62451 1302 729 3466 2 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 2,
        (Nat.powMod 2 (1302+340200*t.val) 62451+729)%62451 ≠ 3466%62451 from by decide))
    heq

theorem no_h5_a8 (k v : Nat)
    (heq : 124659*v+3952 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    124659 1302 729 3952 9 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 9,
        (Nat.powMod 2 (1302+340200*t.val) 124659+729)%124659 ≠ 3952%124659 from by decide))
    heq

theorem no_h5_a9 (k v : Nat)
    (heq : 249075*v+4438 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    249075 1302 729 4438 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 249075+729)%249075 ≠ 4438%249075 from by decide))
    heq

theorem no_h5_a10 (k v : Nat)
    (heq : 497907*v+4924 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    497907 1302 729 4924 11 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 11,
        (Nat.powMod 2 (1302+340200*t.val) 497907+729)%497907 ≠ 4924%497907 from by decide))
    heq

theorem no_h5_a11 (k v : Nat)
    (heq : 995571*v+5410 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    995571 1302 729 5410 1 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 1,
        (Nat.powMod 2 (1302+340200*t.val) 995571+729)%995571 ≠ 5410%995571 from by decide))
    heq

theorem no_h5_a12 (k v : Nat)
    (heq : 1990899*v+5896 = 2^(1302+340200*k)+729) : False := by
  exact no_generic_equation
    1990899 1302 729 5896 13 k v
    (by decide) (by decide)
    (by rw [←Nat.powMod_def]; decide)
    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using
      (show ∀ t : Fin 13,
        (Nat.powMod 2 (1302+340200*t.val) 1990899+729)%1990899 ≠ 5896%1990899 from by decide))
    heq

#print axioms no_h0_a1
#print axioms no_h5_a12
end SheepPower1296
