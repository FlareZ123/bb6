-- Generated exact affine-node and progression-specific low-a certificates.
-- Source: inverse_tree_certificate.py, inverse_tree_h1a3_h3a6_certificate.py,
--         inverse_tree_44_classes_certificate.py.
-- All arithmetic proofs below use kernel `decide`; this file has NOT yet been Lean-compiled.
import SheepPower1458SourceIntegration

namespace SheepPower1458

def residues_t1 : List Nat := [1]
def period_t1 : Nat := 32526940446000

def nodes_t1 : List AffineNode :=
  [
    { s := 0, b := 0, c := 0, C := 1 },
    { s := 3, b := 0, c := 2, C := 15 },
    { s := 5, b := 22, c := 0, C := 135 },
    { s := 7, b := 358, c := 0, C := 1215 },
    { s := 9, b := 3862, c := 0, C := 10935 },
    { s := 10, b := 0, c := 9772, C := 19683 },
    { s := 7, b := 0, c := 452, C := 405 },
    { s := 7, b := 0, c := 182, C := 675 },
    { s := 9, b := 0, c := 3428, C := 3645 },
    { s := 11, b := 0, c := 42872, C := 20655 },
    { s := 12, b := 0, c := 78454, C := 98415 },
    { s := 13, b := 0, c := 156908, C := 98415 },
    { s := 13, b := 0, c := 212798, C := 103275 },
    { s := 14, b := 0, c := 510646, C := 492075 },
    { s := 16, b := 0, c := 2436244, C := 885735 }
  ]

def edges_t1 : List (Nat × Nat × Nat × Nat) :=
  [
    ⟨0, 1, 1, 1⟩,
    ⟨0, 2, 3, 1⟩,
    ⟨0, 3, 5, 1⟩,
    ⟨0, 4, 7, 1⟩,
    ⟨0, 5, 7, 2⟩,
    ⟨1, 6, 1, 2⟩,
    ⟨2, 7, 0, 1⟩,
    ⟨2, 8, 1, 2⟩,
    ⟨3, 9, 0, 3⟩,
    ⟨5, 10, 0, 1⟩,
    ⟨8, 11, 1, 2⟩,
    ⟨9, 12, 0, 1⟩,
    ⟨10, 13, 0, 1⟩,
    ⟨11, 14, 0, 2⟩
  ]

theorem val_nohit_t1_n1 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+3) 27 ≠ 17%27 := by
  decide
theorem val_period_t1_n1 :
    Nat.powMod 2 (47424279170268000) 27 = 1 := by
  decide

theorem val_nohit_t1_n2 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+5) 243 ≠ 113%243 := by
  decide
theorem val_period_t1_n2 :
    Nat.powMod 2 (47424279170268000) 243 = 1 := by
  decide

theorem val_nohit_t1_n3 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+7) 2187 ≠ 857%2187 := by
  decide
theorem val_period_t1_n3 :
    Nat.powMod 2 (47424279170268000) 2187 = 1 := by
  decide

theorem val_nohit_t1_n4 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+9) 6561 ≠ 7073%6561 := by
  decide
theorem val_period_t1_n4 :
    Nat.powMod 2 (47424279170268000) 6561 = 1 := by
  decide

theorem val_nohit_t1_n5 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+10) 59049 ≠ 29455%59049 := by
  decide
theorem val_period_t1_n5 :
    Nat.powMod 2 (47424279170268000) 59049 = 1 := by
  decide

theorem val_nohit_t1_n6 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+7) 2187 ≠ 857%2187 := by
  decide
theorem val_period_t1_n6 :
    Nat.powMod 2 (47424279170268000) 2187 = 1 := by
  decide

theorem val_nohit_t1_n7 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+7) 2187 ≠ 857%2187 := by
  decide
theorem val_period_t1_n7 :
    Nat.powMod 2 (47424279170268000) 2187 = 1 := by
  decide

theorem val_nohit_t1_n8 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+9) 6561 ≠ 7073%6561 := by
  decide
theorem val_period_t1_n8 :
    Nat.powMod 2 (47424279170268000) 6561 = 1 := by
  decide

theorem val_nohit_t1_n9 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+11) 729 ≠ 63527%729 := by
  decide
theorem val_period_t1_n9 :
    Nat.powMod 2 (47424279170268000) 729 = 1 := by
  decide

theorem val_nohit_t1_n10 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+12) 59049 ≠ 176869%59049 := by
  decide
theorem val_period_t1_n10 :
    Nat.powMod 2 (47424279170268000) 59049 = 1 := by
  decide

theorem val_nohit_t1_n11 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+13) 59049 ≠ 255323%59049 := by
  decide
theorem val_period_t1_n11 :
    Nat.powMod 2 (47424279170268000) 59049 = 1 := by
  decide

theorem val_nohit_t1_n12 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+13) 729 ≠ 316073%729 := by
  decide
theorem val_period_t1_n12 :
    Nat.powMod 2 (47424279170268000) 729 = 1 := by
  decide

theorem val_nohit_t1_n13 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+14) 59049 ≠ 1002721%59049 := by
  decide
theorem val_period_t1_n13 :
    Nat.powMod 2 (47424279170268000) 59049 = 1 := by
  decide

theorem val_nohit_t1_n14 :
    ∀ r ∈ residues_t1,
      Nat.powMod 2 (1458*r+16) 531441 ≠ 3321979%531441 := by
  decide
theorem val_period_t1_n14 :
    Nat.powMod 2 (47424279170268000) 531441 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 75+0)%75 ≠ 19%75 := by
  decide
theorem low_period_t1_n1_h0_a1 :
    Nat.powMod 2 (47424279170268000) 75 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 135+0)%135 ≠ 49%135 := by
  decide
theorem low_period_t1_n1_h0_a2 :
    Nat.powMod 2 (47424279170268000) 135 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 255+0)%255 ≠ 79%255 := by
  decide
theorem low_period_t1_n1_h0_a3 :
    Nat.powMod 2 (47424279170268000) 255 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 495+0)%495 ≠ 109%495 := by
  decide
theorem low_period_t1_n1_h0_a4 :
    Nat.powMod 2 (47424279170268000) 495 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 975+0)%975 ≠ 139%975 := by
  decide
theorem low_period_t1_n1_h0_a5 :
    Nat.powMod 2 (47424279170268000) 975 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 1935+0)%1935 ≠ 169%1935 := by
  decide
theorem low_period_t1_n1_h0_a6 :
    Nat.powMod 2 (47424279170268000) 1935 = 1 := by
  decide

theorem low_nohit_t1_n1_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+4) 3855+0)%3855 ≠ 199%3855 := by
  decide
theorem low_period_t1_n1_h0_a7 :
    Nat.powMod 2 (47424279170268000) 3855 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 225+0)%225 ≠ 23%225 := by
  decide
theorem low_period_t1_n1_h1_a1 :
    Nat.powMod 2 (47424279170268000) 225 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 765+0)%765 ≠ 203%765 := by
  decide
theorem low_period_t1_n1_h1_a3 :
    Nat.powMod 2 (47424279170268000) 765 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 1485+0)%1485 ≠ 293%1485 := by
  decide
theorem low_period_t1_n1_h1_a4 :
    Nat.powMod 2 (47424279170268000) 1485 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 2925+0)%2925 ≠ 383%2925 := by
  decide
theorem low_period_t1_n1_h1_a5 :
    Nat.powMod 2 (47424279170268000) 2925 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 5805+0)%5805 ≠ 473%5805 := by
  decide
theorem low_period_t1_n1_h1_a6 :
    Nat.powMod 2 (47424279170268000) 5805 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 11565+0)%11565 ≠ 563%11565 := by
  decide
theorem low_period_t1_n1_h1_a7 :
    Nat.powMod 2 (47424279170268000) 11565 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 23085+0)%23085 ≠ 653%23085 := by
  decide
theorem low_period_t1_n1_h1_a8 :
    Nat.powMod 2 (47424279170268000) 23085 = 1 := by
  decide

theorem low_nohit_t1_n1_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+5) 46125+0)%46125 ≠ 743%46125 := by
  decide
theorem low_period_t1_n1_h1_a9 :
    Nat.powMod 2 (47424279170268000) 46125 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 1215+0)%1215 ≠ 361%1215 := by
  decide
theorem low_period_t1_n2_h0_a2 :
    Nat.powMod 2 (47424279170268000) 1215 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 2295+0)%2295 ≠ 631%2295 := by
  decide
theorem low_period_t1_n2_h0_a3 :
    Nat.powMod 2 (47424279170268000) 2295 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 4455+0)%4455 ≠ 901%4455 := by
  decide
theorem low_period_t1_n2_h0_a4 :
    Nat.powMod 2 (47424279170268000) 4455 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 8775+0)%8775 ≠ 1171%8775 := by
  decide
theorem low_period_t1_n2_h0_a5 :
    Nat.powMod 2 (47424279170268000) 8775 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 17415+0)%17415 ≠ 1441%17415 := by
  decide
theorem low_period_t1_n2_h0_a6 :
    Nat.powMod 2 (47424279170268000) 17415 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 34695+0)%34695 ≠ 1711%34695 := by
  decide
theorem low_period_t1_n2_h0_a7 :
    Nat.powMod 2 (47424279170268000) 34695 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 69255+0)%69255 ≠ 1981%69255 := by
  decide
theorem low_period_t1_n2_h0_a8 :
    Nat.powMod 2 (47424279170268000) 69255 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 138375+0)%138375 ≠ 2251%138375 := by
  decide
theorem low_period_t1_n2_h0_a9 :
    Nat.powMod 2 (47424279170268000) 138375 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 276615+0)%276615 ≠ 2521%276615 := by
  decide
theorem low_period_t1_n2_h0_a10 :
    Nat.powMod 2 (47424279170268000) 276615 = 1 := by
  decide

theorem low_nohit_t1_n2_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+6) 553095+0)%553095 ≠ 2791%553095 := by
  decide
theorem low_period_t1_n2_h0_a11 :
    Nat.powMod 2 (47424279170268000) 553095 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 2025+0)%2025 ≠ 47%2025 := by
  decide
theorem low_period_t1_n2_h1_a1 :
    Nat.powMod 2 (47424279170268000) 2025 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 6885+0)%6885 ≠ 1667%6885 := by
  decide
theorem low_period_t1_n2_h1_a3 :
    Nat.powMod 2 (47424279170268000) 6885 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 13365+0)%13365 ≠ 2477%13365 := by
  decide
theorem low_period_t1_n2_h1_a4 :
    Nat.powMod 2 (47424279170268000) 13365 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 26325+0)%26325 ≠ 3287%26325 := by
  decide
theorem low_period_t1_n2_h1_a5 :
    Nat.powMod 2 (47424279170268000) 26325 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 52245+0)%52245 ≠ 4097%52245 := by
  decide
theorem low_period_t1_n2_h1_a6 :
    Nat.powMod 2 (47424279170268000) 52245 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 104085+0)%104085 ≠ 4907%104085 := by
  decide
theorem low_period_t1_n2_h1_a7 :
    Nat.powMod 2 (47424279170268000) 104085 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 207765+0)%207765 ≠ 5717%207765 := by
  decide
theorem low_period_t1_n2_h1_a8 :
    Nat.powMod 2 (47424279170268000) 207765 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 415125+0)%415125 ≠ 6527%415125 := by
  decide
theorem low_period_t1_n2_h1_a9 :
    Nat.powMod 2 (47424279170268000) 415125 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 829845+0)%829845 ≠ 7337%829845 := by
  decide
theorem low_period_t1_n2_h1_a10 :
    Nat.powMod 2 (47424279170268000) 829845 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 1659285+0)%1659285 ≠ 8147%1659285 := by
  decide
theorem low_period_t1_n2_h1_a11 :
    Nat.powMod 2 (47424279170268000) 1659285 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 3318165+0)%3318165 ≠ 8957%3318165 := by
  decide
theorem low_period_t1_n2_h1_a12 :
    Nat.powMod 2 (47424279170268000) 3318165 = 1 := by
  decide

theorem low_nohit_t1_n2_h1_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+7) 6635925+0)%6635925 ≠ 9767%6635925 := by
  decide
theorem low_period_t1_n2_h1_a13 :
    Nat.powMod 2 (47424279170268000) 6635925 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 6075+0)%6075 ≠ 499%6075 := by
  decide
theorem low_period_t1_n3_h0_a1 :
    Nat.powMod 2 (47424279170268000) 6075 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 10935+0)%10935 ≠ 2929%10935 := by
  decide
theorem low_period_t1_n3_h0_a2 :
    Nat.powMod 2 (47424279170268000) 10935 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 40095+0)%40095 ≠ 7789%40095 := by
  decide
theorem low_period_t1_n3_h0_a4 :
    Nat.powMod 2 (47424279170268000) 40095 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 78975+0)%78975 ≠ 10219%78975 := by
  decide
theorem low_period_t1_n3_h0_a5 :
    Nat.powMod 2 (47424279170268000) 78975 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 156735+0)%156735 ≠ 12649%156735 := by
  decide
theorem low_period_t1_n3_h0_a6 :
    Nat.powMod 2 (47424279170268000) 156735 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 312255+0)%312255 ≠ 15079%312255 := by
  decide
theorem low_period_t1_n3_h0_a7 :
    Nat.powMod 2 (47424279170268000) 312255 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 623295+0)%623295 ≠ 17509%623295 := by
  decide
theorem low_period_t1_n3_h0_a8 :
    Nat.powMod 2 (47424279170268000) 623295 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 1245375+0)%1245375 ≠ 19939%1245375 := by
  decide
theorem low_period_t1_n3_h0_a9 :
    Nat.powMod 2 (47424279170268000) 1245375 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 2489535+0)%2489535 ≠ 22369%2489535 := by
  decide
theorem low_period_t1_n3_h0_a10 :
    Nat.powMod 2 (47424279170268000) 2489535 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 4977855+0)%4977855 ≠ 24799%4977855 := by
  decide
theorem low_period_t1_n3_h0_a11 :
    Nat.powMod 2 (47424279170268000) 4977855 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 9954495+0)%9954495 ≠ 27229%9954495 := by
  decide
theorem low_period_t1_n3_h0_a12 :
    Nat.powMod 2 (47424279170268000) 9954495 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 19907775+0)%19907775 ≠ 29659%19907775 := by
  decide
theorem low_period_t1_n3_h0_a13 :
    Nat.powMod 2 (47424279170268000) 19907775 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 39814335+0)%39814335 ≠ 32089%39814335 := by
  decide
theorem low_period_t1_n3_h0_a14 :
    Nat.powMod 2 (47424279170268000) 39814335 = 1 := by
  decide

theorem low_nohit_t1_n3_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 79627455+0)%79627455 ≠ 34519%79627455 := by
  decide
theorem low_period_t1_n3_h0_a15 :
    Nat.powMod 2 (47424279170268000) 79627455 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 18225+217)%18225 ≠ 0%18225 := by
  decide
theorem low_period_t1_n3_h1_a1 :
    Nat.powMod 2 (47424279170268000) 18225 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 32805+0)%32805 ≠ 7073%32805 := by
  decide
theorem low_period_t1_n3_h1_a2 :
    Nat.powMod 2 (47424279170268000) 32805 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 61965+0)%61965 ≠ 14363%61965 := by
  decide
theorem low_period_t1_n3_h1_a3 :
    Nat.powMod 2 (47424279170268000) 61965 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 120285+0)%120285 ≠ 21653%120285 := by
  decide
theorem low_period_t1_n3_h1_a4 :
    Nat.powMod 2 (47424279170268000) 120285 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 236925+0)%236925 ≠ 28943%236925 := by
  decide
theorem low_period_t1_n3_h1_a5 :
    Nat.powMod 2 (47424279170268000) 236925 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 470205+0)%470205 ≠ 36233%470205 := by
  decide
theorem low_period_t1_n3_h1_a6 :
    Nat.powMod 2 (47424279170268000) 470205 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 936765+0)%936765 ≠ 43523%936765 := by
  decide
theorem low_period_t1_n3_h1_a7 :
    Nat.powMod 2 (47424279170268000) 936765 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 1869885+0)%1869885 ≠ 50813%1869885 := by
  decide
theorem low_period_t1_n3_h1_a8 :
    Nat.powMod 2 (47424279170268000) 1869885 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 3736125+0)%3736125 ≠ 58103%3736125 := by
  decide
theorem low_period_t1_n3_h1_a9 :
    Nat.powMod 2 (47424279170268000) 3736125 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 7468605+0)%7468605 ≠ 65393%7468605 := by
  decide
theorem low_period_t1_n3_h1_a10 :
    Nat.powMod 2 (47424279170268000) 7468605 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 14933565+0)%14933565 ≠ 72683%14933565 := by
  decide
theorem low_period_t1_n3_h1_a11 :
    Nat.powMod 2 (47424279170268000) 14933565 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 29863485+0)%29863485 ≠ 79973%29863485 := by
  decide
theorem low_period_t1_n3_h1_a12 :
    Nat.powMod 2 (47424279170268000) 29863485 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 59723325+0)%59723325 ≠ 87263%59723325 := by
  decide
theorem low_period_t1_n3_h1_a13 :
    Nat.powMod 2 (47424279170268000) 59723325 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 119443005+0)%119443005 ≠ 94553%119443005 := by
  decide
theorem low_period_t1_n3_h1_a14 :
    Nat.powMod 2 (47424279170268000) 119443005 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 238882365+0)%238882365 ≠ 101843%238882365 := by
  decide
theorem low_period_t1_n3_h1_a15 :
    Nat.powMod 2 (47424279170268000) 238882365 = 1 := by
  decide

theorem low_nohit_t1_n3_h1_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 477761085+0)%477761085 ≠ 109133%477761085 := by
  decide
theorem low_period_t1_n3_h1_a16 :
    Nat.powMod 2 (47424279170268000) 477761085 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 54675+0)%54675 ≠ 3211%54675 := by
  decide
theorem low_period_t1_n4_h0_a1 :
    Nat.powMod 2 (47424279170268000) 54675 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 98415+0)%98415 ≠ 25081%98415 := by
  decide
theorem low_period_t1_n4_h0_a2 :
    Nat.powMod 2 (47424279170268000) 98415 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 185895+0)%185895 ≠ 46951%185895 := by
  decide
theorem low_period_t1_n4_h0_a3 :
    Nat.powMod 2 (47424279170268000) 185895 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 360855+0)%360855 ≠ 68821%360855 := by
  decide
theorem low_period_t1_n4_h0_a4 :
    Nat.powMod 2 (47424279170268000) 360855 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 710775+0)%710775 ≠ 90691%710775 := by
  decide
theorem low_period_t1_n4_h0_a5 :
    Nat.powMod 2 (47424279170268000) 710775 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1410615+0)%1410615 ≠ 112561%1410615 := by
  decide
theorem low_period_t1_n4_h0_a6 :
    Nat.powMod 2 (47424279170268000) 1410615 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 2810295+0)%2810295 ≠ 134431%2810295 := by
  decide
theorem low_period_t1_n4_h0_a7 :
    Nat.powMod 2 (47424279170268000) 2810295 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 5609655+0)%5609655 ≠ 156301%5609655 := by
  decide
theorem low_period_t1_n4_h0_a8 :
    Nat.powMod 2 (47424279170268000) 5609655 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 11208375+0)%11208375 ≠ 178171%11208375 := by
  decide
theorem low_period_t1_n4_h0_a9 :
    Nat.powMod 2 (47424279170268000) 11208375 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 22405815+0)%22405815 ≠ 200041%22405815 := by
  decide
theorem low_period_t1_n4_h0_a10 :
    Nat.powMod 2 (47424279170268000) 22405815 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 44800695+0)%44800695 ≠ 221911%44800695 := by
  decide
theorem low_period_t1_n4_h0_a11 :
    Nat.powMod 2 (47424279170268000) 44800695 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 89590455+0)%89590455 ≠ 243781%89590455 := by
  decide
theorem low_period_t1_n4_h0_a12 :
    Nat.powMod 2 (47424279170268000) 89590455 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 179169975+0)%179169975 ≠ 265651%179169975 := by
  decide
theorem low_period_t1_n4_h0_a13 :
    Nat.powMod 2 (47424279170268000) 179169975 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 358329015+0)%358329015 ≠ 287521%358329015 := by
  decide
theorem low_period_t1_n4_h0_a14 :
    Nat.powMod 2 (47424279170268000) 358329015 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 716647095+0)%716647095 ≠ 309391%716647095 := by
  decide
theorem low_period_t1_n4_h0_a15 :
    Nat.powMod 2 (47424279170268000) 716647095 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1433283255+0)%1433283255 ≠ 331261%1433283255 := by
  decide
theorem low_period_t1_n4_h0_a16 :
    Nat.powMod 2 (47424279170268000) 1433283255 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 2866555575+0)%2866555575 ≠ 353131%2866555575 := by
  decide
theorem low_period_t1_n4_h0_a17 :
    Nat.powMod 2 (47424279170268000) 2866555575 = 1 := by
  decide

theorem low_nohit_t1_n4_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 5733100215+0)%5733100215 ≠ 375001%5733100215 := by
  decide
theorem low_period_t1_n4_h0_a18 :
    Nat.powMod 2 (47424279170268000) 5733100215 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 177147+0)%177147 ≠ 78593%177147 := by
  decide
theorem low_period_t1_n5_h0_a2 :
    Nat.powMod 2 (47424279170268000) 177147 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 334611+0)%334611 ≠ 117959%334611 := by
  decide
theorem low_period_t1_n5_h0_a3 :
    Nat.powMod 2 (47424279170268000) 334611 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 649539+0)%649539 ≠ 157325%649539 := by
  decide
theorem low_period_t1_n5_h0_a4 :
    Nat.powMod 2 (47424279170268000) 649539 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1279395+0)%1279395 ≠ 196691%1279395 := by
  decide
theorem low_period_t1_n5_h0_a5 :
    Nat.powMod 2 (47424279170268000) 1279395 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2539107+0)%2539107 ≠ 236057%2539107 := by
  decide
theorem low_period_t1_n5_h0_a6 :
    Nat.powMod 2 (47424279170268000) 2539107 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 5058531+0)%5058531 ≠ 275423%5058531 := by
  decide
theorem low_period_t1_n5_h0_a7 :
    Nat.powMod 2 (47424279170268000) 5058531 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 10097379+0)%10097379 ≠ 314789%10097379 := by
  decide
theorem low_period_t1_n5_h0_a8 :
    Nat.powMod 2 (47424279170268000) 10097379 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 20175075+0)%20175075 ≠ 354155%20175075 := by
  decide
theorem low_period_t1_n5_h0_a9 :
    Nat.powMod 2 (47424279170268000) 20175075 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 40330467+0)%40330467 ≠ 393521%40330467 := by
  decide
theorem low_period_t1_n5_h0_a10 :
    Nat.powMod 2 (47424279170268000) 40330467 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 80641251+0)%80641251 ≠ 432887%80641251 := by
  decide
theorem low_period_t1_n5_h0_a11 :
    Nat.powMod 2 (47424279170268000) 80641251 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 161262819+0)%161262819 ≠ 472253%161262819 := by
  decide
theorem low_period_t1_n5_h0_a12 :
    Nat.powMod 2 (47424279170268000) 161262819 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 322505955+0)%322505955 ≠ 511619%322505955 := by
  decide
theorem low_period_t1_n5_h0_a13 :
    Nat.powMod 2 (47424279170268000) 322505955 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 644992227+0)%644992227 ≠ 550985%644992227 := by
  decide
theorem low_period_t1_n5_h0_a14 :
    Nat.powMod 2 (47424279170268000) 644992227 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1289964771+0)%1289964771 ≠ 590351%1289964771 := by
  decide
theorem low_period_t1_n5_h0_a15 :
    Nat.powMod 2 (47424279170268000) 1289964771 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2579909859+0)%2579909859 ≠ 629717%2579909859 := by
  decide
theorem low_period_t1_n5_h0_a16 :
    Nat.powMod 2 (47424279170268000) 2579909859 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 5159800035+0)%5159800035 ≠ 669083%5159800035 := by
  decide
theorem low_period_t1_n5_h0_a17 :
    Nat.powMod 2 (47424279170268000) 5159800035 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 10319580387+0)%10319580387 ≠ 708449%10319580387 := by
  decide
theorem low_period_t1_n5_h0_a18 :
    Nat.powMod 2 (47424279170268000) 10319580387 = 1 := by
  decide

theorem low_nohit_t1_n5_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 20639141091+0)%20639141091 ≠ 747815%20639141091 := by
  decide
theorem low_period_t1_n5_h0_a19 :
    Nat.powMod 2 (47424279170268000) 20639141091 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 2025+0)%2025 ≠ 1309%2025 := by
  decide
theorem low_period_t1_n6_h0_a1 :
    Nat.powMod 2 (47424279170268000) 2025 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 3645+0)%3645 ≠ 2119%3645 := by
  decide
theorem low_period_t1_n6_h0_a2 :
    Nat.powMod 2 (47424279170268000) 3645 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 6885+0)%6885 ≠ 2929%6885 := by
  decide
theorem low_period_t1_n6_h0_a3 :
    Nat.powMod 2 (47424279170268000) 6885 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 13365+0)%13365 ≠ 3739%13365 := by
  decide
theorem low_period_t1_n6_h0_a4 :
    Nat.powMod 2 (47424279170268000) 13365 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 26325+0)%26325 ≠ 4549%26325 := by
  decide
theorem low_period_t1_n6_h0_a5 :
    Nat.powMod 2 (47424279170268000) 26325 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 52245+0)%52245 ≠ 5359%52245 := by
  decide
theorem low_period_t1_n6_h0_a6 :
    Nat.powMod 2 (47424279170268000) 52245 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 104085+0)%104085 ≠ 6169%104085 := by
  decide
theorem low_period_t1_n6_h0_a7 :
    Nat.powMod 2 (47424279170268000) 104085 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 207765+0)%207765 ≠ 6979%207765 := by
  decide
theorem low_period_t1_n6_h0_a8 :
    Nat.powMod 2 (47424279170268000) 207765 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 415125+0)%415125 ≠ 7789%415125 := by
  decide
theorem low_period_t1_n6_h0_a9 :
    Nat.powMod 2 (47424279170268000) 415125 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 829845+0)%829845 ≠ 8599%829845 := by
  decide
theorem low_period_t1_n6_h0_a10 :
    Nat.powMod 2 (47424279170268000) 829845 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 1659285+0)%1659285 ≠ 9409%1659285 := by
  decide
theorem low_period_t1_n6_h0_a11 :
    Nat.powMod 2 (47424279170268000) 1659285 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 3318165+0)%3318165 ≠ 10219%3318165 := by
  decide
theorem low_period_t1_n6_h0_a12 :
    Nat.powMod 2 (47424279170268000) 3318165 = 1 := by
  decide

theorem low_nohit_t1_n6_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 6635925+0)%6635925 ≠ 11029%6635925 := by
  decide
theorem low_period_t1_n6_h0_a13 :
    Nat.powMod 2 (47424279170268000) 6635925 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 6075+0)%6075 ≠ 2213%6075 := by
  decide
theorem low_period_t1_n6_h1_a1 :
    Nat.powMod 2 (47424279170268000) 6075 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 10935+0)%10935 ≠ 4643%10935 := by
  decide
theorem low_period_t1_n6_h1_a2 :
    Nat.powMod 2 (47424279170268000) 10935 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 20655+0)%20655 ≠ 7073%20655 := by
  decide
theorem low_period_t1_n6_h1_a3 :
    Nat.powMod 2 (47424279170268000) 20655 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 40095+0)%40095 ≠ 9503%40095 := by
  decide
theorem low_period_t1_n6_h1_a4 :
    Nat.powMod 2 (47424279170268000) 40095 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 78975+0)%78975 ≠ 11933%78975 := by
  decide
theorem low_period_t1_n6_h1_a5 :
    Nat.powMod 2 (47424279170268000) 78975 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 156735+0)%156735 ≠ 14363%156735 := by
  decide
theorem low_period_t1_n6_h1_a6 :
    Nat.powMod 2 (47424279170268000) 156735 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 312255+0)%312255 ≠ 16793%312255 := by
  decide
theorem low_period_t1_n6_h1_a7 :
    Nat.powMod 2 (47424279170268000) 312255 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 623295+0)%623295 ≠ 19223%623295 := by
  decide
theorem low_period_t1_n6_h1_a8 :
    Nat.powMod 2 (47424279170268000) 623295 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 1245375+0)%1245375 ≠ 21653%1245375 := by
  decide
theorem low_period_t1_n6_h1_a9 :
    Nat.powMod 2 (47424279170268000) 1245375 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 2489535+0)%2489535 ≠ 24083%2489535 := by
  decide
theorem low_period_t1_n6_h1_a10 :
    Nat.powMod 2 (47424279170268000) 2489535 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 4977855+0)%4977855 ≠ 26513%4977855 := by
  decide
theorem low_period_t1_n6_h1_a11 :
    Nat.powMod 2 (47424279170268000) 4977855 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 9954495+0)%9954495 ≠ 28943%9954495 := by
  decide
theorem low_period_t1_n6_h1_a12 :
    Nat.powMod 2 (47424279170268000) 9954495 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 19907775+0)%19907775 ≠ 31373%19907775 := by
  decide
theorem low_period_t1_n6_h1_a13 :
    Nat.powMod 2 (47424279170268000) 19907775 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 39814335+0)%39814335 ≠ 33803%39814335 := by
  decide
theorem low_period_t1_n6_h1_a14 :
    Nat.powMod 2 (47424279170268000) 39814335 = 1 := by
  decide

theorem low_nohit_t1_n6_h1_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 79627455+0)%79627455 ≠ 36233%79627455 := by
  decide
theorem low_period_t1_n6_h1_a15 :
    Nat.powMod 2 (47424279170268000) 79627455 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 18225+0)%18225 ≠ 3211%18225 := by
  decide
theorem low_period_t1_n6_h2_a1 :
    Nat.powMod 2 (47424279170268000) 18225 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 32805+0)%32805 ≠ 10501%32805 := by
  decide
theorem low_period_t1_n6_h2_a2 :
    Nat.powMod 2 (47424279170268000) 32805 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 61965+0)%61965 ≠ 17791%61965 := by
  decide
theorem low_period_t1_n6_h2_a3 :
    Nat.powMod 2 (47424279170268000) 61965 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 120285+0)%120285 ≠ 25081%120285 := by
  decide
theorem low_period_t1_n6_h2_a4 :
    Nat.powMod 2 (47424279170268000) 120285 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 236925+0)%236925 ≠ 32371%236925 := by
  decide
theorem low_period_t1_n6_h2_a5 :
    Nat.powMod 2 (47424279170268000) 236925 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 470205+0)%470205 ≠ 39661%470205 := by
  decide
theorem low_period_t1_n6_h2_a6 :
    Nat.powMod 2 (47424279170268000) 470205 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 936765+0)%936765 ≠ 46951%936765 := by
  decide
theorem low_period_t1_n6_h2_a7 :
    Nat.powMod 2 (47424279170268000) 936765 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1869885+0)%1869885 ≠ 54241%1869885 := by
  decide
theorem low_period_t1_n6_h2_a8 :
    Nat.powMod 2 (47424279170268000) 1869885 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 3736125+0)%3736125 ≠ 61531%3736125 := by
  decide
theorem low_period_t1_n6_h2_a9 :
    Nat.powMod 2 (47424279170268000) 3736125 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 7468605+0)%7468605 ≠ 68821%7468605 := by
  decide
theorem low_period_t1_n6_h2_a10 :
    Nat.powMod 2 (47424279170268000) 7468605 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 14933565+0)%14933565 ≠ 76111%14933565 := by
  decide
theorem low_period_t1_n6_h2_a11 :
    Nat.powMod 2 (47424279170268000) 14933565 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 29863485+0)%29863485 ≠ 83401%29863485 := by
  decide
theorem low_period_t1_n6_h2_a12 :
    Nat.powMod 2 (47424279170268000) 29863485 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 59723325+0)%59723325 ≠ 90691%59723325 := by
  decide
theorem low_period_t1_n6_h2_a13 :
    Nat.powMod 2 (47424279170268000) 59723325 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 119443005+0)%119443005 ≠ 97981%119443005 := by
  decide
theorem low_period_t1_n6_h2_a14 :
    Nat.powMod 2 (47424279170268000) 119443005 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 238882365+0)%238882365 ≠ 105271%238882365 := by
  decide
theorem low_period_t1_n6_h2_a15 :
    Nat.powMod 2 (47424279170268000) 238882365 = 1 := by
  decide

theorem low_nohit_t1_n6_h2_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 477761085+0)%477761085 ≠ 112561%477761085 := by
  decide
theorem low_period_t1_n6_h2_a16 :
    Nat.powMod 2 (47424279170268000) 477761085 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 3375+0)%3375 ≠ 1039%3375 := by
  decide
theorem low_period_t1_n7_h0_a1 :
    Nat.powMod 2 (47424279170268000) 3375 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 6075+0)%6075 ≠ 2389%6075 := by
  decide
theorem low_period_t1_n7_h0_a2 :
    Nat.powMod 2 (47424279170268000) 6075 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 11475+0)%11475 ≠ 3739%11475 := by
  decide
theorem low_period_t1_n7_h0_a3 :
    Nat.powMod 2 (47424279170268000) 11475 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 22275+0)%22275 ≠ 5089%22275 := by
  decide
theorem low_period_t1_n7_h0_a4 :
    Nat.powMod 2 (47424279170268000) 22275 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 43875+0)%43875 ≠ 6439%43875 := by
  decide
theorem low_period_t1_n7_h0_a5 :
    Nat.powMod 2 (47424279170268000) 43875 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 87075+0)%87075 ≠ 7789%87075 := by
  decide
theorem low_period_t1_n7_h0_a6 :
    Nat.powMod 2 (47424279170268000) 87075 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 173475+0)%173475 ≠ 9139%173475 := by
  decide
theorem low_period_t1_n7_h0_a7 :
    Nat.powMod 2 (47424279170268000) 173475 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 346275+0)%346275 ≠ 10489%346275 := by
  decide
theorem low_period_t1_n7_h0_a8 :
    Nat.powMod 2 (47424279170268000) 346275 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 691875+0)%691875 ≠ 11839%691875 := by
  decide
theorem low_period_t1_n7_h0_a9 :
    Nat.powMod 2 (47424279170268000) 691875 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 1383075+0)%1383075 ≠ 13189%1383075 := by
  decide
theorem low_period_t1_n7_h0_a10 :
    Nat.powMod 2 (47424279170268000) 1383075 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 2765475+0)%2765475 ≠ 14539%2765475 := by
  decide
theorem low_period_t1_n7_h0_a11 :
    Nat.powMod 2 (47424279170268000) 2765475 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 5530275+0)%5530275 ≠ 15889%5530275 := by
  decide
theorem low_period_t1_n7_h0_a12 :
    Nat.powMod 2 (47424279170268000) 5530275 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 11059875+0)%11059875 ≠ 17239%11059875 := by
  decide
theorem low_period_t1_n7_h0_a13 :
    Nat.powMod 2 (47424279170268000) 11059875 = 1 := by
  decide

theorem low_nohit_t1_n7_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+8) 22119075+0)%22119075 ≠ 18589%22119075 := by
  decide
theorem low_period_t1_n7_h0_a14 :
    Nat.powMod 2 (47424279170268000) 22119075 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 10125+0)%10125 ≠ 1403%10125 := by
  decide
theorem low_period_t1_n7_h1_a1 :
    Nat.powMod 2 (47424279170268000) 10125 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 18225+0)%18225 ≠ 5453%18225 := by
  decide
theorem low_period_t1_n7_h1_a2 :
    Nat.powMod 2 (47424279170268000) 18225 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 34425+0)%34425 ≠ 9503%34425 := by
  decide
theorem low_period_t1_n7_h1_a3 :
    Nat.powMod 2 (47424279170268000) 34425 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 66825+0)%66825 ≠ 13553%66825 := by
  decide
theorem low_period_t1_n7_h1_a4 :
    Nat.powMod 2 (47424279170268000) 66825 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 131625+0)%131625 ≠ 17603%131625 := by
  decide
theorem low_period_t1_n7_h1_a5 :
    Nat.powMod 2 (47424279170268000) 131625 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 261225+0)%261225 ≠ 21653%261225 := by
  decide
theorem low_period_t1_n7_h1_a6 :
    Nat.powMod 2 (47424279170268000) 261225 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 520425+0)%520425 ≠ 25703%520425 := by
  decide
theorem low_period_t1_n7_h1_a7 :
    Nat.powMod 2 (47424279170268000) 520425 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 1038825+0)%1038825 ≠ 29753%1038825 := by
  decide
theorem low_period_t1_n7_h1_a8 :
    Nat.powMod 2 (47424279170268000) 1038825 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 2075625+0)%2075625 ≠ 33803%2075625 := by
  decide
theorem low_period_t1_n7_h1_a9 :
    Nat.powMod 2 (47424279170268000) 2075625 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 4149225+0)%4149225 ≠ 37853%4149225 := by
  decide
theorem low_period_t1_n7_h1_a10 :
    Nat.powMod 2 (47424279170268000) 4149225 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 8296425+0)%8296425 ≠ 41903%8296425 := by
  decide
theorem low_period_t1_n7_h1_a11 :
    Nat.powMod 2 (47424279170268000) 8296425 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 16590825+0)%16590825 ≠ 45953%16590825 := by
  decide
theorem low_period_t1_n7_h1_a12 :
    Nat.powMod 2 (47424279170268000) 16590825 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 33179625+0)%33179625 ≠ 50003%33179625 := by
  decide
theorem low_period_t1_n7_h1_a13 :
    Nat.powMod 2 (47424279170268000) 33179625 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 66357225+0)%66357225 ≠ 54053%66357225 := by
  decide
theorem low_period_t1_n7_h1_a14 :
    Nat.powMod 2 (47424279170268000) 66357225 = 1 := by
  decide

theorem low_nohit_t1_n7_h1_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+9) 132712425+0)%132712425 ≠ 58103%132712425 := by
  decide
theorem low_period_t1_n7_h1_a15 :
    Nat.powMod 2 (47424279170268000) 132712425 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 30375+0)%30375 ≠ 781%30375 := by
  decide
theorem low_period_t1_n7_h2_a1 :
    Nat.powMod 2 (47424279170268000) 30375 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 54675+0)%54675 ≠ 12931%54675 := by
  decide
theorem low_period_t1_n7_h2_a2 :
    Nat.powMod 2 (47424279170268000) 54675 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 103275+0)%103275 ≠ 25081%103275 := by
  decide
theorem low_period_t1_n7_h2_a3 :
    Nat.powMod 2 (47424279170268000) 103275 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 200475+0)%200475 ≠ 37231%200475 := by
  decide
theorem low_period_t1_n7_h2_a4 :
    Nat.powMod 2 (47424279170268000) 200475 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 394875+0)%394875 ≠ 49381%394875 := by
  decide
theorem low_period_t1_n7_h2_a5 :
    Nat.powMod 2 (47424279170268000) 394875 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 783675+0)%783675 ≠ 61531%783675 := by
  decide
theorem low_period_t1_n7_h2_a6 :
    Nat.powMod 2 (47424279170268000) 783675 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1561275+0)%1561275 ≠ 73681%1561275 := by
  decide
theorem low_period_t1_n7_h2_a7 :
    Nat.powMod 2 (47424279170268000) 1561275 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 3116475+0)%3116475 ≠ 85831%3116475 := by
  decide
theorem low_period_t1_n7_h2_a8 :
    Nat.powMod 2 (47424279170268000) 3116475 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 6226875+0)%6226875 ≠ 97981%6226875 := by
  decide
theorem low_period_t1_n7_h2_a9 :
    Nat.powMod 2 (47424279170268000) 6226875 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 12447675+0)%12447675 ≠ 110131%12447675 := by
  decide
theorem low_period_t1_n7_h2_a10 :
    Nat.powMod 2 (47424279170268000) 12447675 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 24889275+0)%24889275 ≠ 122281%24889275 := by
  decide
theorem low_period_t1_n7_h2_a11 :
    Nat.powMod 2 (47424279170268000) 24889275 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 49772475+0)%49772475 ≠ 134431%49772475 := by
  decide
theorem low_period_t1_n7_h2_a12 :
    Nat.powMod 2 (47424279170268000) 49772475 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 99538875+0)%99538875 ≠ 146581%99538875 := by
  decide
theorem low_period_t1_n7_h2_a13 :
    Nat.powMod 2 (47424279170268000) 99538875 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 199071675+0)%199071675 ≠ 158731%199071675 := by
  decide
theorem low_period_t1_n7_h2_a14 :
    Nat.powMod 2 (47424279170268000) 199071675 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 398137275+0)%398137275 ≠ 170881%398137275 := by
  decide
theorem low_period_t1_n7_h2_a15 :
    Nat.powMod 2 (47424279170268000) 398137275 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 796268475+0)%796268475 ≠ 183031%796268475 := by
  decide
theorem low_period_t1_n7_h2_a16 :
    Nat.powMod 2 (47424279170268000) 796268475 = 1 := by
  decide

theorem low_nohit_t1_n7_h2_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1592530875+0)%1592530875 ≠ 195181%1592530875 := by
  decide
theorem low_period_t1_n7_h2_a17 :
    Nat.powMod 2 (47424279170268000) 1592530875 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 91125+4513)%91125 ≠ 0%91125 := by
  decide
theorem low_period_t1_n7_h3_a1 :
    Nat.powMod 2 (47424279170268000) 91125 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 164025+0)%164025 ≠ 31937%164025 := by
  decide
theorem low_period_t1_n7_h3_a2 :
    Nat.powMod 2 (47424279170268000) 164025 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 309825+0)%309825 ≠ 68387%309825 := by
  decide
theorem low_period_t1_n7_h3_a3 :
    Nat.powMod 2 (47424279170268000) 309825 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 601425+0)%601425 ≠ 104837%601425 := by
  decide
theorem low_period_t1_n7_h3_a4 :
    Nat.powMod 2 (47424279170268000) 601425 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1184625+0)%1184625 ≠ 141287%1184625 := by
  decide
theorem low_period_t1_n7_h3_a5 :
    Nat.powMod 2 (47424279170268000) 1184625 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2351025+0)%2351025 ≠ 177737%2351025 := by
  decide
theorem low_period_t1_n7_h3_a6 :
    Nat.powMod 2 (47424279170268000) 2351025 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 4683825+0)%4683825 ≠ 214187%4683825 := by
  decide
theorem low_period_t1_n7_h3_a7 :
    Nat.powMod 2 (47424279170268000) 4683825 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 9349425+0)%9349425 ≠ 250637%9349425 := by
  decide
theorem low_period_t1_n7_h3_a8 :
    Nat.powMod 2 (47424279170268000) 9349425 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 18680625+0)%18680625 ≠ 287087%18680625 := by
  decide
theorem low_period_t1_n7_h3_a9 :
    Nat.powMod 2 (47424279170268000) 18680625 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 37343025+0)%37343025 ≠ 323537%37343025 := by
  decide
theorem low_period_t1_n7_h3_a10 :
    Nat.powMod 2 (47424279170268000) 37343025 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 74667825+0)%74667825 ≠ 359987%74667825 := by
  decide
theorem low_period_t1_n7_h3_a11 :
    Nat.powMod 2 (47424279170268000) 74667825 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 149317425+0)%149317425 ≠ 396437%149317425 := by
  decide
theorem low_period_t1_n7_h3_a12 :
    Nat.powMod 2 (47424279170268000) 149317425 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 298616625+0)%298616625 ≠ 432887%298616625 := by
  decide
theorem low_period_t1_n7_h3_a13 :
    Nat.powMod 2 (47424279170268000) 298616625 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 597215025+0)%597215025 ≠ 469337%597215025 := by
  decide
theorem low_period_t1_n7_h3_a14 :
    Nat.powMod 2 (47424279170268000) 597215025 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1194411825+0)%1194411825 ≠ 505787%1194411825 := by
  decide
theorem low_period_t1_n7_h3_a15 :
    Nat.powMod 2 (47424279170268000) 1194411825 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2388805425+0)%2388805425 ≠ 542237%2388805425 := by
  decide
theorem low_period_t1_n7_h3_a16 :
    Nat.powMod 2 (47424279170268000) 2388805425 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 4777592625+0)%4777592625 ≠ 578687%4777592625 := by
  decide
theorem low_period_t1_n7_h3_a17 :
    Nat.powMod 2 (47424279170268000) 4777592625 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 9555167025+0)%9555167025 ≠ 615137%9555167025 := by
  decide
theorem low_period_t1_n7_h3_a18 :
    Nat.powMod 2 (47424279170268000) 9555167025 = 1 := by
  decide

theorem low_nohit_t1_n7_h3_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 19110315825+0)%19110315825 ≠ 651587%19110315825 := by
  decide
theorem low_period_t1_n7_h3_a19 :
    Nat.powMod 2 (47424279170268000) 19110315825 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 18225+0)%18225 ≠ 10501%18225 := by
  decide
theorem low_period_t1_n8_h0_a1 :
    Nat.powMod 2 (47424279170268000) 18225 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 32805+0)%32805 ≠ 17791%32805 := by
  decide
theorem low_period_t1_n8_h0_a2 :
    Nat.powMod 2 (47424279170268000) 32805 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 61965+0)%61965 ≠ 25081%61965 := by
  decide
theorem low_period_t1_n8_h0_a3 :
    Nat.powMod 2 (47424279170268000) 61965 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 120285+0)%120285 ≠ 32371%120285 := by
  decide
theorem low_period_t1_n8_h0_a4 :
    Nat.powMod 2 (47424279170268000) 120285 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 236925+0)%236925 ≠ 39661%236925 := by
  decide
theorem low_period_t1_n8_h0_a5 :
    Nat.powMod 2 (47424279170268000) 236925 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 470205+0)%470205 ≠ 46951%470205 := by
  decide
theorem low_period_t1_n8_h0_a6 :
    Nat.powMod 2 (47424279170268000) 470205 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 936765+0)%936765 ≠ 54241%936765 := by
  decide
theorem low_period_t1_n8_h0_a7 :
    Nat.powMod 2 (47424279170268000) 936765 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 1869885+0)%1869885 ≠ 61531%1869885 := by
  decide
theorem low_period_t1_n8_h0_a8 :
    Nat.powMod 2 (47424279170268000) 1869885 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 3736125+0)%3736125 ≠ 68821%3736125 := by
  decide
theorem low_period_t1_n8_h0_a9 :
    Nat.powMod 2 (47424279170268000) 3736125 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 7468605+0)%7468605 ≠ 76111%7468605 := by
  decide
theorem low_period_t1_n8_h0_a10 :
    Nat.powMod 2 (47424279170268000) 7468605 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 14933565+0)%14933565 ≠ 83401%14933565 := by
  decide
theorem low_period_t1_n8_h0_a11 :
    Nat.powMod 2 (47424279170268000) 14933565 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 29863485+0)%29863485 ≠ 90691%29863485 := by
  decide
theorem low_period_t1_n8_h0_a12 :
    Nat.powMod 2 (47424279170268000) 29863485 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 59723325+0)%59723325 ≠ 97981%59723325 := by
  decide
theorem low_period_t1_n8_h0_a13 :
    Nat.powMod 2 (47424279170268000) 59723325 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 119443005+0)%119443005 ≠ 105271%119443005 := by
  decide
theorem low_period_t1_n8_h0_a14 :
    Nat.powMod 2 (47424279170268000) 119443005 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 238882365+0)%238882365 ≠ 112561%238882365 := by
  decide
theorem low_period_t1_n8_h0_a15 :
    Nat.powMod 2 (47424279170268000) 238882365 = 1 := by
  decide

theorem low_nohit_t1_n8_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+10) 477761085+0)%477761085 ≠ 119851%477761085 := by
  decide
theorem low_period_t1_n8_h0_a16 :
    Nat.powMod 2 (47424279170268000) 477761085 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 54675+0)%54675 ≠ 17357%54675 := by
  decide
theorem low_period_t1_n8_h1_a1 :
    Nat.powMod 2 (47424279170268000) 54675 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 185895+0)%185895 ≠ 61097%185895 := by
  decide
theorem low_period_t1_n8_h1_a3 :
    Nat.powMod 2 (47424279170268000) 185895 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 360855+0)%360855 ≠ 82967%360855 := by
  decide
theorem low_period_t1_n8_h1_a4 :
    Nat.powMod 2 (47424279170268000) 360855 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 710775+0)%710775 ≠ 104837%710775 := by
  decide
theorem low_period_t1_n8_h1_a5 :
    Nat.powMod 2 (47424279170268000) 710775 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1410615+0)%1410615 ≠ 126707%1410615 := by
  decide
theorem low_period_t1_n8_h1_a6 :
    Nat.powMod 2 (47424279170268000) 1410615 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2810295+0)%2810295 ≠ 148577%2810295 := by
  decide
theorem low_period_t1_n8_h1_a7 :
    Nat.powMod 2 (47424279170268000) 2810295 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 5609655+0)%5609655 ≠ 170447%5609655 := by
  decide
theorem low_period_t1_n8_h1_a8 :
    Nat.powMod 2 (47424279170268000) 5609655 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 11208375+0)%11208375 ≠ 192317%11208375 := by
  decide
theorem low_period_t1_n8_h1_a9 :
    Nat.powMod 2 (47424279170268000) 11208375 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 22405815+0)%22405815 ≠ 214187%22405815 := by
  decide
theorem low_period_t1_n8_h1_a10 :
    Nat.powMod 2 (47424279170268000) 22405815 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 44800695+0)%44800695 ≠ 236057%44800695 := by
  decide
theorem low_period_t1_n8_h1_a11 :
    Nat.powMod 2 (47424279170268000) 44800695 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 89590455+0)%89590455 ≠ 257927%89590455 := by
  decide
theorem low_period_t1_n8_h1_a12 :
    Nat.powMod 2 (47424279170268000) 89590455 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 179169975+0)%179169975 ≠ 279797%179169975 := by
  decide
theorem low_period_t1_n8_h1_a13 :
    Nat.powMod 2 (47424279170268000) 179169975 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 358329015+0)%358329015 ≠ 301667%358329015 := by
  decide
theorem low_period_t1_n8_h1_a14 :
    Nat.powMod 2 (47424279170268000) 358329015 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 716647095+0)%716647095 ≠ 323537%716647095 := by
  decide
theorem low_period_t1_n8_h1_a15 :
    Nat.powMod 2 (47424279170268000) 716647095 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 1433283255+0)%1433283255 ≠ 345407%1433283255 := by
  decide
theorem low_period_t1_n8_h1_a16 :
    Nat.powMod 2 (47424279170268000) 1433283255 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 2866555575+0)%2866555575 ≠ 367277%2866555575 := by
  decide
theorem low_period_t1_n8_h1_a17 :
    Nat.powMod 2 (47424279170268000) 2866555575 = 1 := by
  decide

theorem low_nohit_t1_n8_h1_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+11) 5733100215+0)%5733100215 ≠ 389147%5733100215 := by
  decide
theorem low_period_t1_n8_h1_a18 :
    Nat.powMod 2 (47424279170268000) 5733100215 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 185895+0)%185895 ≠ 147709%185895 := by
  decide
theorem low_period_t1_n9_h0_a2 :
    Nat.powMod 2 (47424279170268000) 185895 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 351135+0)%351135 ≠ 189019%351135 := by
  decide
theorem low_period_t1_n9_h0_a3 :
    Nat.powMod 2 (47424279170268000) 351135 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 681615+0)%681615 ≠ 230329%681615 := by
  decide
theorem low_period_t1_n9_h0_a4 :
    Nat.powMod 2 (47424279170268000) 681615 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 1342575+0)%1342575 ≠ 271639%1342575 := by
  decide
theorem low_period_t1_n9_h0_a5 :
    Nat.powMod 2 (47424279170268000) 1342575 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 2664495+0)%2664495 ≠ 312949%2664495 := by
  decide
theorem low_period_t1_n9_h0_a6 :
    Nat.powMod 2 (47424279170268000) 2664495 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 5308335+0)%5308335 ≠ 354259%5308335 := by
  decide
theorem low_period_t1_n9_h0_a7 :
    Nat.powMod 2 (47424279170268000) 5308335 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 10596015+0)%10596015 ≠ 395569%10596015 := by
  decide
theorem low_period_t1_n9_h0_a8 :
    Nat.powMod 2 (47424279170268000) 10596015 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 21171375+0)%21171375 ≠ 436879%21171375 := by
  decide
theorem low_period_t1_n9_h0_a9 :
    Nat.powMod 2 (47424279170268000) 21171375 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 42322095+0)%42322095 ≠ 478189%42322095 := by
  decide
theorem low_period_t1_n9_h0_a10 :
    Nat.powMod 2 (47424279170268000) 42322095 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 84623535+0)%84623535 ≠ 519499%84623535 := by
  decide
theorem low_period_t1_n9_h0_a11 :
    Nat.powMod 2 (47424279170268000) 84623535 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 169226415+0)%169226415 ≠ 560809%169226415 := by
  decide
theorem low_period_t1_n9_h0_a12 :
    Nat.powMod 2 (47424279170268000) 169226415 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 338432175+0)%338432175 ≠ 602119%338432175 := by
  decide
theorem low_period_t1_n9_h0_a13 :
    Nat.powMod 2 (47424279170268000) 338432175 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 676843695+0)%676843695 ≠ 643429%676843695 := by
  decide
theorem low_period_t1_n9_h0_a14 :
    Nat.powMod 2 (47424279170268000) 676843695 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 1353666735+0)%1353666735 ≠ 684739%1353666735 := by
  decide
theorem low_period_t1_n9_h0_a15 :
    Nat.powMod 2 (47424279170268000) 1353666735 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 2707312815+0)%2707312815 ≠ 726049%2707312815 := by
  decide
theorem low_period_t1_n9_h0_a16 :
    Nat.powMod 2 (47424279170268000) 2707312815 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 5414604975+0)%5414604975 ≠ 767359%5414604975 := by
  decide
theorem low_period_t1_n9_h0_a17 :
    Nat.powMod 2 (47424279170268000) 5414604975 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 10829189295+0)%10829189295 ≠ 808669%10829189295 := by
  decide
theorem low_period_t1_n9_h0_a18 :
    Nat.powMod 2 (47424279170268000) 10829189295 = 1 := by
  decide

theorem low_nohit_t1_n9_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+12) 21658357935+0)%21658357935 ≠ 849979%21658357935 := by
  decide
theorem low_period_t1_n9_h0_a19 :
    Nat.powMod 2 (47424279170268000) 21658357935 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 885735+0)%885735 ≠ 452153%885735 := by
  decide
theorem low_period_t1_n10_h0_a2 :
    Nat.powMod 2 (47424279170268000) 885735 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 1673055+0)%1673055 ≠ 648983%1673055 := by
  decide
theorem low_period_t1_n10_h0_a3 :
    Nat.powMod 2 (47424279170268000) 1673055 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 3247695+0)%3247695 ≠ 845813%3247695 := by
  decide
theorem low_period_t1_n10_h0_a4 :
    Nat.powMod 2 (47424279170268000) 3247695 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 6396975+0)%6396975 ≠ 1042643%6396975 := by
  decide
theorem low_period_t1_n10_h0_a5 :
    Nat.powMod 2 (47424279170268000) 6396975 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 12695535+0)%12695535 ≠ 1239473%12695535 := by
  decide
theorem low_period_t1_n10_h0_a6 :
    Nat.powMod 2 (47424279170268000) 12695535 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 25292655+0)%25292655 ≠ 1436303%25292655 := by
  decide
theorem low_period_t1_n10_h0_a7 :
    Nat.powMod 2 (47424279170268000) 25292655 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 50486895+0)%50486895 ≠ 1633133%50486895 := by
  decide
theorem low_period_t1_n10_h0_a8 :
    Nat.powMod 2 (47424279170268000) 50486895 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 100875375+0)%100875375 ≠ 1829963%100875375 := by
  decide
theorem low_period_t1_n10_h0_a9 :
    Nat.powMod 2 (47424279170268000) 100875375 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 201652335+0)%201652335 ≠ 2026793%201652335 := by
  decide
theorem low_period_t1_n10_h0_a10 :
    Nat.powMod 2 (47424279170268000) 201652335 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 403206255+0)%403206255 ≠ 2223623%403206255 := by
  decide
theorem low_period_t1_n10_h0_a11 :
    Nat.powMod 2 (47424279170268000) 403206255 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 806314095+0)%806314095 ≠ 2420453%806314095 := by
  decide
theorem low_period_t1_n10_h0_a12 :
    Nat.powMod 2 (47424279170268000) 806314095 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 1612529775+0)%1612529775 ≠ 2617283%1612529775 := by
  decide
theorem low_period_t1_n10_h0_a13 :
    Nat.powMod 2 (47424279170268000) 1612529775 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 3224961135+0)%3224961135 ≠ 2814113%3224961135 := by
  decide
theorem low_period_t1_n10_h0_a14 :
    Nat.powMod 2 (47424279170268000) 3224961135 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 6449823855+0)%6449823855 ≠ 3010943%6449823855 := by
  decide
theorem low_period_t1_n10_h0_a15 :
    Nat.powMod 2 (47424279170268000) 6449823855 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 12899549295+0)%12899549295 ≠ 3207773%12899549295 := by
  decide
theorem low_period_t1_n10_h0_a16 :
    Nat.powMod 2 (47424279170268000) 12899549295 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 25799000175+0)%25799000175 ≠ 3404603%25799000175 := by
  decide
theorem low_period_t1_n10_h0_a17 :
    Nat.powMod 2 (47424279170268000) 25799000175 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 51597901935+0)%51597901935 ≠ 3601433%51597901935 := by
  decide
theorem low_period_t1_n10_h0_a18 :
    Nat.powMod 2 (47424279170268000) 51597901935 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 103195705455+0)%103195705455 ≠ 3798263%103195705455 := by
  decide
theorem low_period_t1_n10_h0_a19 :
    Nat.powMod 2 (47424279170268000) 103195705455 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a20 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 206391312495+0)%206391312495 ≠ 3995093%206391312495 := by
  decide
theorem low_period_t1_n10_h0_a20 :
    Nat.powMod 2 (47424279170268000) 206391312495 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a21 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 412782526575+0)%412782526575 ≠ 4191923%412782526575 := by
  decide
theorem low_period_t1_n10_h0_a21 :
    Nat.powMod 2 (47424279170268000) 412782526575 = 1 := by
  decide

theorem low_nohit_t1_n10_h0_a22 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+13) 825564954735+0)%825564954735 ≠ 4388753%825564954735 := by
  decide
theorem low_period_t1_n10_h0_a22 :
    Nat.powMod 2 (47424279170268000) 825564954735 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 492075+0)%492075 ≠ 412231%492075 := by
  decide
theorem low_period_t1_n11_h0_a1 :
    Nat.powMod 2 (47424279170268000) 492075 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 1673055+0)%1673055 ≠ 805891%1673055 := by
  decide
theorem low_period_t1_n11_h0_a3 :
    Nat.powMod 2 (47424279170268000) 1673055 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 3247695+0)%3247695 ≠ 1002721%3247695 := by
  decide
theorem low_period_t1_n11_h0_a4 :
    Nat.powMod 2 (47424279170268000) 3247695 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 6396975+0)%6396975 ≠ 1199551%6396975 := by
  decide
theorem low_period_t1_n11_h0_a5 :
    Nat.powMod 2 (47424279170268000) 6396975 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 12695535+0)%12695535 ≠ 1396381%12695535 := by
  decide
theorem low_period_t1_n11_h0_a6 :
    Nat.powMod 2 (47424279170268000) 12695535 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 25292655+0)%25292655 ≠ 1593211%25292655 := by
  decide
theorem low_period_t1_n11_h0_a7 :
    Nat.powMod 2 (47424279170268000) 25292655 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 50486895+0)%50486895 ≠ 1790041%50486895 := by
  decide
theorem low_period_t1_n11_h0_a8 :
    Nat.powMod 2 (47424279170268000) 50486895 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 100875375+0)%100875375 ≠ 1986871%100875375 := by
  decide
theorem low_period_t1_n11_h0_a9 :
    Nat.powMod 2 (47424279170268000) 100875375 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 201652335+0)%201652335 ≠ 2183701%201652335 := by
  decide
theorem low_period_t1_n11_h0_a10 :
    Nat.powMod 2 (47424279170268000) 201652335 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 403206255+0)%403206255 ≠ 2380531%403206255 := by
  decide
theorem low_period_t1_n11_h0_a11 :
    Nat.powMod 2 (47424279170268000) 403206255 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 806314095+0)%806314095 ≠ 2577361%806314095 := by
  decide
theorem low_period_t1_n11_h0_a12 :
    Nat.powMod 2 (47424279170268000) 806314095 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 1612529775+0)%1612529775 ≠ 2774191%1612529775 := by
  decide
theorem low_period_t1_n11_h0_a13 :
    Nat.powMod 2 (47424279170268000) 1612529775 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 3224961135+0)%3224961135 ≠ 2971021%3224961135 := by
  decide
theorem low_period_t1_n11_h0_a14 :
    Nat.powMod 2 (47424279170268000) 3224961135 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 6449823855+0)%6449823855 ≠ 3167851%6449823855 := by
  decide
theorem low_period_t1_n11_h0_a15 :
    Nat.powMod 2 (47424279170268000) 6449823855 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 12899549295+0)%12899549295 ≠ 3364681%12899549295 := by
  decide
theorem low_period_t1_n11_h0_a16 :
    Nat.powMod 2 (47424279170268000) 12899549295 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 25799000175+0)%25799000175 ≠ 3561511%25799000175 := by
  decide
theorem low_period_t1_n11_h0_a17 :
    Nat.powMod 2 (47424279170268000) 25799000175 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 51597901935+0)%51597901935 ≠ 3758341%51597901935 := by
  decide
theorem low_period_t1_n11_h0_a18 :
    Nat.powMod 2 (47424279170268000) 51597901935 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 103195705455+0)%103195705455 ≠ 3955171%103195705455 := by
  decide
theorem low_period_t1_n11_h0_a19 :
    Nat.powMod 2 (47424279170268000) 103195705455 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a20 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 206391312495+0)%206391312495 ≠ 4152001%206391312495 := by
  decide
theorem low_period_t1_n11_h0_a20 :
    Nat.powMod 2 (47424279170268000) 206391312495 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a21 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 412782526575+0)%412782526575 ≠ 4348831%412782526575 := by
  decide
theorem low_period_t1_n11_h0_a21 :
    Nat.powMod 2 (47424279170268000) 412782526575 = 1 := by
  decide

theorem low_nohit_t1_n11_h0_a22 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 825564954735+0)%825564954735 ≠ 4545661%825564954735 := by
  decide
theorem low_period_t1_n11_h0_a22 :
    Nat.powMod 2 (47424279170268000) 825564954735 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 516375+0)%516375 ≠ 528871%516375 := by
  decide
theorem low_period_t1_n12_h0_a1 :
    Nat.powMod 2 (47424279170268000) 516375 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 929475+0)%929475 ≠ 735421%929475 := by
  decide
theorem low_period_t1_n12_h0_a2 :
    Nat.powMod 2 (47424279170268000) 929475 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 1755675+0)%1755675 ≠ 941971%1755675 := by
  decide
theorem low_period_t1_n12_h0_a3 :
    Nat.powMod 2 (47424279170268000) 1755675 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 3408075+0)%3408075 ≠ 1148521%3408075 := by
  decide
theorem low_period_t1_n12_h0_a4 :
    Nat.powMod 2 (47424279170268000) 3408075 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 6712875+0)%6712875 ≠ 1355071%6712875 := by
  decide
theorem low_period_t1_n12_h0_a5 :
    Nat.powMod 2 (47424279170268000) 6712875 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 13322475+0)%13322475 ≠ 1561621%13322475 := by
  decide
theorem low_period_t1_n12_h0_a6 :
    Nat.powMod 2 (47424279170268000) 13322475 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 26541675+0)%26541675 ≠ 1768171%26541675 := by
  decide
theorem low_period_t1_n12_h0_a7 :
    Nat.powMod 2 (47424279170268000) 26541675 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 52980075+0)%52980075 ≠ 1974721%52980075 := by
  decide
theorem low_period_t1_n12_h0_a8 :
    Nat.powMod 2 (47424279170268000) 52980075 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 105856875+0)%105856875 ≠ 2181271%105856875 := by
  decide
theorem low_period_t1_n12_h0_a9 :
    Nat.powMod 2 (47424279170268000) 105856875 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 211610475+0)%211610475 ≠ 2387821%211610475 := by
  decide
theorem low_period_t1_n12_h0_a10 :
    Nat.powMod 2 (47424279170268000) 211610475 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 423117675+0)%423117675 ≠ 2594371%423117675 := by
  decide
theorem low_period_t1_n12_h0_a11 :
    Nat.powMod 2 (47424279170268000) 423117675 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 846132075+0)%846132075 ≠ 2800921%846132075 := by
  decide
theorem low_period_t1_n12_h0_a12 :
    Nat.powMod 2 (47424279170268000) 846132075 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 1692160875+0)%1692160875 ≠ 3007471%1692160875 := by
  decide
theorem low_period_t1_n12_h0_a13 :
    Nat.powMod 2 (47424279170268000) 1692160875 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 3384218475+0)%3384218475 ≠ 3214021%3384218475 := by
  decide
theorem low_period_t1_n12_h0_a14 :
    Nat.powMod 2 (47424279170268000) 3384218475 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 6768333675+0)%6768333675 ≠ 3420571%6768333675 := by
  decide
theorem low_period_t1_n12_h0_a15 :
    Nat.powMod 2 (47424279170268000) 6768333675 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 13536564075+0)%13536564075 ≠ 3627121%13536564075 := by
  decide
theorem low_period_t1_n12_h0_a16 :
    Nat.powMod 2 (47424279170268000) 13536564075 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 27073024875+0)%27073024875 ≠ 3833671%27073024875 := by
  decide
theorem low_period_t1_n12_h0_a17 :
    Nat.powMod 2 (47424279170268000) 27073024875 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 54145946475+0)%54145946475 ≠ 4040221%54145946475 := by
  decide
theorem low_period_t1_n12_h0_a18 :
    Nat.powMod 2 (47424279170268000) 54145946475 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 108291789675+0)%108291789675 ≠ 4246771%108291789675 := by
  decide
theorem low_period_t1_n12_h0_a19 :
    Nat.powMod 2 (47424279170268000) 108291789675 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a20 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 216583476075+0)%216583476075 ≠ 4453321%216583476075 := by
  decide
theorem low_period_t1_n12_h0_a20 :
    Nat.powMod 2 (47424279170268000) 216583476075 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a21 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 433166848875+0)%433166848875 ≠ 4659871%433166848875 := by
  decide
theorem low_period_t1_n12_h0_a21 :
    Nat.powMod 2 (47424279170268000) 433166848875 = 1 := by
  decide

theorem low_nohit_t1_n12_h0_a22 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+14) 866333594475+0)%866333594475 ≠ 4866421%866333594475 := by
  decide
theorem low_period_t1_n12_h0_a22 :
    Nat.powMod 2 (47424279170268000) 866333594475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 2460375+0)%2460375 ≠ 1513367%2460375 := by
  decide
theorem low_period_t1_n13_h0_a1 :
    Nat.powMod 2 (47424279170268000) 2460375 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 4428675+0)%4428675 ≠ 2497517%4428675 := by
  decide
theorem low_period_t1_n13_h0_a2 :
    Nat.powMod 2 (47424279170268000) 4428675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 8365275+0)%8365275 ≠ 3481667%8365275 := by
  decide
theorem low_period_t1_n13_h0_a3 :
    Nat.powMod 2 (47424279170268000) 8365275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 16238475+0)%16238475 ≠ 4465817%16238475 := by
  decide
theorem low_period_t1_n13_h0_a4 :
    Nat.powMod 2 (47424279170268000) 16238475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 31984875+0)%31984875 ≠ 5449967%31984875 := by
  decide
theorem low_period_t1_n13_h0_a5 :
    Nat.powMod 2 (47424279170268000) 31984875 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 63477675+0)%63477675 ≠ 6434117%63477675 := by
  decide
theorem low_period_t1_n13_h0_a6 :
    Nat.powMod 2 (47424279170268000) 63477675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 126463275+0)%126463275 ≠ 7418267%126463275 := by
  decide
theorem low_period_t1_n13_h0_a7 :
    Nat.powMod 2 (47424279170268000) 126463275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 252434475+0)%252434475 ≠ 8402417%252434475 := by
  decide
theorem low_period_t1_n13_h0_a8 :
    Nat.powMod 2 (47424279170268000) 252434475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 504376875+0)%504376875 ≠ 9386567%504376875 := by
  decide
theorem low_period_t1_n13_h0_a9 :
    Nat.powMod 2 (47424279170268000) 504376875 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 1008261675+0)%1008261675 ≠ 10370717%1008261675 := by
  decide
theorem low_period_t1_n13_h0_a10 :
    Nat.powMod 2 (47424279170268000) 1008261675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 2016031275+0)%2016031275 ≠ 11354867%2016031275 := by
  decide
theorem low_period_t1_n13_h0_a11 :
    Nat.powMod 2 (47424279170268000) 2016031275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 4031570475+0)%4031570475 ≠ 12339017%4031570475 := by
  decide
theorem low_period_t1_n13_h0_a12 :
    Nat.powMod 2 (47424279170268000) 4031570475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 8062648875+0)%8062648875 ≠ 13323167%8062648875 := by
  decide
theorem low_period_t1_n13_h0_a13 :
    Nat.powMod 2 (47424279170268000) 8062648875 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 16124805675+0)%16124805675 ≠ 14307317%16124805675 := by
  decide
theorem low_period_t1_n13_h0_a14 :
    Nat.powMod 2 (47424279170268000) 16124805675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 32249119275+0)%32249119275 ≠ 15291467%32249119275 := by
  decide
theorem low_period_t1_n13_h0_a15 :
    Nat.powMod 2 (47424279170268000) 32249119275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 64497746475+0)%64497746475 ≠ 16275617%64497746475 := by
  decide
theorem low_period_t1_n13_h0_a16 :
    Nat.powMod 2 (47424279170268000) 64497746475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 128995000875+0)%128995000875 ≠ 17259767%128995000875 := by
  decide
theorem low_period_t1_n13_h0_a17 :
    Nat.powMod 2 (47424279170268000) 128995000875 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 257989509675+0)%257989509675 ≠ 18243917%257989509675 := by
  decide
theorem low_period_t1_n13_h0_a18 :
    Nat.powMod 2 (47424279170268000) 257989509675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 515978527275+0)%515978527275 ≠ 19228067%515978527275 := by
  decide
theorem low_period_t1_n13_h0_a19 :
    Nat.powMod 2 (47424279170268000) 515978527275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a20 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 1031956562475+0)%1031956562475 ≠ 20212217%1031956562475 := by
  decide
theorem low_period_t1_n13_h0_a20 :
    Nat.powMod 2 (47424279170268000) 1031956562475 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a21 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 2063912632875+0)%2063912632875 ≠ 21196367%2063912632875 := by
  decide
theorem low_period_t1_n13_h0_a21 :
    Nat.powMod 2 (47424279170268000) 2063912632875 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a22 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 4127824773675+0)%4127824773675 ≠ 22180517%4127824773675 := by
  decide
theorem low_period_t1_n13_h0_a22 :
    Nat.powMod 2 (47424279170268000) 4127824773675 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a23 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 8255649055275+0)%8255649055275 ≠ 23164667%8255649055275 := by
  decide
theorem low_period_t1_n13_h0_a23 :
    Nat.powMod 2 (47424279170268000) 8255649055275 = 1 := by
  decide

theorem low_nohit_t1_n13_h0_a24 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+15) 16511297618475+0)%16511297618475 ≠ 24148817%16511297618475 := by
  decide
theorem low_period_t1_n13_h0_a24 :
    Nat.powMod 2 (47424279170268000) 16511297618475 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a1 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 4428675+0)%4428675 ≠ 5758223%4428675 := by
  decide
theorem low_period_t1_n14_h0_a1 :
    Nat.powMod 2 (47424279170268000) 4428675 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a2 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 7971615+0)%7971615 ≠ 7529693%7971615 := by
  decide
theorem low_period_t1_n14_h0_a2 :
    Nat.powMod 2 (47424279170268000) 7971615 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a3 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 15057495+0)%15057495 ≠ 9301163%15057495 := by
  decide
theorem low_period_t1_n14_h0_a3 :
    Nat.powMod 2 (47424279170268000) 15057495 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a4 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 29229255+0)%29229255 ≠ 11072633%29229255 := by
  decide
theorem low_period_t1_n14_h0_a4 :
    Nat.powMod 2 (47424279170268000) 29229255 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a5 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 57572775+0)%57572775 ≠ 12844103%57572775 := by
  decide
theorem low_period_t1_n14_h0_a5 :
    Nat.powMod 2 (47424279170268000) 57572775 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a6 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 114259815+0)%114259815 ≠ 14615573%114259815 := by
  decide
theorem low_period_t1_n14_h0_a6 :
    Nat.powMod 2 (47424279170268000) 114259815 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a7 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 227633895+0)%227633895 ≠ 16387043%227633895 := by
  decide
theorem low_period_t1_n14_h0_a7 :
    Nat.powMod 2 (47424279170268000) 227633895 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a8 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 454382055+0)%454382055 ≠ 18158513%454382055 := by
  decide
theorem low_period_t1_n14_h0_a8 :
    Nat.powMod 2 (47424279170268000) 454382055 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a9 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 907878375+0)%907878375 ≠ 19929983%907878375 := by
  decide
theorem low_period_t1_n14_h0_a9 :
    Nat.powMod 2 (47424279170268000) 907878375 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a10 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 1814871015+0)%1814871015 ≠ 21701453%1814871015 := by
  decide
theorem low_period_t1_n14_h0_a10 :
    Nat.powMod 2 (47424279170268000) 1814871015 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a11 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 3628856295+0)%3628856295 ≠ 23472923%3628856295 := by
  decide
theorem low_period_t1_n14_h0_a11 :
    Nat.powMod 2 (47424279170268000) 3628856295 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a12 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 7256826855+0)%7256826855 ≠ 25244393%7256826855 := by
  decide
theorem low_period_t1_n14_h0_a12 :
    Nat.powMod 2 (47424279170268000) 7256826855 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a13 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 14512767975+0)%14512767975 ≠ 27015863%14512767975 := by
  decide
theorem low_period_t1_n14_h0_a13 :
    Nat.powMod 2 (47424279170268000) 14512767975 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a14 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 29024650215+0)%29024650215 ≠ 28787333%29024650215 := by
  decide
theorem low_period_t1_n14_h0_a14 :
    Nat.powMod 2 (47424279170268000) 29024650215 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a15 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 58048414695+0)%58048414695 ≠ 30558803%58048414695 := by
  decide
theorem low_period_t1_n14_h0_a15 :
    Nat.powMod 2 (47424279170268000) 58048414695 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a16 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 116095943655+0)%116095943655 ≠ 32330273%116095943655 := by
  decide
theorem low_period_t1_n14_h0_a16 :
    Nat.powMod 2 (47424279170268000) 116095943655 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a17 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 232191001575+0)%232191001575 ≠ 34101743%232191001575 := by
  decide
theorem low_period_t1_n14_h0_a17 :
    Nat.powMod 2 (47424279170268000) 232191001575 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a18 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 464381117415+0)%464381117415 ≠ 35873213%464381117415 := by
  decide
theorem low_period_t1_n14_h0_a18 :
    Nat.powMod 2 (47424279170268000) 464381117415 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a19 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 928761349095+0)%928761349095 ≠ 37644683%928761349095 := by
  decide
theorem low_period_t1_n14_h0_a19 :
    Nat.powMod 2 (47424279170268000) 928761349095 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a20 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 1857521812455+0)%1857521812455 ≠ 39416153%1857521812455 := by
  decide
theorem low_period_t1_n14_h0_a20 :
    Nat.powMod 2 (47424279170268000) 1857521812455 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a21 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 3715042739175+0)%3715042739175 ≠ 41187623%3715042739175 := by
  decide
theorem low_period_t1_n14_h0_a21 :
    Nat.powMod 2 (47424279170268000) 3715042739175 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a22 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 7430084592615+0)%7430084592615 ≠ 42959093%7430084592615 := by
  decide
theorem low_period_t1_n14_h0_a22 :
    Nat.powMod 2 (47424279170268000) 7430084592615 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a23 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 14860168299495+0)%14860168299495 ≠ 44730563%14860168299495 := by
  decide
theorem low_period_t1_n14_h0_a23 :
    Nat.powMod 2 (47424279170268000) 14860168299495 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a24 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 29720335713255+0)%29720335713255 ≠ 46502033%29720335713255 := by
  decide
theorem low_period_t1_n14_h0_a24 :
    Nat.powMod 2 (47424279170268000) 29720335713255 = 1 := by
  decide

theorem low_nohit_t1_n14_h0_a25 :
    ∀ r ∈ residues_t1,
      (Nat.powMod 2 (1458*r+17) 59440670540775+0)%59440670540775 ≠ 48273503%59440670540775 := by
  decide
theorem low_period_t1_n14_h0_a25 :
    Nat.powMod 2 (47424279170268000) 59440670540775 = 1 := by
  decide

-- t1: 15 nodes, 14 edges, 455 generic rows;
-- emitted 376 intermediate non-edge low-a certificates and 14 valuation certificates.
-- 9 intermediate rows are graph edges and are handled by the child-node equations.

def residues_h1a3 : List Nat := [50, 58, 170, 178, 230, 238, 350, 430, 490, 598, 610, 710, 770, 778, 790, 850, 890, 898, 958, 1030, 1070, 1078, 1130, 1138, 1210, 1250]
def period_h1a3 : Nat := 80313433200

def nodes_h1a3 : List AffineNode :=
  [
    { s := 0, b := 0, c := 0, C := 1 },
    { s := 5, b := 0, c := 104, C := 51 },
    { s := 7, b := 0, c := 518, C := 255 },
    { s := 8, b := 0, c := 1444, C := 459 },
    { s := 10, b := 0, c := 6694, C := 2295 },
    { s := 13, b := 0, c := 81092, C := 20655 },
    { s := 16, b := 0, c := 896596, C := 185895 }
  ]

def edges_h1a3 : List (Nat × Nat × Nat × Nat) :=
  [
    ⟨0, 1, 1, 3⟩,
    ⟨1, 2, 0, 1⟩,
    ⟨1, 3, 0, 2⟩,
    ⟨3, 4, 0, 1⟩,
    ⟨4, 5, 0, 2⟩,
    ⟨5, 6, 0, 2⟩
  ]

theorem val_nohit_h1a3_n1 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+5) 9 ≠ 155%9 := by
  decide
theorem val_period_h1a3_n1 :
    Nat.powMod 2 (117096985605600) 9 = 1 := by
  decide

theorem val_nohit_h1a3_n2 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+7) 9 ≠ 773%9 := by
  decide
theorem val_period_h1a3_n2 :
    Nat.powMod 2 (117096985605600) 9 = 1 := by
  decide

theorem val_nohit_h1a3_n3 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+8) 81 ≠ 1903%81 := by
  decide
theorem val_period_h1a3_n3 :
    Nat.powMod 2 (117096985605600) 81 = 1 := by
  decide

theorem val_nohit_h1a3_n4 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+10) 81 ≠ 8989%81 := by
  decide
theorem val_period_h1a3_n4 :
    Nat.powMod 2 (117096985605600) 81 = 1 := by
  decide

theorem val_nohit_h1a3_n5 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+13) 729 ≠ 101747%729 := by
  decide
theorem val_period_h1a3_n5 :
    Nat.powMod 2 (117096985605600) 729 = 1 := by
  decide

theorem val_nohit_h1a3_n6 :
    ∀ r ∈ residues_h1a3,
      Nat.powMod 2 (1458*r+16) 6561 ≠ 1082491%6561 := by
  decide
theorem val_period_h1a3_n6 :
    Nat.powMod 2 (117096985605600) 6561 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 867+0)%867 ≠ 463%867 := by
  decide
theorem low_period_h1a3_n1_h0_a3 :
    Nat.powMod 2 (117096985605600) 867 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 1683+0)%1683 ≠ 565%1683 := by
  decide
theorem low_period_h1a3_n1_h0_a4 :
    Nat.powMod 2 (117096985605600) 1683 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 3315+0)%3315 ≠ 667%3315 := by
  decide
theorem low_period_h1a3_n1_h0_a5 :
    Nat.powMod 2 (117096985605600) 3315 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 6579+0)%6579 ≠ 769%6579 := by
  decide
theorem low_period_h1a3_n1_h0_a6 :
    Nat.powMod 2 (117096985605600) 6579 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 13107+0)%13107 ≠ 871%13107 := by
  decide
theorem low_period_h1a3_n1_h0_a7 :
    Nat.powMod 2 (117096985605600) 13107 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 26163+0)%26163 ≠ 973%26163 := by
  decide
theorem low_period_h1a3_n1_h0_a8 :
    Nat.powMod 2 (117096985605600) 26163 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 52275+0)%52275 ≠ 1075%52275 := by
  decide
theorem low_period_h1a3_n1_h0_a9 :
    Nat.powMod 2 (117096985605600) 52275 = 1 := by
  decide

theorem low_nohit_h1a3_n1_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+6) 104499+0)%104499 ≠ 1177%104499 := by
  decide
theorem low_period_h1a3_n1_h0_a10 :
    Nat.powMod 2 (117096985605600) 104499 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a1 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 1275+0)%1275 ≠ 1291%1275 := by
  decide
theorem low_period_h1a3_n2_h0_a1 :
    Nat.powMod 2 (117096985605600) 1275 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a2 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 2295+0)%2295 ≠ 1801%2295 := by
  decide
theorem low_period_h1a3_n2_h0_a2 :
    Nat.powMod 2 (117096985605600) 2295 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 4335+0)%4335 ≠ 2311%4335 := by
  decide
theorem low_period_h1a3_n2_h0_a3 :
    Nat.powMod 2 (117096985605600) 4335 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 8415+0)%8415 ≠ 2821%8415 := by
  decide
theorem low_period_h1a3_n2_h0_a4 :
    Nat.powMod 2 (117096985605600) 8415 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 16575+0)%16575 ≠ 3331%16575 := by
  decide
theorem low_period_h1a3_n2_h0_a5 :
    Nat.powMod 2 (117096985605600) 16575 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 32895+0)%32895 ≠ 3841%32895 := by
  decide
theorem low_period_h1a3_n2_h0_a6 :
    Nat.powMod 2 (117096985605600) 32895 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 65535+0)%65535 ≠ 4351%65535 := by
  decide
theorem low_period_h1a3_n2_h0_a7 :
    Nat.powMod 2 (117096985605600) 65535 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 130815+0)%130815 ≠ 4861%130815 := by
  decide
theorem low_period_h1a3_n2_h0_a8 :
    Nat.powMod 2 (117096985605600) 130815 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 261375+0)%261375 ≠ 5371%261375 := by
  decide
theorem low_period_h1a3_n2_h0_a9 :
    Nat.powMod 2 (117096985605600) 261375 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 522495+0)%522495 ≠ 5881%522495 := by
  decide
theorem low_period_h1a3_n2_h0_a10 :
    Nat.powMod 2 (117096985605600) 522495 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a11 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 1044735+0)%1044735 ≠ 6391%1044735 := by
  decide
theorem low_period_h1a3_n2_h0_a11 :
    Nat.powMod 2 (117096985605600) 1044735 = 1 := by
  decide

theorem low_nohit_h1a3_n2_h0_a12 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+8) 2089215+0)%2089215 ≠ 6901%2089215 := by
  decide
theorem low_period_h1a3_n2_h0_a12 :
    Nat.powMod 2 (117096985605600) 2089215 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a2 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 4131+0)%4131 ≠ 4265%4131 := by
  decide
theorem low_period_h1a3_n3_h0_a2 :
    Nat.powMod 2 (117096985605600) 4131 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 7803+0)%7803 ≠ 5183%7803 := by
  decide
theorem low_period_h1a3_n3_h0_a3 :
    Nat.powMod 2 (117096985605600) 7803 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 15147+0)%15147 ≠ 6101%15147 := by
  decide
theorem low_period_h1a3_n3_h0_a4 :
    Nat.powMod 2 (117096985605600) 15147 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 29835+0)%29835 ≠ 7019%29835 := by
  decide
theorem low_period_h1a3_n3_h0_a5 :
    Nat.powMod 2 (117096985605600) 29835 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 59211+0)%59211 ≠ 7937%59211 := by
  decide
theorem low_period_h1a3_n3_h0_a6 :
    Nat.powMod 2 (117096985605600) 59211 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 117963+0)%117963 ≠ 8855%117963 := by
  decide
theorem low_period_h1a3_n3_h0_a7 :
    Nat.powMod 2 (117096985605600) 117963 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 235467+0)%235467 ≠ 9773%235467 := by
  decide
theorem low_period_h1a3_n3_h0_a8 :
    Nat.powMod 2 (117096985605600) 235467 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 470475+0)%470475 ≠ 10691%470475 := by
  decide
theorem low_period_h1a3_n3_h0_a9 :
    Nat.powMod 2 (117096985605600) 470475 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 940491+0)%940491 ≠ 11609%940491 := by
  decide
theorem low_period_h1a3_n3_h0_a10 :
    Nat.powMod 2 (117096985605600) 940491 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a11 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 1880523+0)%1880523 ≠ 12527%1880523 := by
  decide
theorem low_period_h1a3_n3_h0_a11 :
    Nat.powMod 2 (117096985605600) 1880523 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a12 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 3760587+0)%3760587 ≠ 13445%3760587 := by
  decide
theorem low_period_h1a3_n3_h0_a12 :
    Nat.powMod 2 (117096985605600) 3760587 = 1 := by
  decide

theorem low_nohit_h1a3_n3_h0_a13 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+9) 7520715+0)%7520715 ≠ 14363%7520715 := by
  decide
theorem low_period_h1a3_n3_h0_a13 :
    Nat.powMod 2 (117096985605600) 7520715 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a1 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 11475+0)%11475 ≠ 15683%11475 := by
  decide
theorem low_period_h1a3_n4_h0_a1 :
    Nat.powMod 2 (117096985605600) 11475 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 39015+0)%39015 ≠ 24863%39015 := by
  decide
theorem low_period_h1a3_n4_h0_a3 :
    Nat.powMod 2 (117096985605600) 39015 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 75735+0)%75735 ≠ 29453%75735 := by
  decide
theorem low_period_h1a3_n4_h0_a4 :
    Nat.powMod 2 (117096985605600) 75735 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 149175+0)%149175 ≠ 34043%149175 := by
  decide
theorem low_period_h1a3_n4_h0_a5 :
    Nat.powMod 2 (117096985605600) 149175 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 296055+0)%296055 ≠ 38633%296055 := by
  decide
theorem low_period_h1a3_n4_h0_a6 :
    Nat.powMod 2 (117096985605600) 296055 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 589815+0)%589815 ≠ 43223%589815 := by
  decide
theorem low_period_h1a3_n4_h0_a7 :
    Nat.powMod 2 (117096985605600) 589815 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 1177335+0)%1177335 ≠ 47813%1177335 := by
  decide
theorem low_period_h1a3_n4_h0_a8 :
    Nat.powMod 2 (117096985605600) 1177335 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 2352375+0)%2352375 ≠ 52403%2352375 := by
  decide
theorem low_period_h1a3_n4_h0_a9 :
    Nat.powMod 2 (117096985605600) 2352375 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 4702455+0)%4702455 ≠ 56993%4702455 := by
  decide
theorem low_period_h1a3_n4_h0_a10 :
    Nat.powMod 2 (117096985605600) 4702455 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a11 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 9402615+0)%9402615 ≠ 61583%9402615 := by
  decide
theorem low_period_h1a3_n4_h0_a11 :
    Nat.powMod 2 (117096985605600) 9402615 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a12 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 18802935+0)%18802935 ≠ 66173%18802935 := by
  decide
theorem low_period_h1a3_n4_h0_a12 :
    Nat.powMod 2 (117096985605600) 18802935 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a13 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 37603575+0)%37603575 ≠ 70763%37603575 := by
  decide
theorem low_period_h1a3_n4_h0_a13 :
    Nat.powMod 2 (117096985605600) 37603575 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a14 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 75204855+0)%75204855 ≠ 75353%75204855 := by
  decide
theorem low_period_h1a3_n4_h0_a14 :
    Nat.powMod 2 (117096985605600) 75204855 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a15 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 150407415+0)%150407415 ≠ 79943%150407415 := by
  decide
theorem low_period_h1a3_n4_h0_a15 :
    Nat.powMod 2 (117096985605600) 150407415 = 1 := by
  decide

theorem low_nohit_h1a3_n4_h0_a16 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+11) 300812535+0)%300812535 ≠ 84533%300812535 := by
  decide
theorem low_period_h1a3_n4_h0_a16 :
    Nat.powMod 2 (117096985605600) 300812535 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a1 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 103275+0)%103275 ≠ 182839%103275 := by
  decide
theorem low_period_h1a3_n5_h0_a1 :
    Nat.powMod 2 (117096985605600) 103275 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 351135+0)%351135 ≠ 265459%351135 := by
  decide
theorem low_period_h1a3_n5_h0_a3 :
    Nat.powMod 2 (117096985605600) 351135 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 681615+0)%681615 ≠ 306769%681615 := by
  decide
theorem low_period_h1a3_n5_h0_a4 :
    Nat.powMod 2 (117096985605600) 681615 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 1342575+0)%1342575 ≠ 348079%1342575 := by
  decide
theorem low_period_h1a3_n5_h0_a5 :
    Nat.powMod 2 (117096985605600) 1342575 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 2664495+0)%2664495 ≠ 389389%2664495 := by
  decide
theorem low_period_h1a3_n5_h0_a6 :
    Nat.powMod 2 (117096985605600) 2664495 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 5308335+0)%5308335 ≠ 430699%5308335 := by
  decide
theorem low_period_h1a3_n5_h0_a7 :
    Nat.powMod 2 (117096985605600) 5308335 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 10596015+0)%10596015 ≠ 472009%10596015 := by
  decide
theorem low_period_h1a3_n5_h0_a8 :
    Nat.powMod 2 (117096985605600) 10596015 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 21171375+0)%21171375 ≠ 513319%21171375 := by
  decide
theorem low_period_h1a3_n5_h0_a9 :
    Nat.powMod 2 (117096985605600) 21171375 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 42322095+0)%42322095 ≠ 554629%42322095 := by
  decide
theorem low_period_h1a3_n5_h0_a10 :
    Nat.powMod 2 (117096985605600) 42322095 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a11 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 84623535+0)%84623535 ≠ 595939%84623535 := by
  decide
theorem low_period_h1a3_n5_h0_a11 :
    Nat.powMod 2 (117096985605600) 84623535 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a12 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 169226415+0)%169226415 ≠ 637249%169226415 := by
  decide
theorem low_period_h1a3_n5_h0_a12 :
    Nat.powMod 2 (117096985605600) 169226415 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a13 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 338432175+0)%338432175 ≠ 678559%338432175 := by
  decide
theorem low_period_h1a3_n5_h0_a13 :
    Nat.powMod 2 (117096985605600) 338432175 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a14 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 676843695+0)%676843695 ≠ 719869%676843695 := by
  decide
theorem low_period_h1a3_n5_h0_a14 :
    Nat.powMod 2 (117096985605600) 676843695 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a15 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 1353666735+0)%1353666735 ≠ 761179%1353666735 := by
  decide
theorem low_period_h1a3_n5_h0_a15 :
    Nat.powMod 2 (117096985605600) 1353666735 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a16 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 2707312815+0)%2707312815 ≠ 802489%2707312815 := by
  decide
theorem low_period_h1a3_n5_h0_a16 :
    Nat.powMod 2 (117096985605600) 2707312815 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a17 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 5414604975+0)%5414604975 ≠ 843799%5414604975 := by
  decide
theorem low_period_h1a3_n5_h0_a17 :
    Nat.powMod 2 (117096985605600) 5414604975 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a18 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 10829189295+0)%10829189295 ≠ 885109%10829189295 := by
  decide
theorem low_period_h1a3_n5_h0_a18 :
    Nat.powMod 2 (117096985605600) 10829189295 = 1 := by
  decide

theorem low_nohit_h1a3_n5_h0_a19 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+14) 21658357935+0)%21658357935 ≠ 926419%21658357935 := by
  decide
theorem low_period_h1a3_n5_h0_a19 :
    Nat.powMod 2 (117096985605600) 21658357935 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a1 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 929475+0)%929475 ≠ 1979087%929475 := by
  decide
theorem low_period_h1a3_n6_h0_a1 :
    Nat.powMod 2 (117096985605600) 929475 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a2 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 1673055+0)%1673055 ≠ 2350877%1673055 := by
  decide
theorem low_period_h1a3_n6_h0_a2 :
    Nat.powMod 2 (117096985605600) 1673055 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a3 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 3160215+0)%3160215 ≠ 2722667%3160215 := by
  decide
theorem low_period_h1a3_n6_h0_a3 :
    Nat.powMod 2 (117096985605600) 3160215 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a4 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 6134535+0)%6134535 ≠ 3094457%6134535 := by
  decide
theorem low_period_h1a3_n6_h0_a4 :
    Nat.powMod 2 (117096985605600) 6134535 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a5 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 12083175+0)%12083175 ≠ 3466247%12083175 := by
  decide
theorem low_period_h1a3_n6_h0_a5 :
    Nat.powMod 2 (117096985605600) 12083175 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a6 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 23980455+0)%23980455 ≠ 3838037%23980455 := by
  decide
theorem low_period_h1a3_n6_h0_a6 :
    Nat.powMod 2 (117096985605600) 23980455 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a7 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 47775015+0)%47775015 ≠ 4209827%47775015 := by
  decide
theorem low_period_h1a3_n6_h0_a7 :
    Nat.powMod 2 (117096985605600) 47775015 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a8 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 95364135+0)%95364135 ≠ 4581617%95364135 := by
  decide
theorem low_period_h1a3_n6_h0_a8 :
    Nat.powMod 2 (117096985605600) 95364135 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a9 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 190542375+0)%190542375 ≠ 4953407%190542375 := by
  decide
theorem low_period_h1a3_n6_h0_a9 :
    Nat.powMod 2 (117096985605600) 190542375 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a10 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 380898855+0)%380898855 ≠ 5325197%380898855 := by
  decide
theorem low_period_h1a3_n6_h0_a10 :
    Nat.powMod 2 (117096985605600) 380898855 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a11 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 761611815+0)%761611815 ≠ 5696987%761611815 := by
  decide
theorem low_period_h1a3_n6_h0_a11 :
    Nat.powMod 2 (117096985605600) 761611815 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a12 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 1523037735+0)%1523037735 ≠ 6068777%1523037735 := by
  decide
theorem low_period_h1a3_n6_h0_a12 :
    Nat.powMod 2 (117096985605600) 1523037735 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a13 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 3045889575+0)%3045889575 ≠ 6440567%3045889575 := by
  decide
theorem low_period_h1a3_n6_h0_a13 :
    Nat.powMod 2 (117096985605600) 3045889575 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a14 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 6091593255+0)%6091593255 ≠ 6812357%6091593255 := by
  decide
theorem low_period_h1a3_n6_h0_a14 :
    Nat.powMod 2 (117096985605600) 6091593255 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a15 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 12183000615+0)%12183000615 ≠ 7184147%12183000615 := by
  decide
theorem low_period_h1a3_n6_h0_a15 :
    Nat.powMod 2 (117096985605600) 12183000615 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a16 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 24365815335+0)%24365815335 ≠ 7555937%24365815335 := by
  decide
theorem low_period_h1a3_n6_h0_a16 :
    Nat.powMod 2 (117096985605600) 24365815335 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a17 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 48731444775+0)%48731444775 ≠ 7927727%48731444775 := by
  decide
theorem low_period_h1a3_n6_h0_a17 :
    Nat.powMod 2 (117096985605600) 48731444775 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a18 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 97462703655+0)%97462703655 ≠ 8299517%97462703655 := by
  decide
theorem low_period_h1a3_n6_h0_a18 :
    Nat.powMod 2 (117096985605600) 97462703655 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a19 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 194925221415+0)%194925221415 ≠ 8671307%194925221415 := by
  decide
theorem low_period_h1a3_n6_h0_a19 :
    Nat.powMod 2 (117096985605600) 194925221415 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a20 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 389850256935+0)%389850256935 ≠ 9043097%389850256935 := by
  decide
theorem low_period_h1a3_n6_h0_a20 :
    Nat.powMod 2 (117096985605600) 389850256935 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a21 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 779700327975+0)%779700327975 ≠ 9414887%779700327975 := by
  decide
theorem low_period_h1a3_n6_h0_a21 :
    Nat.powMod 2 (117096985605600) 779700327975 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a22 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 1559400470055+0)%1559400470055 ≠ 9786677%1559400470055 := by
  decide
theorem low_period_h1a3_n6_h0_a22 :
    Nat.powMod 2 (117096985605600) 1559400470055 = 1 := by
  decide

theorem low_nohit_h1a3_n6_h0_a23 :
    ∀ r ∈ residues_h1a3,
      (Nat.powMod 2 (1458*r+17) 3118800754215+0)%3118800754215 ≠ 10158467%3118800754215 := by
  decide
theorem low_period_h1a3_n6_h0_a23 :
    Nat.powMod 2 (117096985605600) 3118800754215 = 1 := by
  decide

-- h1a3: 7 nodes, 6 edges, 163 generic rows;
-- emitted 88 intermediate non-edge low-a certificates and 6 valuation certificates.
-- 5 intermediate rows are graph edges and are handled by the child-node equations.

def residues_h3a6 : List Nat := [40, 124, 152, 236, 292, 320, 376, 404, 544, 572, 628, 656, 740, 796, 824, 880, 992, 1048, 1076, 1132, 1160, 1244]
def period_h3a6 : Nat := 150151201200

def nodes_h3a6 : List AffineNode :=
  [
    { s := 0, b := 0, c := 0, C := 1 },
    { s := 10, b := 0, c := 16576, C := 3483 },
    { s := 13, b := 0, c := 174404, C := 31347 }
  ]

def edges_h3a6 : List (Nat × Nat × Nat × Nat) :=
  [
    ⟨0, 1, 3, 6⟩,
    ⟨1, 2, 0, 2⟩
  ]

theorem val_nohit_h3a6_n1 :
    ∀ r ∈ residues_h3a6,
      Nat.powMod 2 (1458*r+10) 243 ≠ 20059%243 := by
  decide
theorem val_period_h3a6_n1 :
    Nat.powMod 2 (218920451349600) 243 = 1 := by
  decide

theorem val_nohit_h3a6_n2 :
    ∀ r ∈ residues_h3a6,
      Nat.powMod 2 (1458*r+13) 2187 ≠ 205751%2187 := by
  decide
theorem val_period_h3a6_n2 :
    Nat.powMod 2 (218920451349600) 2187 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a1 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 17415+0)%17415 ≠ 36635%17415 := by
  decide
theorem low_period_h3a6_n1_h0_a1 :
    Nat.powMod 2 (218920451349600) 17415 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a3 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 59211+0)%59211 ≠ 50567%59211 := by
  decide
theorem low_period_h3a6_n1_h0_a3 :
    Nat.powMod 2 (218920451349600) 59211 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a4 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 114939+0)%114939 ≠ 57533%114939 := by
  decide
theorem low_period_h3a6_n1_h0_a4 :
    Nat.powMod 2 (218920451349600) 114939 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a5 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 226395+0)%226395 ≠ 64499%226395 := by
  decide
theorem low_period_h3a6_n1_h0_a5 :
    Nat.powMod 2 (218920451349600) 226395 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a6 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 449307+0)%449307 ≠ 71465%449307 := by
  decide
theorem low_period_h3a6_n1_h0_a6 :
    Nat.powMod 2 (218920451349600) 449307 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a7 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 895131+0)%895131 ≠ 78431%895131 := by
  decide
theorem low_period_h3a6_n1_h0_a7 :
    Nat.powMod 2 (218920451349600) 895131 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a8 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 1786779+0)%1786779 ≠ 85397%1786779 := by
  decide
theorem low_period_h3a6_n1_h0_a8 :
    Nat.powMod 2 (218920451349600) 1786779 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a9 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 3570075+0)%3570075 ≠ 92363%3570075 := by
  decide
theorem low_period_h3a6_n1_h0_a9 :
    Nat.powMod 2 (218920451349600) 3570075 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a10 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 7136667+0)%7136667 ≠ 99329%7136667 := by
  decide
theorem low_period_h3a6_n1_h0_a10 :
    Nat.powMod 2 (218920451349600) 7136667 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a11 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 14269851+0)%14269851 ≠ 106295%14269851 := by
  decide
theorem low_period_h3a6_n1_h0_a11 :
    Nat.powMod 2 (218920451349600) 14269851 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a12 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 28536219+0)%28536219 ≠ 113261%28536219 := by
  decide
theorem low_period_h3a6_n1_h0_a12 :
    Nat.powMod 2 (218920451349600) 28536219 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a13 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 57068955+0)%57068955 ≠ 120227%57068955 := by
  decide
theorem low_period_h3a6_n1_h0_a13 :
    Nat.powMod 2 (218920451349600) 57068955 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a14 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 114134427+0)%114134427 ≠ 127193%114134427 := by
  decide
theorem low_period_h3a6_n1_h0_a14 :
    Nat.powMod 2 (218920451349600) 114134427 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a15 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 228265371+0)%228265371 ≠ 134159%228265371 := by
  decide
theorem low_period_h3a6_n1_h0_a15 :
    Nat.powMod 2 (218920451349600) 228265371 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a16 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 456527259+0)%456527259 ≠ 141125%456527259 := by
  decide
theorem low_period_h3a6_n1_h0_a16 :
    Nat.powMod 2 (218920451349600) 456527259 = 1 := by
  decide

theorem low_nohit_h3a6_n1_h0_a17 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+11) 913051035+0)%913051035 ≠ 148091%913051035 := by
  decide
theorem low_period_h3a6_n1_h0_a17 :
    Nat.powMod 2 (218920451349600) 913051035 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a1 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 156735+0)%156735 ≠ 380155%156735 := by
  decide
theorem low_period_h3a6_n2_h0_a1 :
    Nat.powMod 2 (218920451349600) 156735 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a2 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 282123+0)%282123 ≠ 442849%282123 := by
  decide
theorem low_period_h3a6_n2_h0_a2 :
    Nat.powMod 2 (218920451349600) 282123 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a3 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 532899+0)%532899 ≠ 505543%532899 := by
  decide
theorem low_period_h3a6_n2_h0_a3 :
    Nat.powMod 2 (218920451349600) 532899 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a4 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 1034451+0)%1034451 ≠ 568237%1034451 := by
  decide
theorem low_period_h3a6_n2_h0_a4 :
    Nat.powMod 2 (218920451349600) 1034451 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a5 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 2037555+0)%2037555 ≠ 630931%2037555 := by
  decide
theorem low_period_h3a6_n2_h0_a5 :
    Nat.powMod 2 (218920451349600) 2037555 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a6 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 4043763+0)%4043763 ≠ 693625%4043763 := by
  decide
theorem low_period_h3a6_n2_h0_a6 :
    Nat.powMod 2 (218920451349600) 4043763 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a7 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 8056179+0)%8056179 ≠ 756319%8056179 := by
  decide
theorem low_period_h3a6_n2_h0_a7 :
    Nat.powMod 2 (218920451349600) 8056179 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a8 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 16081011+0)%16081011 ≠ 819013%16081011 := by
  decide
theorem low_period_h3a6_n2_h0_a8 :
    Nat.powMod 2 (218920451349600) 16081011 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a9 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 32130675+0)%32130675 ≠ 881707%32130675 := by
  decide
theorem low_period_h3a6_n2_h0_a9 :
    Nat.powMod 2 (218920451349600) 32130675 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a10 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 64230003+0)%64230003 ≠ 944401%64230003 := by
  decide
theorem low_period_h3a6_n2_h0_a10 :
    Nat.powMod 2 (218920451349600) 64230003 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a11 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 128428659+0)%128428659 ≠ 1007095%128428659 := by
  decide
theorem low_period_h3a6_n2_h0_a11 :
    Nat.powMod 2 (218920451349600) 128428659 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a12 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 256825971+0)%256825971 ≠ 1069789%256825971 := by
  decide
theorem low_period_h3a6_n2_h0_a12 :
    Nat.powMod 2 (218920451349600) 256825971 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a13 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 513620595+0)%513620595 ≠ 1132483%513620595 := by
  decide
theorem low_period_h3a6_n2_h0_a13 :
    Nat.powMod 2 (218920451349600) 513620595 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a14 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 1027209843+0)%1027209843 ≠ 1195177%1027209843 := by
  decide
theorem low_period_h3a6_n2_h0_a14 :
    Nat.powMod 2 (218920451349600) 1027209843 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a15 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 2054388339+0)%2054388339 ≠ 1257871%2054388339 := by
  decide
theorem low_period_h3a6_n2_h0_a15 :
    Nat.powMod 2 (218920451349600) 2054388339 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a16 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 4108745331+0)%4108745331 ≠ 1320565%4108745331 := by
  decide
theorem low_period_h3a6_n2_h0_a16 :
    Nat.powMod 2 (218920451349600) 4108745331 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a17 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 8217459315+0)%8217459315 ≠ 1383259%8217459315 := by
  decide
theorem low_period_h3a6_n2_h0_a17 :
    Nat.powMod 2 (218920451349600) 8217459315 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a18 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 16434887283+0)%16434887283 ≠ 1445953%16434887283 := by
  decide
theorem low_period_h3a6_n2_h0_a18 :
    Nat.powMod 2 (218920451349600) 16434887283 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a19 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 32869743219+0)%32869743219 ≠ 1508647%32869743219 := by
  decide
theorem low_period_h3a6_n2_h0_a19 :
    Nat.powMod 2 (218920451349600) 32869743219 = 1 := by
  decide

theorem low_nohit_h3a6_n2_h0_a20 :
    ∀ r ∈ residues_h3a6,
      (Nat.powMod 2 (1458*r+14) 65739455091+0)%65739455091 ≠ 1571341%65739455091 := by
  decide
theorem low_period_h3a6_n2_h0_a20 :
    Nat.powMod 2 (218920451349600) 65739455091 = 1 := by
  decide

-- h3a6: 3 nodes, 2 edges, 107 generic rows;
-- emitted 36 intermediate non-edge low-a certificates and 2 valuation certificates.
-- 1 intermediate rows are graph edges and are handled by the child-node equations.

def residues_h7a2 : List Nat := [28, 64, 136, 244, 280, 352, 388, 568, 604, 676, 784, 892, 928, 1000, 1036, 1108, 1252]
def period_h7a2 : Nat := 31426995600

def nodes_h7a2 : List AffineNode :=
  [
    { s := 0, b := 0, c := 0, C := 1 },
    { s := 10, b := 0, c := 9772, C := 19683 }
  ]

def edges_h7a2 : List (Nat × Nat × Nat × Nat) :=
  [
    ⟨0, 1, 7, 2⟩
  ]

theorem val_nohit_h7a2_n1 :
    ∀ r ∈ residues_h7a2,
      Nat.powMod 2 (1458*r+10) 59049 ≠ 29455%59049 := by
  decide
theorem val_period_h7a2_n1 :
    Nat.powMod 2 (45820559584800) 59049 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a1 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 98415+0)%98415 ≠ 39227%98415 := by
  decide
theorem low_period_h7a2_n1_h0_a1 :
    Nat.powMod 2 (45820559584800) 98415 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a2 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 177147+0)%177147 ≠ 78593%177147 := by
  decide
theorem low_period_h7a2_n1_h0_a2 :
    Nat.powMod 2 (45820559584800) 177147 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a3 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 334611+0)%334611 ≠ 117959%334611 := by
  decide
theorem low_period_h7a2_n1_h0_a3 :
    Nat.powMod 2 (45820559584800) 334611 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a4 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 649539+0)%649539 ≠ 157325%649539 := by
  decide
theorem low_period_h7a2_n1_h0_a4 :
    Nat.powMod 2 (45820559584800) 649539 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a5 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 1279395+0)%1279395 ≠ 196691%1279395 := by
  decide
theorem low_period_h7a2_n1_h0_a5 :
    Nat.powMod 2 (45820559584800) 1279395 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a6 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 2539107+0)%2539107 ≠ 236057%2539107 := by
  decide
theorem low_period_h7a2_n1_h0_a6 :
    Nat.powMod 2 (45820559584800) 2539107 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a7 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 5058531+0)%5058531 ≠ 275423%5058531 := by
  decide
theorem low_period_h7a2_n1_h0_a7 :
    Nat.powMod 2 (45820559584800) 5058531 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a8 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 10097379+0)%10097379 ≠ 314789%10097379 := by
  decide
theorem low_period_h7a2_n1_h0_a8 :
    Nat.powMod 2 (45820559584800) 10097379 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a9 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 20175075+0)%20175075 ≠ 354155%20175075 := by
  decide
theorem low_period_h7a2_n1_h0_a9 :
    Nat.powMod 2 (45820559584800) 20175075 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a10 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 40330467+0)%40330467 ≠ 393521%40330467 := by
  decide
theorem low_period_h7a2_n1_h0_a10 :
    Nat.powMod 2 (45820559584800) 40330467 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a11 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 80641251+0)%80641251 ≠ 432887%80641251 := by
  decide
theorem low_period_h7a2_n1_h0_a11 :
    Nat.powMod 2 (45820559584800) 80641251 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a12 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 161262819+0)%161262819 ≠ 472253%161262819 := by
  decide
theorem low_period_h7a2_n1_h0_a12 :
    Nat.powMod 2 (45820559584800) 161262819 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a13 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 322505955+0)%322505955 ≠ 511619%322505955 := by
  decide
theorem low_period_h7a2_n1_h0_a13 :
    Nat.powMod 2 (45820559584800) 322505955 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a14 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 644992227+0)%644992227 ≠ 550985%644992227 := by
  decide
theorem low_period_h7a2_n1_h0_a14 :
    Nat.powMod 2 (45820559584800) 644992227 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a15 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 1289964771+0)%1289964771 ≠ 590351%1289964771 := by
  decide
theorem low_period_h7a2_n1_h0_a15 :
    Nat.powMod 2 (45820559584800) 1289964771 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a16 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 2579909859+0)%2579909859 ≠ 629717%2579909859 := by
  decide
theorem low_period_h7a2_n1_h0_a16 :
    Nat.powMod 2 (45820559584800) 2579909859 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a17 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 5159800035+0)%5159800035 ≠ 669083%5159800035 := by
  decide
theorem low_period_h7a2_n1_h0_a17 :
    Nat.powMod 2 (45820559584800) 5159800035 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a18 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 10319580387+0)%10319580387 ≠ 708449%10319580387 := by
  decide
theorem low_period_h7a2_n1_h0_a18 :
    Nat.powMod 2 (45820559584800) 10319580387 = 1 := by
  decide

theorem low_nohit_h7a2_n1_h0_a19 :
    ∀ r ∈ residues_h7a2,
      (Nat.powMod 2 (1458*r+11) 20639141091+0)%20639141091 ≠ 747815%20639141091 := by
  decide
theorem low_period_h7a2_n1_h0_a19 :
    Nat.powMod 2 (45820559584800) 20639141091 = 1 := by
  decide

-- h7a2: 2 nodes, 1 edges, 89 generic rows;
-- emitted 19 intermediate non-edge low-a certificates and 1 valuation certificates.
-- 0 intermediate rows are graph edges and are handled by the child-node equations.

def residues_h7a4 : List Nat := [8, 188, 368, 428, 548, 608, 968, 1088, 1148]
def period_h7a4 : Nat := 10475665200

def nodes_h7a4 : List AffineNode :=
  [
    { s := 0, b := 0, c := 0, C := 1 },
    { s := 12, b := 0, c := 179056, C := 72171 }
  ]

def edges_h7a4 : List (Nat × Nat × Nat × Nat) :=
  [
    ⟨0, 1, 7, 4⟩
  ]

theorem val_nohit_h7a4_n1 :
    ∀ r ∈ residues_h7a4,
      Nat.powMod 2 (1458*r+12) 19683 ≠ 251227%19683 := by
  decide
theorem val_period_h7a4_n1 :
    Nat.powMod 2 (15273519861600) 19683 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a1 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 360855+0)%360855 ≠ 430283%360855 := by
  decide
theorem low_period_h7a4_n1_h0_a1 :
    Nat.powMod 2 (15273519861600) 360855 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a2 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 649539+0)%649539 ≠ 574625%649539 := by
  decide
theorem low_period_h7a4_n1_h0_a2 :
    Nat.powMod 2 (15273519861600) 649539 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a3 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 1226907+0)%1226907 ≠ 718967%1226907 := by
  decide
theorem low_period_h7a4_n1_h0_a3 :
    Nat.powMod 2 (15273519861600) 1226907 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a4 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 2381643+0)%2381643 ≠ 863309%2381643 := by
  decide
theorem low_period_h7a4_n1_h0_a4 :
    Nat.powMod 2 (15273519861600) 2381643 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a5 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 4691115+0)%4691115 ≠ 1007651%4691115 := by
  decide
theorem low_period_h7a4_n1_h0_a5 :
    Nat.powMod 2 (15273519861600) 4691115 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a6 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 9310059+0)%9310059 ≠ 1151993%9310059 := by
  decide
theorem low_period_h7a4_n1_h0_a6 :
    Nat.powMod 2 (15273519861600) 9310059 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a7 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 18547947+0)%18547947 ≠ 1296335%18547947 := by
  decide
theorem low_period_h7a4_n1_h0_a7 :
    Nat.powMod 2 (15273519861600) 18547947 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a8 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 37023723+0)%37023723 ≠ 1440677%37023723 := by
  decide
theorem low_period_h7a4_n1_h0_a8 :
    Nat.powMod 2 (15273519861600) 37023723 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a9 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 73975275+0)%73975275 ≠ 1585019%73975275 := by
  decide
theorem low_period_h7a4_n1_h0_a9 :
    Nat.powMod 2 (15273519861600) 73975275 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a10 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 147878379+0)%147878379 ≠ 1729361%147878379 := by
  decide
theorem low_period_h7a4_n1_h0_a10 :
    Nat.powMod 2 (15273519861600) 147878379 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a11 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 295684587+0)%295684587 ≠ 1873703%295684587 := by
  decide
theorem low_period_h7a4_n1_h0_a11 :
    Nat.powMod 2 (15273519861600) 295684587 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a12 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 591297003+0)%591297003 ≠ 2018045%591297003 := by
  decide
theorem low_period_h7a4_n1_h0_a12 :
    Nat.powMod 2 (15273519861600) 591297003 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a13 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 1182521835+0)%1182521835 ≠ 2162387%1182521835 := by
  decide
theorem low_period_h7a4_n1_h0_a13 :
    Nat.powMod 2 (15273519861600) 1182521835 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a14 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 2364971499+0)%2364971499 ≠ 2306729%2364971499 := by
  decide
theorem low_period_h7a4_n1_h0_a14 :
    Nat.powMod 2 (15273519861600) 2364971499 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a15 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 4729870827+0)%4729870827 ≠ 2451071%4729870827 := by
  decide
theorem low_period_h7a4_n1_h0_a15 :
    Nat.powMod 2 (15273519861600) 4729870827 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a16 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 9459669483+0)%9459669483 ≠ 2595413%9459669483 := by
  decide
theorem low_period_h7a4_n1_h0_a16 :
    Nat.powMod 2 (15273519861600) 9459669483 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a17 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 18919266795+0)%18919266795 ≠ 2739755%18919266795 := by
  decide
theorem low_period_h7a4_n1_h0_a17 :
    Nat.powMod 2 (15273519861600) 18919266795 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a18 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 37838461419+0)%37838461419 ≠ 2884097%37838461419 := by
  decide
theorem low_period_h7a4_n1_h0_a18 :
    Nat.powMod 2 (15273519861600) 37838461419 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a19 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 75676850667+0)%75676850667 ≠ 3028439%75676850667 := by
  decide
theorem low_period_h7a4_n1_h0_a19 :
    Nat.powMod 2 (15273519861600) 75676850667 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a20 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 151353629163+0)%151353629163 ≠ 3172781%151353629163 := by
  decide
theorem low_period_h7a4_n1_h0_a20 :
    Nat.powMod 2 (15273519861600) 151353629163 = 1 := by
  decide

theorem low_nohit_h7a4_n1_h0_a21 :
    ∀ r ∈ residues_h7a4,
      (Nat.powMod 2 (1458*r+13) 302707186155+0)%302707186155 ≠ 3317123%302707186155 := by
  decide
theorem low_period_h7a4_n1_h0_a21 :
    Nat.powMod 2 (15273519861600) 302707186155 = 1 := by
  decide

-- h7a4: 2 nodes, 1 edges, 91 generic rows;
-- emitted 21 intermediate non-edge low-a certificates and 1 valuation certificates.
-- 0 intermediate rows are graph edges and are handled by the child-node equations.

#print axioms val_nohit_t1_n1
end SheepPower1458
