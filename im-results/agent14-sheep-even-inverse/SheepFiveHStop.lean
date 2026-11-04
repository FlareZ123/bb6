import IndependentHBound
set_option maxRecDepth 32768
set_option exponentiation.threshold 10000

namespace SheepFiveHStop

theorem hstop_118_0 (k : Nat) :
    2^(118+14580*k+0) % 9 ≠ 1 := by
  have hp : 2^14580 % 9=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    9 14580 (118+0) k (by decide) hp
  have he : 118+14580*k+0=(118+0)+14580*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_118_0

theorem hstop_118_1 (k : Nat) :
    2^(118+14580*k+3) % 45 ≠ 17 := by
  have hp : 2^14580 % 45=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    45 14580 (118+3) k (by decide) hp
  have he : 118+14580*k+3=(118+3)+14580*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_118_1

theorem hstop_118_2 (k : Nat) :
    2^(118+14580*k+6) % 3645 ≠ 331 := by
  have hp : 2^14580 % 3645=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    3645 14580 (118+6) k (by decide) hp
  have he : 118+14580*k+6=(118+6)+14580*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_118_2

theorem hstop_246_0 (k : Nat) :
    2^(246+24300*k+0) % 27 ≠ 1 := by
  have hp : 2^24300 % 27=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    27 24300 (246+0) k (by decide) hp
  have he : 246+24300*k+0=(246+0)+24300*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_246_0

theorem hstop_246_1 (k : Nat) :
    2^(246+24300*k+5) % 243 ≠ 149 := by
  have hp : 2^24300 % 243=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    243 24300 (246+5) k (by decide) hp
  have he : 246+24300*k+5=(246+5)+24300*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_246_1

theorem hstop_246_2 (k : Nat) :
    2^(246+24300*k+3) % 1215 ≠ 17 := by
  have hp : 2^24300 % 1215=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    1215 24300 (246+3) k (by decide) hp
  have he : 246+24300*k+3=(246+3)+24300*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_246_2

theorem hstop_246_3 (k : Nat) :
    2^(246+24300*k+8) % 6075 ≠ 1759 := by
  have hp : 2^24300 % 6075=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    6075 24300 (246+8) k (by decide) hp
  have he : 246+24300*k+8=(246+8)+24300*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_246_3

theorem hstop_246_4 (k : Nat) :
    2^(246+24300*k+6) % 2025 ≠ 271 := by
  have hp : 2^24300 % 2025=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    2025 24300 (246+6) k (by decide) hp
  have he : 246+24300*k+6=(246+6)+24300*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_246_4

theorem hstop_558_0 (k : Nat) :
    2^(558+8100*k+0) % 81 ≠ 1 := by
  have hp : 2^8100 % 81=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    81 8100 (558+0) k (by decide) hp
  have he : 558+8100*k+0=(558+0)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_558_0

theorem hstop_558_1 (k : Nat) :
    2^(558+8100*k+5) % 405 ≠ 113 := by
  have hp : 2^8100 % 405=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    405 8100 (558+5) k (by decide) hp
  have he : 558+8100*k+5=(558+5)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_558_1

theorem hstop_558_2 (k : Nat) :
    2^(558+8100*k+7) % 2025 ≠ 857 := by
  have hp : 2^8100 % 2025=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    2025 8100 (558+7) k (by decide) hp
  have he : 558+8100*k+7=(558+7)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_558_2

theorem hstop_558_3 (k : Nat) :
    2^(558+8100*k+3) % 135 ≠ 17 := by
  have hp : 2^8100 % 135=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    135 8100 (558+3) k (by decide) hp
  have he : 558+8100*k+3=(558+3)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_558_3

theorem hstop_846_0 (k : Nat) :
    2^(846+8100*k+0) % 81 ≠ 1 := by
  have hp : 2^8100 % 81=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    81 8100 (846+0) k (by decide) hp
  have he : 846+8100*k+0=(846+0)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_846_0

theorem hstop_846_1 (k : Nat) :
    2^(846+8100*k+5) % 405 ≠ 113 := by
  have hp : 2^8100 % 405=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    405 8100 (846+5) k (by decide) hp
  have he : 846+8100*k+5=(846+5)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_846_1

theorem hstop_846_2 (k : Nat) :
    2^(846+8100*k+11) % 26325 ≠ 19922 := by
  have hp : 2^8100 % 26325=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    26325 8100 (846+11) k (by decide) hp
  have he : 846+8100*k+11=(846+11)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_846_2

theorem hstop_846_3 (k : Nat) :
    2^(846+8100*k+3) % 135 ≠ 17 := by
  have hp : 2^8100 % 135=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    135 8100 (846+3) k (by decide) hp
  have he : 846+8100*k+3=(846+3)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_846_3

theorem hstop_846_4 (k : Nat) :
    2^(846+8100*k+6) % 675 ≠ 271 := by
  have hp : 2^8100 % 675=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    675 8100 (846+6) k (by decide) hp
  have he : 846+8100*k+6=(846+6)+8100*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_846_4

theorem hstop_702_0 (k : Nat) :
    2^(702+11340*k+0) % 243 ≠ 1 := by
  have hp : 2^11340 % 243=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    243 11340 (702+0) k (by decide) hp
  have he : 702+11340*k+0=(702+0)+11340*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_702_0

theorem hstop_702_1 (k : Nat) :
    2^(702+11340*k+5) % 1215 ≠ 113 := by
  have hp : 2^11340 % 1215=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    1215 11340 (702+5) k (by decide) hp
  have he : 702+11340*k+5=(702+5)+11340*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_702_1

theorem hstop_702_2 (k : Nat) :
    2^(702+11340*k+3) % 135 ≠ 17 := by
  have hp : 2^11340 % 135=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    135 11340 (702+3) k (by decide) hp
  have he : 702+11340*k+3=(702+3)+11340*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_702_2

theorem hstop_702_3 (k : Nat) :
    2^(702+11340*k+7) % 1215 ≠ 857 := by
  have hp : 2^11340 % 1215=1 := by decide
  have hr := SheepIndependentHBound.pow_mod_period
    1215 11340 (702+7) k (by decide) hp
  have he : 702+11340*k+7=(702+7)+11340*k := by omega
  rw [he, hr]
  decide
#print axioms hstop_702_3

end SheepFiveHStop
