import Box33D17V21DoubleInit

namespace BB6.Agent13.Box33D17V21Double
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

-- Exact short prefix, compressed into verified sweep and turnaround rules.
theorem initSmall (b : Bool) : Reaches b (A z z) (X 8 2 4) := by
  have h0 : run b (10+extra b) (A z z) = some (A (ones 5 z) z) := by
    simpa only [L,zeros_z] using turn3 b z z
  have p0 := reach b h0
  have h1 : run b 16 (A (ones 5 z) z) = some (A (ones 1 z) (zeros 2 (ones 4 z))) := by
    exact lsweepBlank b 2 (ones 1 z)
  have p1 := trans b p0 (reach b h1)
  have h2 : run b 6 (A (ones 1 z) (zeros 2 (ones 4 z))) = some (A z (zeros 2 (ones 2 (zeros 1 (ones 5 z))))) := by
    simpa only [L,zeros_z] using odd b z (ones 4 z)
  have p2 := trans b p1 (reach b h2)
  have h3 : run b (10+extra b) (A z (zeros 2 (ones 2 (zeros 1 (ones 5 z))))) = some (A (ones 5 z) (ones 2 (zeros 1 (ones 5 z)))) := by
    simpa only [L,zeros_z] using turn3 b z (ones 2 (zeros 1 (ones 5 z)))
  have p3 := trans b p2 (reach b h3)
  have h4 : run b 2 (A (ones 5 z) (ones 2 (zeros 1 (ones 5 z)))) = some (A (ones 7 z) (zeros 1 (ones 5 z))) := by
    exact asweep b 2 (ones 5 z) (zeros 1 (ones 5 z))
  have p4 := trans b p3 (reach b h4)
  have h5 : run b 1 (A (ones 7 z) (zeros 1 (ones 5 z))) = some (B (ones 8 z) (ones 5 z)) := by
    simpa only [L,zeros_z] using enterB b (ones 7 z) (ones 5 z)
  have p5 := trans b p4 (reach b h5)
  have h6 : run b 5 (B (ones 8 z) (ones 5 z)) = some (B (zeros 5 (ones 8 z)) z) := by
    exact bsweep b 5 (ones 8 z) z
  have p6 := trans b p5 (reach b h6)
  have h7 : run b 2 (B (zeros 5 (ones 8 z)) z) = some (A (zeros 3 (ones 8 z)) (zeros 2 (ones 1 z))) := by
    simpa only [L,zeros_z] using exitB b (zeros 3 (ones 8 z)) z
  have p7 := trans b p6 (reach b h7)
  have h8 : run b (10+extra b) (A (zeros 3 (ones 8 z)) (zeros 2 (ones 1 z))) = some (A (ones 13 z) (ones 1 z)) := by
    simpa only [L,zeros_z] using turn3 b (ones 8 z) (ones 1 z)
  have p8 := trans b p7 (reach b h8)
  have h9 : run b 1 (A (ones 13 z) (ones 1 z)) = some (A (ones 14 z) z) := by
    exact asweep b 1 (ones 13 z) z
  have p9 := trans b p8 (reach b h9)
  have h10 : run b 56 (A (ones 14 z) z) = some (A z (zeros 2 (ones 14 z))) := by
    exact lsweepBlank b 7 z
  have p10 := trans b p9 (reach b h10)
  have h11 : run b (10+extra b) (A z (zeros 2 (ones 14 z))) = some (A (ones 5 z) (ones 14 z)) := by
    simpa only [L,zeros_z] using turn3 b z (ones 14 z)
  have p11 := trans b p10 (reach b h11)
  have h12 : run b 14 (A (ones 5 z) (ones 14 z)) = some (A (ones 19 z) z) := by
    exact asweep b 14 (ones 5 z) z
  have p12 := trans b p11 (reach b h12)
  have h13 : run b 72 (A (ones 19 z) z) = some (A (ones 1 z) (zeros 2 (ones 18 z))) := by
    exact lsweepBlank b 9 (ones 1 z)
  have p13 := trans b p12 (reach b h13)
  have h14 : run b 6 (A (ones 1 z) (zeros 2 (ones 18 z))) = some (A z (zeros 2 (ones 2 (zeros 1 (ones 19 z))))) := by
    simpa only [L,zeros_z] using odd b z (ones 18 z)
  have p14 := trans b p13 (reach b h14)
  have h15 : run b (10+extra b) (A z (zeros 2 (ones 2 (zeros 1 (ones 19 z))))) = some (A (ones 5 z) (ones 2 (zeros 1 (ones 19 z)))) := by
    simpa only [L,zeros_z] using turn3 b z (ones 2 (zeros 1 (ones 19 z)))
  have p15 := trans b p14 (reach b h15)
  have h16 : run b 2 (A (ones 5 z) (ones 2 (zeros 1 (ones 19 z)))) = some (A (ones 7 z) (zeros 1 (ones 19 z))) := by
    exact asweep b 2 (ones 5 z) (zeros 1 (ones 19 z))
  have p16 := trans b p15 (reach b h16)
  have h17 : run b 1 (A (ones 7 z) (zeros 1 (ones 19 z))) = some (B (ones 8 z) (ones 19 z)) := by
    simpa only [L,zeros_z] using enterB b (ones 7 z) (ones 19 z)
  have p17 := trans b p16 (reach b h17)
  have h18 : run b 19 (B (ones 8 z) (ones 19 z)) = some (B (zeros 19 (ones 8 z)) z) := by
    exact bsweep b 19 (ones 8 z) z
  have p18 := trans b p17 (reach b h18)
  have h19 : run b 2 (B (zeros 19 (ones 8 z)) z) = some (A (zeros 17 (ones 8 z)) (zeros 2 (ones 1 z))) := by
    simpa only [L,zeros_z] using exitB b (zeros 17 (ones 8 z)) z
  have p19 := trans b p18 (reach b h19)
  have h20 : run b (10+extra b) (A (zeros 17 (ones 8 z)) (zeros 2 (ones 1 z))) = some (A (ones 5 (zeros 14 (ones 8 z))) (ones 1 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 14 (ones 8 z)) (ones 1 z)
  have p20 := trans b p19 (reach b h20)
  have h21 : run b 1 (A (ones 5 (zeros 14 (ones 8 z))) (ones 1 z)) = some (A (ones 6 (zeros 14 (ones 8 z))) z) := by
    exact asweep b 1 (ones 5 (zeros 14 (ones 8 z))) z
  have p21 := trans b p20 (reach b h21)
  have h22 : run b 24 (A (ones 6 (zeros 14 (ones 8 z))) z) = some (A (zeros 14 (ones 8 z)) (zeros 2 (ones 6 z))) := by
    exact lsweepBlank b 3 (zeros 14 (ones 8 z))
  have p22 := trans b p21 (reach b h22)
  have h23 : run b (10+extra b) (A (zeros 14 (ones 8 z)) (zeros 2 (ones 6 z))) = some (A (ones 5 (zeros 11 (ones 8 z))) (ones 6 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 11 (ones 8 z)) (ones 6 z)
  have p23 := trans b p22 (reach b h23)
  have h24 : run b 6 (A (ones 5 (zeros 11 (ones 8 z))) (ones 6 z)) = some (A (ones 11 (zeros 11 (ones 8 z))) z) := by
    exact asweep b 6 (ones 5 (zeros 11 (ones 8 z))) z
  have p24 := trans b p23 (reach b h24)
  have h25 : run b 40 (A (ones 11 (zeros 11 (ones 8 z))) z) = some (A (ones 1 (zeros 11 (ones 8 z))) (zeros 2 (ones 10 z))) := by
    exact lsweepBlank b 5 (ones 1 (zeros 11 (ones 8 z)))
  have p25 := trans b p24 (reach b h25)
  have h26 : run b 6 (A (ones 1 (zeros 11 (ones 8 z))) (zeros 2 (ones 10 z))) = some (A (zeros 8 (ones 8 z)) (zeros 2 (ones 2 (zeros 1 (ones 11 z))))) := by
    simpa only [L,zeros_z] using odd b (zeros 8 (ones 8 z)) (ones 10 z)
  have p26 := trans b p25 (reach b h26)
  have h27 : run b (10+extra b) (A (zeros 8 (ones 8 z)) (zeros 2 (ones 2 (zeros 1 (ones 11 z))))) = some (A (ones 5 (zeros 5 (ones 8 z))) (ones 2 (zeros 1 (ones 11 z)))) := by
    simpa only [L,zeros_z] using turn3 b (zeros 5 (ones 8 z)) (ones 2 (zeros 1 (ones 11 z)))
  have p27 := trans b p26 (reach b h27)
  have h28 : run b 2 (A (ones 5 (zeros 5 (ones 8 z))) (ones 2 (zeros 1 (ones 11 z)))) = some (A (ones 7 (zeros 5 (ones 8 z))) (zeros 1 (ones 11 z))) := by
    exact asweep b 2 (ones 5 (zeros 5 (ones 8 z))) (zeros 1 (ones 11 z))
  have p28 := trans b p27 (reach b h28)
  have h29 : run b 1 (A (ones 7 (zeros 5 (ones 8 z))) (zeros 1 (ones 11 z))) = some (B (ones 8 (zeros 5 (ones 8 z))) (ones 11 z)) := by
    simpa only [L,zeros_z] using enterB b (ones 7 (zeros 5 (ones 8 z))) (ones 11 z)
  have p29 := trans b p28 (reach b h29)
  have h30 : run b 11 (B (ones 8 (zeros 5 (ones 8 z))) (ones 11 z)) = some (B (zeros 11 (ones 8 (zeros 5 (ones 8 z)))) z) := by
    exact bsweep b 11 (ones 8 (zeros 5 (ones 8 z))) z
  have p30 := trans b p29 (reach b h30)
  have h31 : run b 2 (B (zeros 11 (ones 8 (zeros 5 (ones 8 z)))) z) = some (A (zeros 9 (ones 8 (zeros 5 (ones 8 z)))) (zeros 2 (ones 1 z))) := by
    simpa only [L,zeros_z] using exitB b (zeros 9 (ones 8 (zeros 5 (ones 8 z)))) z
  have p31 := trans b p30 (reach b h31)
  have h32 : run b (10+extra b) (A (zeros 9 (ones 8 (zeros 5 (ones 8 z)))) (zeros 2 (ones 1 z))) = some (A (ones 5 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))) (ones 1 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 6 (ones 8 (zeros 5 (ones 8 z)))) (ones 1 z)
  have p32 := trans b p31 (reach b h32)
  have h33 : run b 1 (A (ones 5 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))) (ones 1 z)) = some (A (ones 6 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))) z) := by
    exact asweep b 1 (ones 5 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))) z
  have p33 := trans b p32 (reach b h33)
  have h34 : run b 24 (A (ones 6 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))) z) = some (A (zeros 6 (ones 8 (zeros 5 (ones 8 z)))) (zeros 2 (ones 6 z))) := by
    exact lsweepBlank b 3 (zeros 6 (ones 8 (zeros 5 (ones 8 z))))
  have p34 := trans b p33 (reach b h34)
  have h35 : run b (10+extra b) (A (zeros 6 (ones 8 (zeros 5 (ones 8 z)))) (zeros 2 (ones 6 z))) = some (A (ones 5 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) (ones 6 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 3 (ones 8 (zeros 5 (ones 8 z)))) (ones 6 z)
  have p35 := trans b p34 (reach b h35)
  have h36 : run b 6 (A (ones 5 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) (ones 6 z)) = some (A (ones 11 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) z) := by
    exact asweep b 6 (ones 5 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) z
  have p36 := trans b p35 (reach b h36)
  have h37 : run b 40 (A (ones 11 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) z) = some (A (ones 1 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) (zeros 2 (ones 10 z))) := by
    exact lsweepBlank b 5 (ones 1 (zeros 3 (ones 8 (zeros 5 (ones 8 z)))))
  have p37 := trans b p36 (reach b h37)
  have h38 : run b 6 (A (ones 1 (zeros 3 (ones 8 (zeros 5 (ones 8 z))))) (zeros 2 (ones 10 z))) = some (A (ones 8 (zeros 5 (ones 8 z))) (zeros 2 (ones 2 (zeros 1 (ones 11 z))))) := by
    simpa only [L,zeros_z] using odd b (ones 8 (zeros 5 (ones 8 z))) (ones 10 z)
  have p38 := trans b p37 (reach b h38)
  have h39 : run b 32 (A (ones 8 (zeros 5 (ones 8 z))) (zeros 2 (ones 2 (zeros 1 (ones 11 z))))) = some (A (zeros 5 (ones 8 z)) (zeros 2 (ones 10 (zeros 1 (ones 11 z))))) := by
    exact lsweep b 4 (zeros 5 (ones 8 z)) (ones 2 (zeros 1 (ones 11 z)))
  have p39 := trans b p38 (reach b h39)
  have h40 : run b (10+extra b) (A (zeros 5 (ones 8 z)) (zeros 2 (ones 10 (zeros 1 (ones 11 z))))) = some (A (ones 5 (zeros 2 (ones 8 z))) (ones 10 (zeros 1 (ones 11 z)))) := by
    simpa only [L,zeros_z] using turn3 b (zeros 2 (ones 8 z)) (ones 10 (zeros 1 (ones 11 z)))
  have p40 := trans b p39 (reach b h40)
  have h41 : run b 10 (A (ones 5 (zeros 2 (ones 8 z))) (ones 10 (zeros 1 (ones 11 z)))) = some (A (ones 15 (zeros 2 (ones 8 z))) (zeros 1 (ones 11 z))) := by
    exact asweep b 10 (ones 5 (zeros 2 (ones 8 z))) (zeros 1 (ones 11 z))
  have p41 := trans b p40 (reach b h41)
  have h42 : run b 1 (A (ones 15 (zeros 2 (ones 8 z))) (zeros 1 (ones 11 z))) = some (B (ones 16 (zeros 2 (ones 8 z))) (ones 11 z)) := by
    simpa only [L,zeros_z] using enterB b (ones 15 (zeros 2 (ones 8 z))) (ones 11 z)
  have p42 := trans b p41 (reach b h42)
  have h43 : run b 11 (B (ones 16 (zeros 2 (ones 8 z))) (ones 11 z)) = some (B (zeros 11 (ones 16 (zeros 2 (ones 8 z)))) z) := by
    exact bsweep b 11 (ones 16 (zeros 2 (ones 8 z))) z
  have p43 := trans b p42 (reach b h43)
  have h44 : run b 2 (B (zeros 11 (ones 16 (zeros 2 (ones 8 z)))) z) = some (A (zeros 9 (ones 16 (zeros 2 (ones 8 z)))) (zeros 2 (ones 1 z))) := by
    simpa only [L,zeros_z] using exitB b (zeros 9 (ones 16 (zeros 2 (ones 8 z)))) z
  have p44 := trans b p43 (reach b h44)
  have h45 : run b (10+extra b) (A (zeros 9 (ones 16 (zeros 2 (ones 8 z)))) (zeros 2 (ones 1 z))) = some (A (ones 5 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))) (ones 1 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 6 (ones 16 (zeros 2 (ones 8 z)))) (ones 1 z)
  have p45 := trans b p44 (reach b h45)
  have h46 : run b 1 (A (ones 5 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))) (ones 1 z)) = some (A (ones 6 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))) z) := by
    exact asweep b 1 (ones 5 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))) z
  have p46 := trans b p45 (reach b h46)
  have h47 : run b 24 (A (ones 6 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))) z) = some (A (zeros 6 (ones 16 (zeros 2 (ones 8 z)))) (zeros 2 (ones 6 z))) := by
    exact lsweepBlank b 3 (zeros 6 (ones 16 (zeros 2 (ones 8 z))))
  have p47 := trans b p46 (reach b h47)
  have h48 : run b (10+extra b) (A (zeros 6 (ones 16 (zeros 2 (ones 8 z)))) (zeros 2 (ones 6 z))) = some (A (ones 5 (zeros 3 (ones 16 (zeros 2 (ones 8 z))))) (ones 6 z)) := by
    simpa only [L,zeros_z] using turn3 b (zeros 3 (ones 16 (zeros 2 (ones 8 z)))) (ones 6 z)
  have p48 := trans b p47 (reach b h48)
  have h49 : run b 6 (A (ones 5 (zeros 3 (ones 16 (zeros 2 (ones 8 z))))) (ones 6 z)) = some (A (ones 11 (zeros 3 (ones 16 (zeros 2 (ones 8 z))))) z) := by
    exact asweep b 6 (ones 5 (zeros 3 (ones 16 (zeros 2 (ones 8 z))))) z
  have p49 := trans b p48 (reach b h49)
  exact p49

theorem initLarge (b : Bool) : Reaches b (A z z) (phase 153) := by
  have h0 := trans b (initSmall b) (exitTwo b 7 3)
  have h1 := trans b h0 (enterP b 8 7)
  have h2 := trans b h1 (advanceMany b 2 12 2 7)
  have h3 := trans b h2 (exitTwo b 19 6)
  have h4 := trans b h3 (enterP b 32 10)
  have h5 := trans b h4 (advanceMany b 10 12 2 10)
  have h6 := trans b h5 (exitTwo b 51 9)
  have h7 := trans b h6 (enterP b 96 13)
  have h8 := trans b h7 (advanceMany b 32 12 0 13)
  have he : X 140 0 13 = phase 153 := by
    unfold X phase
    rw [show zeros 0 (ones (2*13) z)=ones (2*13) z by rfl]
    rw [←ones_add (2*140) (2*13) z]
    rfl
  exact he ▸ h8

def blank : Config := A z z
theorem never_blank (b : Bool) (n : Nat) : run b n blank ≠ none := by
  obtain ⟨t,ht⟩ := initLarge b
  change run b t blank = some (phase 153) at ht
  intro h
  by_cases hn : n ≤ t
  · rw [←show n+(t-n)=t by omega,run_add,h] at ht
    contradiction
  · rw [←show t+(n-t)=n by omega,run_add,ht,Option.bind_some] at h
    exact never_phase b _ 153 h

#print axioms never_blank
end BB6.Agent13.Box33D17V21Double
