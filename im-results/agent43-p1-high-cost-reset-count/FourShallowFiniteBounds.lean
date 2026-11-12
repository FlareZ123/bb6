import ThreeShallowFiniteBounds

namespace BB6.Agent43FourShallowFinite

open BB6.Agent43TwoShallowFinite
open BB6.Agent43ThreeShallowFinite

/-- If the final depth-two run has length at least three, the fourth
successive source numerator must be divisible by its shallow factor times
512. -/
def fourthOverflow (n s u v w t1 t2 t3 t4 : Nat) : Bool := Id.run do
  let P := 2^n
  let D := 14*n+92
  let q := 8^s
  if P%q != 0 || D%q != 0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let (gamma,C3,L3,O3) := triple t3
  let (delta,C4,L4,O4) := triple t4
  let T1 := n+6+3*s
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int)
  if N1 % ((2:Int)^alpha) != 0 then return false
  let I1 := N1 / ((2:Int)^alpha)
  if I1 % ((8:Int)^u) != 0 then return false
  let N2 : Int := I1/((8:Int)^u)-(C2:Int)*(P:Int)+
    (L2:Int)*(T1+alpha+3*u:Int)-(O2:Int)
  if N2 % ((2:Int)^beta) != 0 then return false
  let I2 := N2 / ((2:Int)^beta)
  if I2 % ((8:Int)^v) != 0 then return false
  let N3 : Int := I2/((8:Int)^v)-(C3:Int)*(P:Int)+
    (L3:Int)*(T1+alpha+3*u+beta+3*v:Int)-(O3:Int)
  if N3 % ((2:Int)^gamma) != 0 then return false
  let I3 := N3 / ((2:Int)^gamma)
  if I3 % ((8:Int)^w) != 0 then return false
  let N4 : Int := I3/((8:Int)^w)-(C4:Int)*(P:Int)+
    (L4:Int)*(T1+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)
  return N4 % ((2:Int)^delta*512) == 0

/-- Exact scalar terminal equality after four shallow transitions and five
arbitrary depth-two runs. -/
def fourBad (n s u v w r t1 t2 t3 t4 : Nat) : Bool := Id.run do
  let q := 8^s
  let P := 2^n
  let D := 14*n+92
  if P%q != 0 || D%q != 0 then return false
  let p := P/q
  let d := D/q
  let (alpha,C1,L1,O1) := triple t1
  let (beta,C2,L2,O2) := triple t2
  let (gamma,C3,L3,O3) := triple t3
  let (delta,C4,L4,O4) := triple t4
  let A1 := 2^alpha*8^u
  let A2 := 2^beta*8^v
  let A3 := 2^gamma*8^w
  let A4 := 2^delta*8^r
  let T1 := n+6+3*s
  let T2 := T1+alpha+3*u
  let T3 := T2+beta+3*v
  let T4 := T3+gamma+3*w
  let T5 := T4+delta+3*r
  let R1 := L1*T1-O1-d
  let R2 := L2*T2-O2
  let R3 := L3*T3-O3
  let R4 := L4*T4-O4
  let E := 112*T5-384
  let K := C1*q+C2*q*A1+C3*q*A1*A2+C4*q*A1*A2*A3-98
  return K*p == A1*(A2*(A3*(A4*E+R4)+R3)+R2)+R1

set_option maxRecDepth 4096
set_option maxHeartbeats 80000000

theorem four_first_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ t : Fin 2,
      BB6.Agent43TwoShallowFinite.firstOverflow (n.val+14) s.val t.val = false := by decide

theorem four_second_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2,
      BB6.Agent43TwoShallowFinite.secondOverflow
        (n.val+14) s.val u.val t1.val t2.val = false := by decide

theorem four_third_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3,
      ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2,
      BB6.Agent43ThreeShallowFinite.thirdOverflow
        (n.val+14) s.val u.val v.val t1.val t2.val t3.val = false := by decide

theorem four_fourth_overflow_false_14_21 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+14) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_22_29 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+22) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_30_37 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+30) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_38_45 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+38) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_46_53 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+46) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_54_61 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+54) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_62_69 :
    ∀ n : Fin 8, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+62) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_70_75 :
    ∀ n : Fin 6, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+70) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by decide

theorem four_fourth_overflow_false_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourthOverflow (n.val+14) s.val u.val v.val w.val t1.val t2.val t3.val t4.val = false := by
  intro n s u v w t1 t2 t3 t4
  by_cases h0 : n.val < 8
  · let n' : Fin 8 := ⟨n.val, by omega⟩
    have heq : n.val+14=n'.val+14 := by simp [n']
    simpa [heq] using four_fourth_overflow_false_14_21 n' s u v w t1 t2 t3 t4
  · by_cases h1 : n.val < 16
    · let n' : Fin 8 := ⟨n.val-8, by omega⟩
      have heq : n.val+14=n'.val+22 := by omega
      simpa [heq] using four_fourth_overflow_false_22_29 n' s u v w t1 t2 t3 t4
    · by_cases h2 : n.val < 24
      · let n' : Fin 8 := ⟨n.val-16, by omega⟩
        have heq : n.val+14=n'.val+30 := by omega
        simpa [heq] using four_fourth_overflow_false_30_37 n' s u v w t1 t2 t3 t4
      · by_cases h3 : n.val < 32
        · let n' : Fin 8 := ⟨n.val-24, by omega⟩
          have heq : n.val+14=n'.val+38 := by omega
          simpa [heq] using four_fourth_overflow_false_38_45 n' s u v w t1 t2 t3 t4
        · by_cases h4 : n.val < 40
          · let n' : Fin 8 := ⟨n.val-32, by omega⟩
            have heq : n.val+14=n'.val+46 := by omega
            simpa [heq] using four_fourth_overflow_false_46_53 n' s u v w t1 t2 t3 t4
          · by_cases h5 : n.val < 48
            · let n' : Fin 8 := ⟨n.val-40, by omega⟩
              have heq : n.val+14=n'.val+54 := by omega
              simpa [heq] using four_fourth_overflow_false_54_61 n' s u v w t1 t2 t3 t4
            · by_cases h6 : n.val < 56
              · let n' : Fin 8 := ⟨n.val-48, by omega⟩
                have heq : n.val+14=n'.val+62 := by omega
                simpa [heq] using four_fourth_overflow_false_62_69 n' s u v w t1 t2 t3 t4
              · let n' : Fin 6 := ⟨n.val-56, by omega⟩
                  have heq : n.val+14=n'.val+70 := by omega
                  simpa [heq] using four_fourth_overflow_false_70_75 n' s u v w t1 t2 t3 t4

theorem no_four_small_bad_14_17 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+14) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_18_21 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+18) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_22_25 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+22) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_26_29 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+26) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_30_33 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+30) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_34_37 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+34) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_38_41 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+38) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_42_45 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+42) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_46_49 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+46) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_50_53 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+50) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_54_57 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+54) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_58_61 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+58) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_62_65 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+62) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_66_69 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+66) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_70_73 :
    ∀ n : Fin 4, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+70) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_74_75 :
    ∀ n : Fin 2, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+74) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by decide

theorem no_four_small_bad_76 :
    ∀ n : Fin 62, ∀ s : Fin 4, ∀ u : Fin 3, ∀ v : Fin 3, ∀ w : Fin 3, ∀ r : Fin 3, ∀ t1 : Fin 2, ∀ t2 : Fin 2, ∀ t3 : Fin 2, ∀ t4 : Fin 2,
      fourBad (n.val+14) s.val u.val v.val w.val r.val t1.val t2.val t3.val t4.val = false := by
  intro n s u v w r t1 t2 t3 t4
  by_cases h0 : n.val < 4
  · let n' : Fin 4 := ⟨n.val, by omega⟩
    have heq : n.val+14=n'.val+14 := by simp [n']
    simpa [heq] using no_four_small_bad_14_17 n' s u v w r t1 t2 t3 t4
  · by_cases h1 : n.val < 8
    · let n' : Fin 4 := ⟨n.val-4, by omega⟩
      have heq : n.val+14=n'.val+18 := by omega
      simpa [heq] using no_four_small_bad_18_21 n' s u v w r t1 t2 t3 t4
    · by_cases h2 : n.val < 12
      · let n' : Fin 4 := ⟨n.val-8, by omega⟩
        have heq : n.val+14=n'.val+22 := by omega
        simpa [heq] using no_four_small_bad_22_25 n' s u v w r t1 t2 t3 t4
      · by_cases h3 : n.val < 16
        · let n' : Fin 4 := ⟨n.val-12, by omega⟩
          have heq : n.val+14=n'.val+26 := by omega
          simpa [heq] using no_four_small_bad_26_29 n' s u v w r t1 t2 t3 t4
        · by_cases h4 : n.val < 20
          · let n' : Fin 4 := ⟨n.val-16, by omega⟩
            have heq : n.val+14=n'.val+30 := by omega
            simpa [heq] using no_four_small_bad_30_33 n' s u v w r t1 t2 t3 t4
          · by_cases h5 : n.val < 24
            · let n' : Fin 4 := ⟨n.val-20, by omega⟩
              have heq : n.val+14=n'.val+34 := by omega
              simpa [heq] using no_four_small_bad_34_37 n' s u v w r t1 t2 t3 t4
            · by_cases h6 : n.val < 28
              · let n' : Fin 4 := ⟨n.val-24, by omega⟩
                have heq : n.val+14=n'.val+38 := by omega
                simpa [heq] using no_four_small_bad_38_41 n' s u v w r t1 t2 t3 t4
              · by_cases h7 : n.val < 32
                · let n' : Fin 4 := ⟨n.val-28, by omega⟩
                  have heq : n.val+14=n'.val+42 := by omega
                  simpa [heq] using no_four_small_bad_42_45 n' s u v w r t1 t2 t3 t4
                · by_cases h8 : n.val < 36
                  · let n' : Fin 4 := ⟨n.val-32, by omega⟩
                    have heq : n.val+14=n'.val+46 := by omega
                    simpa [heq] using no_four_small_bad_46_49 n' s u v w r t1 t2 t3 t4
                  · by_cases h9 : n.val < 40
                    · let n' : Fin 4 := ⟨n.val-36, by omega⟩
                      have heq : n.val+14=n'.val+50 := by omega
                      simpa [heq] using no_four_small_bad_50_53 n' s u v w r t1 t2 t3 t4
                    · by_cases h10 : n.val < 44
                      · let n' : Fin 4 := ⟨n.val-40, by omega⟩
                        have heq : n.val+14=n'.val+54 := by omega
                        simpa [heq] using no_four_small_bad_54_57 n' s u v w r t1 t2 t3 t4
                      · by_cases h11 : n.val < 48
                        · let n' : Fin 4 := ⟨n.val-44, by omega⟩
                          have heq : n.val+14=n'.val+58 := by omega
                          simpa [heq] using no_four_small_bad_58_61 n' s u v w r t1 t2 t3 t4
                        · by_cases h12 : n.val < 52
                          · let n' : Fin 4 := ⟨n.val-48, by omega⟩
                            have heq : n.val+14=n'.val+62 := by omega
                            simpa [heq] using no_four_small_bad_62_65 n' s u v w r t1 t2 t3 t4
                          · by_cases h13 : n.val < 56
                            · let n' : Fin 4 := ⟨n.val-52, by omega⟩
                              have heq : n.val+14=n'.val+66 := by omega
                              simpa [heq] using no_four_small_bad_66_69 n' s u v w r t1 t2 t3 t4
                            · by_cases h14 : n.val < 60
                              · let n' : Fin 4 := ⟨n.val-56, by omega⟩
                                have heq : n.val+14=n'.val+70 := by omega
                                simpa [heq] using no_four_small_bad_70_73 n' s u v w r t1 t2 t3 t4
                              · let n' : Fin 2 := ⟨n.val-60, by omega⟩
                                  have heq : n.val+14=n'.val+74 := by omega
                                  simpa [heq] using no_four_small_bad_74_75 n' s u v w r t1 t2 t3 t4

#print axioms four_first_overflow_false_76
#print axioms four_second_overflow_false_76
#print axioms four_third_overflow_false_76
#print axioms four_fourth_overflow_false_76
#print axioms no_four_small_bad_76

end BB6.Agent43FourShallowFinite
