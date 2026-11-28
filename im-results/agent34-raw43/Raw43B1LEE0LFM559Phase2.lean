import Raw43B1LEE0LFM559Phase1
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent34Raw43B1LEE0LFM559Phase2
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent34Raw43B1LEE0LFM559Phase1

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,rep,ih,List.append_assoc]

theorem rep_double (P : List Bool) (n : Nat) : rep (P++P) n = rep P (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add]
    simp [rep,List.append_assoc]

theorem rep_succ_front (P : List Bool) (n : Nat) : rep P (n+1) = P ++ rep P n := by
  rw [show n+1 = Nat.succ n by omega]
  rfl

theorem turn16 : ∀ R,
    run0 table 16 ⟨4,[],[false,false,true,true,false,true,true,false]++R⟩ =
      some ⟨4,[],[false,false,false,false,false,true,false,true,true,false]++R⟩ := by
  intro R; rfl

theorem fixed19a : ∀ R,
    run0 table 19 ⟨4,[],[false,false,false,false,false,true,false,true,true,false]++R⟩ =
      some ⟨5,[true,true,true,false,false,true,false,true,true,false,true],[false]++R⟩ := by
  intro R; rfl

theorem sweep6a : ∀ L R,
    run0 table 6 ⟨5,[true,true]++L,[false,true]++[true,true]++R⟩ =
      some ⟨5,[true,true]++[false,true]++L,[false,true]++R⟩ := by
  intro L R; rfl

theorem sweep6b : ∀ L R,
    run0 table 6 ⟨5,[true]++L,[false]++[true,true,false,true,true,false]++R⟩ =
      some ⟨5,[true]++[true,true,false,true,true,false]++L,[false]++R⟩ := by
  intro L R; rfl

theorem fixed9a : ∀ L,
    run0 table 9 ⟨5,[true]++L,[false,false,true,true,false,false,true,true]⟩ =
      some ⟨4,[true,true,true,false]++L,[true,false,false,true,true]⟩ := by
  intro L; rfl

theorem sweep30e : ∀ L R,
    run0 table 30 ⟨4,[true,true,true,false]++[true,true,false,true,true,false]++L,R⟩ =
      some ⟨4,[true,true,true,false]++L,[true,true,false,true,true,false]++R⟩ := by
  intro L R; rfl

theorem step1e : ∀ L R,
    run0 table 1 ⟨4,[true]++L,R⟩ = some ⟨4,L,[false]++R⟩ := by
  intro L R; rfl

theorem sweep14e : ∀ L R,
    run0 table 14 ⟨4,[true,true]++[false,true]++L,R⟩ =
      some ⟨4,[true,true]++L,[true,true]++R⟩ := by
  intro L R; rfl

theorem fixed19b : ∀ R,
    run0 table 19 ⟨4,[true,true,true,false,false,true,false,true,true,false,true],[true]++R⟩ =
      some ⟨5,[true,true,false,true,true,false,true,true,false,true],[false,true]++R⟩ := by
  intro R; rfl

theorem fixed9b : ∀ L,
    run0 table 9 ⟨5,[true]++L,[false,true,true,false,true,false,false,true,true]⟩ =
      some ⟨4,[true,true,true,true,false,true,true,false]++L,[true,true]⟩ := by
  intro L; rfl

theorem fixed5 : ∀ L,
    run0 table 5 ⟨4,[true,true,true,true,false]++L,[true,true]⟩ =
      some ⟨5,L,[false,false,false,false,false,true,true]⟩ := by
  intro L; rfl

def phase2 (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,false,false,false,true,false,true,true,false,true] ++
      rep [true,true] (2*n+1) ++ [true,false] ++
      rep [true,true,false] (4*n+1) ++ [false,true,true,false,false,true,true]⟩

def phase3 (n : Nat) : Z0 :=
  ⟨4,[],
    [false,false,true,true,false,true,true,false,true,true,true,true] ++
      rep [true,true] (2*n+1) ++ [false] ++
      rep [true,true,false] (4*n+3) ++ [false,true,true]⟩

theorem phase1_to_phase2 (n : Nat) : run0 table 16 (phase1 n) = some (phase2 n) := by
  have h := turn16
    ([true,true,true,true] ++ rep [true,true] (2*n) ++ [false] ++
      rep [true,true,false] (4*n+1) ++ [false,true,true,false,false,true,true])
  have hs : rep [true,true] (2*n+1) = [true,true] ++ rep [true,true] (2*n) :=
    rep_succ_front [true,true] (2*n)
  have hr : [true] ++ rep [true,true] (2*n) = rep [true,true] (2*n) ++ [true] := by
    simpa using rotate true [true] (2*n)
  have ho : [true,true,true,true] ++ rep [true,true] (2*n) =
      [true] ++ rep [true,true] (2*n+1) ++ [true] := by
    rw [hs]
    simp only [List.append_assoc]
    rw [← hr]
    rfl
  simpa [phase1,phase2,ho,List.append_assoc] using h

theorem phase2_to_phase3 (n : Nat) :
    run0 table (224*n+260) (phase2 n) = some (phase3 n) := by
  let j := 2*n+1
  let m := 4*n+1
  let sfx : List Bool := [false,true,true,false,false,true,true]
  let tailA : List Bool := [true,false,false,true,false,true,true,false,true]
  let tailC : List Bool := [false,true,true,false,true,true,false,true]
  let tailF : List Bool := [true,false,true,true,false,true,true,false,true]
  let B : List Bool := [true,true,false]
  let Q : List Bool := [true,true,false,true,true,false]
  have hBm : B ++ rep B m = rep Q j := by
    rw [← rep_succ_front B m]
    rw [show m+1=2*j by simp [m,j]; omega]
    rw [← rep_double B j]
    rfl
  have hQ : rep Q j = rep B (2*j) := by
    simpa [Q,B] using rep_double B j
  have hBodd : B ++ rep Q j = rep B (2*j+1) := by
    rw [hQ]
    rw [← rep_succ_front B (2*j)]
  have hrot11 : [true] ++ rep [true,true] j = rep [true,true] j ++ [true] := by
    simpa using rotate true [true] j
  have hrot10 : [true] ++ rep [false,true] j = rep [true,false] j ++ [true] := by
    simpa using rotate true [false] j
  let z1 : Z0 := ⟨5,[true,true]++tailA,
    [false,true] ++ rep [true,true] j ++ [true,false] ++ rep B m ++ sfx⟩
  let z2 : Z0 := ⟨5,[true,true] ++ rep [false,true] j ++ tailA,
    [false] ++ rep Q j ++ sfx⟩
  let z3 : Z0 := ⟨5,[true] ++ rep Q j ++ [true] ++ rep [false,true] j ++ tailA,
    [false] ++ sfx⟩
  let z4 : Z0 := ⟨4,[true,true,true,false] ++ rep Q j ++ [true] ++ rep [false,true] j ++ tailA,
    [true,false,false,true,true]⟩
  let z5 : Z0 := ⟨4,[true,true,true,false] ++ [true] ++ rep [false,true] j ++ tailA,
    rep Q j ++ [true,false,false,true,true]⟩
  let z6 : Z0 := ⟨4,[true,true] ++ rep [false,true] (j+1) ++ tailA,
    [false] ++ rep Q j ++ [true,false,false,true,true]⟩
  let z7 : Z0 := ⟨4,[true,true]++tailA,
    rep [true,true] (j+1) ++ [false] ++ rep Q j ++ [true,false,false,true,true]⟩
  let z8 : Z0 := ⟨5,[true,true]++tailC,
    [false,true] ++ rep [true,true] j ++ [true,false] ++ rep Q j ++ [true,false,false,true,true]⟩
  let z9 : Z0 := ⟨5,[true,true] ++ rep [false,true] j ++ tailC,
    [false] ++ rep Q j ++ [true,true,false] ++ [true,false,false,true,true]⟩
  let z10 : Z0 := ⟨5,[true] ++ rep Q j ++ [true] ++ rep [false,true] j ++ tailC,
    [false,true,true,false,true,false,false,true,true]⟩
  let z11 : Z0 := ⟨4,[true,true,true,true,false,true,true,false] ++ rep Q j ++
      [true] ++ rep [false,true] j ++ tailC,[true,true]⟩
  let z12 : Z0 := ⟨5,rep B (2*j+1) ++ rep [true,false] j ++ tailF,
    [false,false,false,false,false,true,true]⟩
  let z13 : Z0 := ⟨5,rep [true,false] j ++ tailF,
    [false,false,false,false] ++ rep B (2*j+1) ++ [false,true,true]⟩
  let z14 : Z0 := ⟨5,tailF,
    [false,false,false] ++ rep [true,true] j ++ [false] ++ rep B (2*j+1) ++ [false,true,true]⟩
  have h19a : run0 table 19 (phase2 n) = some z1 := by
    have h := fixed19a
      ([true] ++ rep [true,true] j ++ [true,false] ++ rep B m ++ sfx)
    simpa [phase2,z1,j,m,sfx,tailA,B,List.append_assoc] using h
  have h6a : run0 table (6*j) z1 = some z2 := by
    have h := sweepR table 5 [true,true] [false,true] [true,true] [false,true] 6
      sweep6a j tailA ([true,false] ++ rep B m ++ sfx)
    have hR : [false,true] ++ ([true,false] ++ rep B m ++ sfx) = [false] ++ rep Q j ++ sfx := by
      have hc := congrArg (fun x : List Bool => [false] ++ x ++ sfx) hBm
      simpa [B,Q,List.append_assoc] using hc
    rw [hR] at h
    simpa [z1,z2,B,Q,List.append_assoc] using h
  have h6b : run0 table (6*j) z2 = some z3 := by
    have h := sweepR table 5 [true] [false] Q Q 6 sweep6b j
      ([true] ++ rep [false,true] j ++ tailA) sfx
    simpa [z2,z3,Q,List.append_assoc] using h
  have h9a : run0 table 9 z3 = some z4 := by
    have h := fixed9a
      (rep Q j ++ [true] ++ rep [false,true] j ++ tailA)
    simpa [z3,z4,sfx,Q,List.append_assoc] using h
  have h30 : run0 table (30*j) z4 = some z5 := by
    have h := sweepL table 4 [true,true,true,false] [] Q Q 30 sweep30e j
      ([true] ++ rep [false,true] j ++ tailA) [true,false,false,true,true]
    simpa [z4,z5,Q,List.append_assoc] using h
  have h1 : run0 table 1 z5 = some z6 := by
    have h := step1e
      ([true,true,false,true] ++ rep [false,true] j ++ tailA)
      (rep Q j ++ [true,false,false,true,true])
    simpa [z5,z6,Q,rep_succ_front,List.append_assoc] using h
  have h14e : run0 table (14*(j+1)) z6 = some z7 := by
    have h := sweepL table 4 [true,true] [] [false,true] [true,true] 14 sweep14e
      (j+1) tailA ([false] ++ rep Q j ++ [true,false,false,true,true])
    simpa [z6,z7,Q,List.append_assoc] using h
  have h19b : run0 table 19 z7 = some z8 := by
    have h := fixed19b
      ([true] ++ rep [true,true] j ++ [false] ++ rep Q j ++ [true,false,false,true,true])
    have hin : rep [true,true] (j+1) ++ [false] ++ rep Q j ++ [true,false,false,true,true] =
        [true] ++ ([true] ++ rep [true,true] j ++ [false] ++ rep Q j ++ [true,false,false,true,true]) := by
      rw [rep_succ_front]
      rfl
    have hout : [false,true] ++ ([true] ++ rep [true,true] j ++ [false] ++ rep Q j ++ [true,false,false,true,true]) =
        [false,true] ++ rep [true,true] j ++ [true,false] ++ rep Q j ++ [true,false,false,true,true] := by
      have hc := congrArg
        (fun x : List Bool => [false,true] ++ x ++ [false] ++ rep Q j ++ [true,false,false,true,true]) hrot11
      simpa [List.append_assoc] using hc
    rw [← hin] at h
    rw [hout] at h
    simpa [z7,z8,tailA,tailC,Q,List.append_assoc] using h
  have h6a2 : run0 table (6*j) z8 = some z9 := by
    have h := sweepR table 5 [true,true] [false,true] [true,true] [false,true] 6
      sweep6a j tailC ([true,false] ++ rep Q j ++ [true,false,false,true,true])
    have hb : B ++ rep Q j = rep Q j ++ B := by
      rw [hQ]
      simpa [hQ] using (rep_snoc B (2*j)).symm
    have hR : [false,true] ++ ([true,false] ++ rep Q j ++ [true,false,false,true,true]) =
        [false] ++ rep Q j ++ [true,true,false] ++ [true,false,false,true,true] := by
      change [false] ++ (B ++ rep Q j) ++ [true,false,false,true,true] =
        [false] ++ rep Q j ++ B ++ [true,false,false,true,true]
      rw [hb]
      simp only [List.append_assoc]
    rw [hR] at h
    simpa [z8,z9,B,Q,List.append_assoc] using h
  have h6b2 : run0 table (6*j) z9 = some z10 := by
    have h := sweepR table 5 [true] [false] Q Q 6 sweep6b j
      ([true] ++ rep [false,true] j ++ tailC) ([true,true,false] ++ [true,false,false,true,true])
    simpa [z9,z10,Q,List.append_assoc] using h
  have h9b : run0 table 9 z10 = some z11 := by
    have h := fixed9b (rep Q j ++ [true] ++ rep [false,true] j ++ tailC)
    simpa [z10,z11,Q,List.append_assoc] using h
  have h5 : run0 table 5 z11 = some z12 := by
    have h := fixed5
      (B ++ rep Q j ++ [true] ++ rep [false,true] j ++ tailC)
    simpa [z11,z12,B,Q,tailC,tailF,hrot10,hBodd,List.append_assoc] using h
  have h15 : run0 table (15*(2*j+1)) z12 = some z13 := by
    have h := sweepL table 5 [] [false,false,false,false] B B 15 loop15
      (2*j+1) (rep [true,false] j ++ tailF) [false,true,true]
    simpa [z12,z13,B,List.append_assoc] using h
  have h14 : run0 table (14*j) z13 = some z14 := by
    have h := sweepL table 5 [] [false,false,false] [true,false] [true,true] 14 loop14
      j tailF ([false] ++ rep B (2*j+1) ++ [false,true,true])
    simpa [z13,z14,B,List.append_assoc] using h
  have h57 : run0 table 57 z14 = some (phase3 n) := by
    have h := finish57
      (rep [true,true] j ++ [false] ++ rep B (2*j+1) ++ [false,true,true])
    have hk : 2*j+1=4*n+3 := by simp [j]; omega
    simpa [z14,phase3,j,B,tailF,hk,List.append_assoc] using h
  have H := join0 h19a (join0 h6a (join0 h6b (join0 h9a
    (join0 h30 (join0 h1 (join0 h14e (join0 h19b
      (join0 h6a2 (join0 h6b2 (join0 h9b (join0 h5
        (join0 h15 (join0 h14 h57)))))))))))))
  have hc : 224*n+260 =
      19 + (6*j + (6*j + (9 + (30*j + (1 + (14*(j+1) +
        (19 + (6*j + (6*j + (9 + (5 + (15*(2*j+1) + (14*j + (57)))))))))))))) := by
    dsimp [j]
    omega
  rw [hc]
  exact H

#print axioms phase1_to_phase2
#print axioms phase2_to_phase3
end BB6.Agent34Raw43B1LEE0LFM559Phase2
