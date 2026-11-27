import M62Grammar
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

/-- The 13-step first part of the unbounded backward carry. -/
theorem carry_prepare (L R : List Bool) :
    run0 table 13 ⟨5,false::L,zeros 4++R⟩ =
      some ⟨0,ones 2++L,bits "101"++R⟩ := by rfl

theorem carry_prepare_blank (L : List Bool) :
    run0 table 13 ⟨5,false::L,[]⟩ =
      some ⟨0,ones 2++L,bits "101"⟩ := by rfl

/-- At A scanning zero, four zero cells become a 1101 packet. -/
theorem carry_q (L R : List Bool) (hL : L.headD false = false) :
    run0 table 8 ⟨0,L,zeros 3++R⟩ =
      some ⟨0,true::L.tail,bits "101"++R⟩ := by
  cases L with
  | nil => rfl
  | cons b L =>
      cases b with
      | false => rfl
      | true => simp at hL

/-- Final A1 then A0,B0,C1 returns F0 with three new left ones. -/
theorem carry_finish (L R : List Bool) (hL : L.headD false = false) :
    run0 table 4 ⟨0,true::L,bits "101"++R⟩ =
      some ⟨5,false::ones 3++L.tail,true::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L =>
      cases b with
      | false => rfl
      | true => simp at hL

/-- Unbounded A1 erasure with the exact primitive cost and untouched tails. -/
theorem erase_ones (n : Nat) (L R : List Bool) :
    run0 table n ⟨0,ones n++L,R⟩ =
      some ⟨0,L,zeros n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      have h1 : run0 table 1 ⟨0,true::(ones n++L),R⟩ =
          some ⟨0,ones n++L,false::R⟩ := by rfl
      have h2 := ih (false::R)
      have h := join0 h1 h2
      rw [Nat.add_comm 1 n] at h
      have hr : zeros n ++ false::R = zeros (n+1) ++ R := by
        rw [zeros,zeros,List.replicate_succ',List.append_assoc]
        rfl
      rw [hr] at h
      simpa only [ones,List.replicate_succ,List.cons_append] using h

/-- Each interior run of >=2 ones is erased, then Q creates 101 and
    leaves the next earlier run available. -/
theorem scan_one (n : Nat) (hn : 2 ≤ n) (L R : List Bool)
    (hL : L.headD false = false) :
    run0 table (n+9) ⟨0,true::(ones n++L),bits "101"++R⟩ =
      some ⟨0,true::L.tail,
        bits "101"++zeros (n-2)++bits "101"++R⟩ := by
  have hzeros : zeros (n+1) = zeros 3 ++ zeros (n-2) := by
    have hn' : n+1 = 3+(n-2) := by omega
    rw [hn',zeros_add]
  have h1 : run0 table (n+1) ⟨0,true::(ones n++L),bits "101"++R⟩ =
      some ⟨0,L,zeros 3++(zeros (n-2)++bits "101"++R)⟩ := by
    have hone : ones (n+1) = true::ones n := by
      simp [ones,List.replicate_succ]
    simpa only [hone,hzeros,List.append_assoc] using
      erase_ones (n+1) L (bits "101"++R)
  have h2 := carry_q L (zeros (n-2)++bits "101"++R) hL
  have h := join0 h1 h2
  have hcost : (n+1)+8=n+9 := by omega
  simpa only [hcost,List.append_assoc] using h

/-- The first run (nearest the original F head) has two extra ones
    written by P. It may have length one. -/
theorem scan_last (n : Nat) (hn : 1 ≤ n) (L R : List Bool)
    (hL : L.headD false = false) :
    run0 table (n+10) ⟨0,ones (n+2)++L,bits "101"++R⟩ =
      some ⟨0,true::L.tail,
        bits "101"++zeros (n-1)++bits "101"++R⟩ := by
  have hzeros : zeros (n+2) = zeros 3 ++ zeros (n-1) := by
    have hn' : n+2 = 3+(n-1) := by omega
    rw [hn',zeros_add]
  have h1 : run0 table (n+2) ⟨0,ones (n+2)++L,bits "101"++R⟩ =
      some ⟨0,L,zeros 3++(zeros (n-1)++bits "101"++R)⟩ := by
    simpa only [hzeros,List.append_assoc] using
      erase_ones (n+2) L (bits "101"++R)
  have h2 := carry_q L (zeros (n-1)++bits "101"++R) hL
  have h := join0 h1 h2
  have hcost : (n+2)+8=n+10 := by omega
  simpa only [hcost,List.append_assoc] using h

def w4 (k : Nat) : List Bool := zeros (5*k+4)++bits "101"

/-- A-code: first zero-run is 1 mod 5; later zero-run packets are 4 mod 5. -/
inductive ACode : List Bool → Prop
  | base (a : Nat) : ACode (zeros (5*a+1)++bits "101")
  | more (k : Nat) (c : List Bool) (hc : ACode c) :
      ACode (c++w4 k)

/-- Parametric propagation across all earlier A-frame runs, expressed
    as a positive-cost existential. This is an arbitrary-tail identity. -/
theorem scan_a {u : List Bool} (hu : AFrame u) (L R : List Bool)
    (hL : L.headD false = false) :
    ∃ t c, 0 < t ∧ ACode c ∧
      run0 table t ⟨0,true::(u++L),bits "101"++R⟩ =
        some ⟨0,true::L.tail,bits "101"++c++R⟩ := by
  induction hu generalizing L R with
  | base a =>
      have h := scan_one (5*a+3) (by omega) L R hL
      have hn : (5*a+3)-2 = 5*a+1 := by omega
      refine ⟨(5*a+3)+9, zeros (5*a+1)++bits "101",
          by omega, ACode.base a, ?_⟩
      simpa only [hn,List.append_assoc] using h
  | more b u hu ih =>
      have h1raw :=
        scan_one (5*(b+1)+1) (by omega) (false::u++L) R (by rfl)
      have hnum : (5*(b+1)+1)-2 = 5*b+4 := by omega
      have h1 : run0 table ((5*(b+1)+1)+9)
          ⟨0,true::((ones (5*(b+1)+1)++false::u)++L),bits "101"++R⟩ =
          some ⟨0,true::(u++L),bits "101"++(w4 b++R)⟩ := by
        simpa only [hnum,w4,List.append_assoc,List.tail_cons] using h1raw
      obtain ⟨t,c,ht,hc,h2⟩ := ih L (w4 b++R) hL
      have h := join0 h1 h2
      refine ⟨((5*(b+1)+1)+9)+t,c++w4 b,by omega,ACode.more b c hc,?_⟩
      simpa only [List.append_assoc] using h

#print axioms carry_prepare
#print axioms carry_q
#print axioms carry_finish
#print axioms erase_ones
#print axioms scan_one
#print axioms scan_last
#print axioms scan_a
end BB6.Agent38M62
