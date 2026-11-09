import SourceOneShallowLift

namespace BB6.Agent43SourceWord
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent43TwoRun

/-- Legal P1 inverse word using only depths 0, 1, or 2, grouped into
(possibly empty) depth-two runs. First index counts depth-0/1 edges. -/
inductive SourceLowWord (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
| two (s b d m B D M : Nat) (h : SourceTwoChain n s b d m B D M) :
    SourceLowWord n 0 b d m B D M
| shallow (z b d m B D M t k c r E F H : Nat)
    (h : SourceLowWord n z b d m B D M)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D t=some (k,c))
    (hk : 2≤k) (hc : c%2=1) (ht : t≤1)
    (hnext : SourceTwoChain n r (2*k-4) (c+4) (M+t+1) E F H) :
    SourceLowWord n (z+1) b d m E F H

/-- A genuine depth-two step extends the final run and preserves the
number of shallow edges. -/
theorem SourceLowWord.appendTwo
    (n z b d m B D M k c : Nat)
    (h : SourceLowWord n z b d m B D M)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D 2=some (k,c))
    (hk : 2≤k) (hc : c%2=1) :
    SourceLowWord n z b d m (2*k-4) (c+4) (M+3) := by
  cases h with
  | two s b d m B D M chain =>
      exact SourceLowWord.two (s+1) b d m (2*k-4) (c+4) (M+3)
        (SourceTwoChain.append s b d m B D M k c chain hb hb4 hd hi hk hc)
  | shallow z b d m Q R S t l e r B D M prev hb0 hb04 hd0 hi0 hk0 hc0 ht0 chain =>
      exact SourceLowWord.shallow z b d m Q R S t l e (r+1)
        (2*k-4) (c+4) (M+3) prev hb0 hb04 hd0 hi0 hk0 hc0 ht0
        (SourceTwoChain.append r (2*l-4) (e+4) (S+t+1) B D M k c
          chain hb hb4 hd hi hk hc)

/-- A genuine shallow step starts a fresh, initially empty depth-two run. -/
theorem SourceLowWord.appendShallow
    (n z b d m B D M t k c : Nat)
    (h : SourceLowWord n z b d m B D M)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D t=some (k,c))
    (hk : 2≤k) (hc : c%2=1) (ht : t≤1) :
    SourceLowWord n (z+1) b d m (2*k-4) (c+4) (M+t+1) := by
  exact SourceLowWord.shallow z b d m B D M t k c 0 (2*k-4) (c+4) (M+t+1)
    h hb hb4 hd hi hk hc ht (SourceTwoChain.empty (2*k-4) (c+4) (M+t+1))

/-- Exactly one shallow edge cannot reach the shifted wall. -/
theorem source_low_word_one_no_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : SourceLowWord n 1 (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  cases h with
  | shallow z b0 d0 m0 B D M t k c r E F H prev hb hb4 hd hi hk hc ht tail =>
    cases prev with
    | two s p q x B D M chain =>
        rcases (by omega : t=0 ∨ t=1) with hz | ho
        · subst t
          exact source_no_zero_word_wall n s r B D M k c b d m hn chain
            hb hb4 hd hi hk hc tail hwall
        · subst t
          exact source_no_one_word_wall n s r B D M k c b d m hn chain
            hb hb4 hd hi hk hc tail hwall

/-- Exactly two shallow edges cannot reach the shifted wall. -/
theorem source_low_word_two_no_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : SourceLowWord n 2 (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  cases h with
  | shallow _ _ _ _ B D M t2 k2 c2 r E F H prev hb2 hb24 hd2 hi2 hk2 hc2 ht2 tail =>
    cases prev with
    | shallow _ _ _ _ B0 D0 M0 t1 k1 c1 u _ _ _ pre hb1 hb14 hd1 hi1 hk1 hc1 ht1 mid =>
      cases pre with
      | two s _ _ _ bp dp mp chain =>
        exact source_no_two_shallow_word_wall_all
          n s u r t1 t2 B0 D0 M0 k1 c1 B D M k2 c2 b d m
          hn ht1 ht2 chain hb1 hb14 hd1 hi1 hk1 hc1
          mid hb2 hb24 hd2 hi2 hk2 hc2 tail hwall

/-- Exactly three shallow edges cannot reach the shifted wall. -/
theorem source_low_word_three_no_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : SourceLowWord n 3 (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  cases h with
  | shallow _ _ _ _ B2 D2 M2 t3 k3 c3 r E F H prev3 hb3 hb34 hd3 hi3 hk3 hc3 ht3 tail =>
    cases prev3 with
    | shallow _ _ _ _ B1 D1 M1 t2 k2 c2 v _ _ _ prev2 hb2 hb24 hd2 hi2 hk2 hc2 ht2 mid2 =>
      cases prev2 with
      | shallow _ _ _ _ bp dp mp t1 k1 c1 u _ _ _ prev1 hb1 hb14 hd1 hi1 hk1 hc1 ht1 mid1 =>
        cases prev1 with
        | two s _ _ _ _ _ _ chain =>
          exact source_no_three_shallow_word_wall_all
            n s u v r t1 t2 t3 bp dp mp k1 c1 B1 D1 M1 k2 c2 B2 D2 M2
            k3 c3 b d m hn ht1 ht2 ht3 chain
            hb1 hb14 hd1 hi1 hk1 hc1 mid1 hb2 hb24 hd2 hi2 hk2 hc2
            mid2 hb3 hb34 hd3 hi3 hk3 hc3 tail hwall

/-- Stepwise true source trace, recording every inverse depth and the
exact number of shallow steps (depth 0 or 1). -/
inductive SourceLowTrace (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
| empty (b d m : Nat) : SourceLowTrace n 0 b d m b d m
| two (z b d m B D M k c : Nat)
    (h : SourceLowTrace n z b d m B D M)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D 2=some (k,c))
    (hk : 2≤k) (hc : c%2=1) :
    SourceLowTrace n z b d m (2*k-4) (c+4) (M+3)
| shallow (z b d m B D M t k c : Nat)
    (h : SourceLowTrace n z b d m B D M)
    (hb : 8≤B) (hb4 : B%4=0) (hd : D%2=1)
    (hi : inverseAt B D t=some (k,c))
    (hk : 2≤k) (hc : c%2=1) (ht : t≤1) :
    SourceLowTrace n (z+1) b d m (2*k-4) (c+4) (M+t+1)

/-- Every finite legal stepwise depth≤2 trace admits the normal form above. -/
theorem SourceLowTrace.toWord
    (n z b d m B D M : Nat) (h : SourceLowTrace n z b d m B D M) :
    SourceLowWord n z b d m B D M := by
  induction h with
  | empty b d m =>
      exact SourceLowWord.two 0 b d m b d m (SourceTwoChain.empty b d m)
  | two z b d m B D M k c prev hb hb4 hd hi hk hc ih =>
      exact SourceLowWord.appendTwo n z b d m B D M k c ih hb hb4 hd hi hk hc
  | shallow z b d m B D M t k c prev hb hb4 hd hi hk hc ht ih =>
      exact SourceLowWord.appendShallow n z b d m B D M t k c ih hb hb4 hd hi hk hc ht

/-- A pure depth-two source history has positive initial energy and negative
terminal wall energy, while each genuine depth-two step divides energy by 8. -/
theorem source_low_word_zero_no_wall
    (n b d m : Nat) (hn : 14≤n)
    (h : SourceLowWord n 0 (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : False := by
  cases h with
  | two s _ _ _ _ _ _ chain =>
      have hmass : (14*2^n-2*n-16)+3+2*0+2*n+13=14*2^n := by omega
      have hmodel := source_two_chain_model n s _ _ _ _ _ _ chain hmass
      have henergy := BB6.Agent43TwoRun.run_energy _ _ _ _ _ s hmodel
      have hrootEq :
          ((↑(14*2^n-2*n-16):Int)+4*(0:Int)+4*(n:Int)+20) =
          14*(2:Int)^n+2*(n:Int)+4 := by
        have hnat : (14*2^n-2*n-16)+4*n+20=14*2^n+2*n+4 := by omega
        exact_mod_cast hnat
      have hrootB : ((0:Int)+(n:Int)+6) = ((n:Int)+6) := by omega
      rw [show (↑(0:Nat):Int)=0 by rfl] at henergy
      rw [hrootEq,hrootB] at henergy
      have hrootI : BB6.Agent43TwoRun.I ((2:Int)^n)
          (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) =
          98*(2:Int)^n-(14*(n:Int)+92) := by
        unfold BB6.Agent43TwoRun.I
        omega
      rw [hrootI] at henergy
      have hwallInt : ((b:Int)+4*(m:Int)+4*(n:Int)+20)=12*(2:Int)^n := by
        exact_mod_cast hwall
      have hendNeg : BB6.Agent43TwoRun.I ((2:Int)^n)
          ((b:Int)+4*(m:Int)+4*(n:Int)+20) ((m:Int)+(n:Int)+6) < 0 := by
        rw [hwallInt]
        unfold BB6.Agent43TwoRun.I
        omega
      have h100 : 100*n≤2^n := BB6.Agent50RightFiveTwo.hundred_mul_le_pow n hn
      have h100i : 100*(n:Int)≤(2:Int)^n := by exact_mod_cast h100
      have hrootPos : 0<98*(2:Int)^n-(14*(n:Int)+92) := by omega
      have hqPos : 0<(8:Int)^s := Int.pow_pos (by decide)
      have hprodNeg : (8:Int)^s * BB6.Agent43TwoRun.I ((2:Int)^n)
          ((b:Int)+4*(m:Int)+4*(n:Int)+20) ((m:Int)+(n:Int)+6) < 0 :=
          Int.mul_neg_of_pos_of_neg hqPos hendNeg
      omega

/-- Source-certified uniform implication: any legal inverse history from the
critical root using only depths ≤2 that reaches the exact shifted wall must
contain at least four genuine shallow (depth 0/1) transitions. -/
theorem source_low_trace_wall_needs_four_shallows
    (n z b d m : Nat) (hn : 14≤n)
    (h : SourceLowTrace n z (14*2^n-2*n-16) 3 0 b d m)
    (hwall : b+4*m+4*n+20=12*2^n) : 4≤z := by
  by_cases hfour : 4≤z
  · exact hfour
  exfalso
  have hz3 : z≤3 := by omega
  rcases (by omega : z=0 ∨ z=1 ∨ z=2 ∨ z=3) with h0 | h1 | h2 | h3
  · subst z
    exact source_low_word_zero_no_wall n b d m hn (h.toWord) hwall
  · subst z
    exact source_low_word_one_no_wall n b d m hn (h.toWord) hwall
  · subst z
    exact source_low_word_two_no_wall n b d m hn (h.toWord) hwall
  · subst z
    exact source_low_word_three_no_wall n b d m hn (h.toWord) hwall

#print axioms source_low_trace_wall_needs_four_shallows
end BB6.Agent43SourceWord
