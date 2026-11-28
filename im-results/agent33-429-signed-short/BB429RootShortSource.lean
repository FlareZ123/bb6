import BB429RootShortArithmetic
import BB429NewResidue
import BB429RootMod16

namespace BB429RootShortSource
open BB429NewResidue
open BB429RootShortArithmetic

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

/-- The three short modular guards are theorems of the *original*
    blank-start accelerator, not abstract signed assumptions. -/
theorem gate_of_reach (a b : Nat) (h : Reach a b) : Gate a b := by
  unfold Gate
  obtain ⟨n,hn⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro ha he
    exact BB429RootEven8.rooted_positive_even_eight n a b hn ha he
  · exact BB429RootMod16.rooted_not_7_7 n a b hn
  · intro ha
    have hall := BB429NewResidue.reach_allowed a b ⟨n,hn⟩
    unfold BB429Mod8.Allowed at hall
    omega

/-- A reachable non-special target has a genuine reachable inverse
    predecessor satisfying the arithmetical three-way Parent relation. -/
theorem parent_of_reach (a b : Nat) (ha : 13 ≤ a) (h : Reach a b) :
    ∃ x y, Reach x y ∧ Parent a b x y := by
  by_cases ho : a%2=1
  · rcases BB429NewResidue.odd_back a b ha ho h with
      ⟨x,y,hp,hx,hy⟩ | ⟨x,y,hp,hx,hy,hb⟩
    · exact ⟨x,y,hp,Or.inl ⟨ho,hx,hy⟩⟩
    · exact ⟨x,y,hp,Or.inr (Or.inl ⟨ho,hb,hx,hy⟩)⟩
  · have he : a%2=0 := by omega
    obtain ⟨x,y,hp,hx,hy,hb⟩ :=
      BB429NewResidue.even_back a b (by omega) he h
    exact ⟨x,y,hp,Or.inr (Or.inr ⟨he,hb,hx,hy⟩)⟩

theorem branch13_q2_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (128*t+77) (256*t+151) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (128*t+77) (256*t+151) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      unfold Parent at h1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have h2' := hp2
      unfold Parent at h1' h2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have h2' := hp2
      have h3' := hp3
      unfold Parent at h1' h2' h3'
      omega) hr3
  exact BB429RootShortArithmetic.branch13_q2_no_four
    t u1 w1 u2 w2 u3 w3 u4 w4 hp1 hp2 hp3 hp4 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4)

theorem branch13_q3_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (128*t+109) (256*t+215) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (128*t+109) (256*t+215) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      unfold Parent at h1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have h2' := hp2
      unfold Parent at h1' h2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have h2' := hp2
      have h3' := hp3
      unfold Parent at h1' h2' h3'
      omega) hr3
  exact BB429RootShortArithmetic.branch13_q3_no_four
    t u1 w1 u2 w2 u3 w3 u4 w4 hp1 hp2 hp3 hp4 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4)

theorem branch15_q1_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (128*t+47) (256*t+91) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (128*t+47) (256*t+91) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      unfold Parent at h1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have h2' := hp2
      unfold Parent at h1' h2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have h2' := hp2
      have h3' := hp3
      unfold Parent at h1' h2' h3'
      omega) hr3
  obtain ⟨u5,w5,hr5,hp5⟩ :=
    parent_of_reach u4 w4 (by
      have h1' := hp1
      have h2' := hp2
      have h3' := hp3
      have h4' := hp4
      unfold Parent at h1' h2' h3' h4'
      omega) hr4
  exact BB429RootShortArithmetic.branch15_q1_no_five
    t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 hp1 hp2 hp3 hp4 hp5 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4) (gate_of_reach u5 w5 hr5)


#print axioms gate_of_reach
#print axioms parent_of_reach
#print axioms branch13_q2_unreachable
#print axioms branch13_q3_unreachable
#print axioms branch15_q1_unreachable
end BB429RootShortSource
