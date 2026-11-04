import S4Octet
import Lean.Elab.Tactic.Omega

namespace S4OctetGrowth
open S4Power S4Octet

private theorem H_bound (L : List Nat) :
    ∀ a U, H a L = some U → a + 2 * W L + a / 2 + 3 ≤ W U := by
  induction L with
  | nil =>
    intro a
    induction a using Nat.strongRecOn with
    | ind a ih =>
      intro U h
      by_cases hp : a % 2 = 0
      · by_cases hz : a = 0
        · simp [H, hp, hz] at h
        · simp [H, hp, hz] at h
          rcases h with ⟨rfl⟩
          simp [W]
          omega
      · by_cases hz : a ≤ 1
        · simp [H, hp, hz] at h
        · have ha : a / 2 < a := by omega
          have h0 : (H (a / 2) []).map (a / 2 :: ·) = some U := by
            rw [H] at h
            simp only [hp, hz, ite_false] at h
            exact h
          obtain ⟨V, hV, hVU⟩ := Option.map_eq_some_iff.mp h0
          subst U
          have hi := ih (a / 2) ha V hV
          simp [W] at hi ⊢
          omega
  | cons b S ih =>
    intro a U h
    by_cases hp : a % 2 = 0
    · simp [H, hp] at h
      rcases h with ⟨rfl⟩
      simp [W]
      omega
    · have h0 : (H (b + a / 2 + 1) S).map (a / 2 :: ·) = some U := by
        rw [H] at h
        simp only [hp, ite_false] at h
        exact h
      obtain ⟨V, hV, hVU⟩ := Option.map_eq_some_iff.mp h0
      subst U
      have hi := ih (b + a / 2 + 1) V hV
      simp only [W] at hi ⊢
      omega

private theorem G107_growth_cons (b : Nat) (S U : List Nat)
    (h : G 107 (b::S)=some U) :
    W (b::S) + 109 + (b+107)/2 ≤ W U := by
  have hb := H_bound S (b+107) U h
  simp only [W] at hb ⊢
  omega

private theorem G148_growth_cons (b : Nat) (S U : List Nat)
    (h : G 148 (b::S)=some U) :
    W (b::S)+150+(b+148)/2 ≤ W U := by
  have hb := H_bound S (b+148) U h
  simp only [W] at hb ⊢
  omega

private theorem G107_head (R U : List Nat) (h : G 107 R=some U) :
    ∃ b S, U=b::S ∧ 53≤b ∧
    (R=[] ∨ ∃ z Z, R=z::Z ∧
       (z%2=0 ∧ b=(z+107)/2 ∨ z%2=1 ∧ b=(z+107)/2+2)) := by
  cases R with
  | nil =>
    have hh : G 107 [] = some [55,52] := by simp [G,H]
    rw [hh] at h
    have hu : U=[55,52] := by cases h; rfl
    subst U
    exact ⟨55,[52],rfl,by omega,Or.inl rfl⟩
  | cons z Z =>
    by_cases he : (z+107)%2=0
    · cases Z with
      | nil =>
          have hu : U=[(z+107)/2+2,(z+107)/2-1] := by
            simpa [G,H,he] using h.symm
          subst U
          refine ⟨(z+107)/2+2,[(z+107)/2-1],rfl,by omega,
            Or.inr ⟨z,[],rfl,?_⟩⟩
          exact Or.inr ⟨by omega,rfl⟩
      | cons k T =>
          have hu : U=((z+107)/2+2)::(k+(z+107)/2)::T := by
            simpa [G,H,he] using h.symm
          subst U
          refine ⟨(z+107)/2+2,(k+(z+107)/2)::T,rfl,by omega,
            Or.inr ⟨z,k::T,rfl,?_⟩⟩
          exact Or.inr ⟨by omega,rfl⟩
    · cases Z with
      | nil =>
          have hh : (H ((z+107)/2) []).map ((z+107)/2::·) = some U := by
            change H (z+107) [] = some U at h
            rw [H] at h
            simp only [he, ite_false] at h
            have hbig : ¬ z+107 ≤ 1 := by omega
            simpa only [hbig, ite_false] using h
          obtain ⟨V,hV,rfl⟩ := Option.map_eq_some_iff.mp hh
          refine ⟨(z+107)/2,V,rfl,by omega,Or.inr ⟨z,[],rfl,?_⟩⟩
          exact Or.inl ⟨by omega,rfl⟩
      | cons k T =>
          have hh : (H (k+(z+107)/2+1) T).map ((z+107)/2::·) = some U := by
            change H (z+107) (k::T) = some U at h
            rw [H] at h
            simpa only [he, ite_false] using h
          obtain ⟨V,hV,rfl⟩ := Option.map_eq_some_iff.mp hh
          refine ⟨(z+107)/2,V,rfl,by omega,Or.inr ⟨z,k::T,rfl,?_⟩⟩
          exact Or.inl ⟨by omega,rfl⟩

private theorem G107_zero_extra (S U : List Nat)
    (h : G 107 (0::S)=some U) :
    W (0::S)+165 ≤ W U := by
  cases S with
  | nil =>
      have hu : U=[53,26,15,12] := by simpa [G,H] using h.symm
      subst U
      decide
  | cons b T =>
      have hm : (H (b+54) T).map (53::·) = some U := by
        change H 107 (b::T) = some U at h
        rw [H] at h
        simpa using h
      obtain ⟨V,hV,rfl⟩ := Option.map_eq_some_iff.mp hm
      have hi := H_bound T (b+54) V hV
      simp only [W] at hi ⊢
      omega

private theorem G107_two_extra (S U : List Nat)
    (h : G 107 (2::S)=some U) :
    W (2::S)+165 ≤ W U := by
  cases S with
  | nil =>
      have hu : U=[54,29,26] := by simpa [G,H] using h.symm
      subst U
      decide
  | cons b T =>
      have hm : (H (b+55) T).map (54::·) = some U := by
        change H 109 (b::T) = some U at h
        rw [H] at h
        simpa using h
      obtain ⟨V,hV,rfl⟩ := Option.map_eq_some_iff.mp hm
      have hi := H_bound T (b+55) V hV
      simp only [W] at hi ⊢
      omega

private theorem W_bump253 (V : List Nat) : W (bumpN 253 V) = W V+253 := by
  cases V <;> simp [bumpN,W] <;> omega

set_option maxHeartbeats 0

theorem Q_growth_668 (R V : List Nat) (h : Q R=some V) :
    W R+668 ≤ W V := by
  cases hu : G 107 R with
  | none =>
      simp [Q,hu] at h
  | some U =>
      cases hv : G 148 U with
      | none =>
          simp [Q,hu,hv] at h
      | some X =>
          have hresult : V=bumpN 253 X := by
            simpa [Q,hu,hv] using h.symm
          rw [hresult, W_bump253]
          obtain ⟨u,T,hut,hlower,hkind⟩ := G107_head R U hu
          subst U
          have hg2 := G148_growth_cons u T X hv
          cases R with
          | nil =>
              have h0 : G 107 [] = some [55,52] := by simp [G,H]
              have he : u::T=[55,52] := by simpa [h0] using hu.symm
              have ⟨hu55,hT⟩ : u=55 ∧ T=[52] := by
                simpa only [List.cons.injEq] using he
              subst u
              subst T
              have h1 : G 148 [55,52] = some [101,79,76] := by simp [G,H]
              rw [h1] at hv
              cases hv
              decide
          | cons b S =>
              have hb := G107_growth_cons b S (u::T) hu
              rcases hkind with hnil | ⟨z,Z,heq,hpar⟩
              · contradiction
              · cases heq
                by_cases h0 : b=0
                · subst b
                  have hstrong := G107_zero_extra S (u::T) hu
                  omega
                · by_cases h2 : b=2
                  · subst b
                    have hstrong := G107_two_extra S (u::T) hu
                    omega
                  · by_cases h1 : b=1
                    · subst b
                      rcases hpar with hmod | hmod
                      · omega
                      · rcases hmod with ⟨hp,huval⟩
                        have hfirst : u=56 := by omega
                        omega
                    · have hlarge : 3≤b := by omega
                      rcases hpar with hmod | hmod
                      · omega
                      · omega

theorem Q_growth_668_sharp :
    Q [1] = some [357,155] ∧ W [357,155] = W [1]+668 := by
  constructor
  · simp [Q,G,H,bumpN]
  · decide

set_option maxRecDepth 2000
theorem qrun_growth_668 (n : Nat) (R S : List Nat)
    (h : qrun n R = some S) : W R + 668*n ≤ W S := by
  induction n generalizing S with
  | zero =>
      simp [qrun] at h
      subst S
      simp
  | succ n ih =>
      simp only [qrun] at h
      cases hn : qrun n R with
      | none => simp [hn] at h
      | some U =>
          simp only [hn,Option.bind_some] at h
          have h0 := ih U hn
          have h1 := Q_growth_668 U S h
          omega

theorem qrun_no_recurrence (n : Nat) (R : List Nat) (hn : 0<n) :
    qrun n R ≠ some R := by
  intro h
  have hg := qrun_growth_668 n R R h
  omega

#print axioms Q_growth_668
#print axioms Q_growth_668_sharp
#print axioms qrun_growth_668
#print axioms qrun_no_recurrence
end S4OctetGrowth
