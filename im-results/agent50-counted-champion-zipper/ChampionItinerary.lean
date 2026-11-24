import CountedItinerary
namespace BB6CountedZipper
structure Sec where
  m : Nat
  a : Nat
  b : Nat
  cost : Nat

def sectionRun : Nat → Nat → Nat → Nat → Sec
  | 0,m,a,b => ⟨m,a,b,0⟩
  | n+1,m,a,b =>
    let s := sectionRun n (nextM m) (nextA m a b) (2^b-1)
    {s with cost := rstCost m (n+1) a b+s.cost}

theorem section_run (L n m a b : Nat) (h : Int) (hn : n<2^L) (hm : m<3) :
    ∃ h', run (sectionRun n m a b).cost (s1 L n m a 0 b h) =
      some (s1 L 0 (sectionRun n m a b).m (sectionRun n m a b).a 0 (sectionRun n m a b).b h') := by
  induction n generalizing m a b h with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    have h₁ := rst L (n+1) m a b h (by omega) hn hm
    obtain ⟨h',h₂⟩ := ih (nextM m) (nextA m a b) (2^b-1) (h+5+3*(b:Int)) (by omega) (by unfold nextM;omega)
    rw [Nat.add_sub_cancel] at h₁
    exact ⟨h',join h₁ h₂⟩

theorem section_marker (n m a b : Nat) (hm : m<3) : (sectionRun n m a b).m=(m+2*n)%3 := by
  induction n generalizing m a b with
  | zero => simp [sectionRun,Nat.mod_eq_of_lt hm]
  | succ n ih =>
    change (sectionRun n (nextM m) (nextA m a b) (2^b-1)).m = _
    rw [ih _ _ _ (by unfold nextM;omega)]
    unfold nextM
    omega

def tag (m : Nat) := if m=1 then 1 else 0

theorem odd_power_sub (b : Nat) (hb : 0<b) : (2^b-1)%2=1 := by
  cases b with
  | zero => omega
  | succ b => rw [Nat.pow_succ]; have := Nat.two_pow_pos b;omega

theorem section_parity (n m a b : Nat) (hm : m<3) (hb : b%2=1) :
    (sectionRun n m a b).b%2=1 ∧
    ((sectionRun n m a b).a+tag (sectionRun n m a b).m)%2=(a+tag m)%2 := by
  induction n generalizing m a b with
  | zero => exact ⟨hb,rfl⟩
  | succ n ih =>
    have h := ih (nextM m) (nextA m a b) (2^b-1) (by unfold nextM;omega) (odd_power_sub b (by omega))
    change _ ∧ _
    refine ⟨h.1,h.2.trans ?_⟩
    have hc : m=0 ∨ m=1 ∨ m=2 := by omega
    rcases hc with hc|hc|hc <;> subst m <;> simp [nextM,nextA,tag] <;> omega

theorem pow_mod_three (k : Nat) : 2^k%3=if k%2=0 then 1 else 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ,Nat.mul_mod,ih]
    by_cases hk : k%2=0
    · simp [hk,show (k+1)%2≠0 by omega]
    · simp [hk,show (k+1)%2=0 by omega]

theorem expanded_mod_odd (a : Nat) (ha : a%2=1) : expanded 3 a%3=1 := by
  have hp := pow_mod_three a
  simp [show a%2≠0 by omega] at hp
  have hs : expanded 3 a+1=31*2^a := by unfold expanded;have := Nat.two_pow_pos a;omega
  have hh := congrArg (fun x : Nat => x%3) hs
  rw [Nat.add_mod,Nat.mul_mod,hp] at hh
  omega

theorem expanded_mod_even (L a : Nat) (hL : L%2=0) : expanded L a%3=2 := by
  have hp := pow_mod_three (L+2)
  simp [show (L+2)%2=0 by omega] at hp
  have hs : (2^(L+2)-1)+1=2^(L+2) := by have := Nat.two_pow_pos (L+2);omega
  have hz := congrArg (fun x : Nat => x%3) hs
  rw [Nat.add_mod,hp] at hz
  have hz' : (2^(L+2)-1)%3=0 := by omega
  have hpos : 0<(2^(L+2)-1)*2^a := Nat.mul_pos (by rw [Nat.pow_succ]; have := Nat.two_pow_pos (L+1);omega) (Nat.two_pow_pos a)
  have he : expanded L a+1=(2^(L+2)-1)*2^a := by unfold expanded;omega
  have hh := congrArg (fun x : Nat => x%3) he
  rw [Nat.add_mod,Nat.mul_mod,hz'] at hh
  simp at hh
  omega

def secondLen (a : Nat) := 3+a+2
def secondSec (a b : Nat) := sectionRun (expanded 3 a) 2 b (2^b-1)
def thirdLen (a b : Nat) := secondLen a+(secondSec a b).a+2
def thirdSec (a b : Nat) := sectionRun (expanded (secondLen a) (secondSec a b).a) 2 (secondSec a b).b (2^(secondSec a b).b-1)
def finishCost (a b : Nat) := primeCost 3 a b+(secondSec a b).cost+primeCost (secondLen a) (secondSec a b).a (secondSec a b).b+(thirdSec a b).cost+(59+12*(thirdLen a b+(thirdSec a b).a))

theorem finish (a b : Nat) (h : Int) (ha : a%2=1) :
    ∃ z, run (finishCost a b) (s1 3 0 1 a 0 b h)=some z ∧ step z=none := by
  have H₂ := rstPrime 3 a b h
  have hN1 : expanded 3 a<2^(secondLen a) := expanded_lt 3 a
  obtain ⟨h₃,H₃⟩ := section_run (secondLen a) (expanded 3 a) 2 b (2^b-1) _ hN1 (by decide)
  change run (secondSec a b).cost _ = some (s1 (secondLen a) 0 (secondSec a b).m (secondSec a b).a 0 (secondSec a b).b h₃) at H₃
  have hm : (secondSec a b).m=1 := by
    unfold secondSec
    rw [section_marker _ _ _ _ (by decide)]
    have := expanded_mod_odd a ha;omega
  rw [hm] at H₃
  have H₄ := rstPrime (secondLen a) (secondSec a b).a (secondSec a b).b h₃
  have hN2 : expanded (secondLen a) (secondSec a b).a<2^(thirdLen a b) := expanded_lt _ _
  obtain ⟨h₅,H₅⟩ := section_run (thirdLen a b) (expanded (secondLen a) (secondSec a b).a) 2 (secondSec a b).b (2^(secondSec a b).b-1) _ hN2 (by decide)
  change run (thirdSec a b).cost _ = some (s1 (thirdLen a b) 0 (thirdSec a b).m (thirdSec a b).a 0 (thirdSec a b).b h₅) at H₅
  have hm' : (thirdSec a b).m=0 := by
    unfold thirdSec
    rw [section_marker _ _ _ _ (by decide)]
    have he : secondLen a%2=0 := by unfold secondLen;omega
    have := expanded_mod_even (secondLen a) (secondSec a b).a he
    omega
  rw [hm'] at H₅
  obtain ⟨z,H₆,Hstop⟩ := haltFinal (thirdLen a b) (thirdSec a b).a (thirdSec a b).b h₅
  exact ⟨z,join (join (join (join H₂ H₃) H₄) H₅) H₆,Hstop⟩

theorem first_exists : ∃ s : Sec, s=sectionRun 7 2 6 63 := ⟨_,rfl⟩
noncomputable def first : Sec := Classical.choose first_exists

theorem first_eq : first = sectionRun 7 2 6 63 := Classical.choose_spec first_exists

theorem first_marker : first.m=1 := (congrArg Sec.m first_eq).trans (section_marker 7 2 6 63 (by decide))

theorem first_a_odd : first.a%2=1 := by
  have h := (section_parity 7 2 6 63 (by decide) (by decide)).2
  rw [← first_eq,first_marker] at h
  simp [tag] at h
  omega

noncomputable def remainingCost : Nat := first.cost+finishCost first.a first.b

theorem complete_itinerary (h : Int) : ∃ z, run remainingCost (s1 3 7 2 6 0 63 h)=some z ∧ step z=none := by
  obtain ⟨h₁,H₁⟩ := section_run 3 7 2 6 63 h (by decide) (by decide)
  rw [← first_eq,first_marker] at H₁
  obtain ⟨z,H₂,Hstop⟩ := finish first.a first.b h₁ first_a_odd
  exact ⟨z,join H₁ H₂,Hstop⟩

#print axioms complete_itinerary
end BB6CountedZipper
