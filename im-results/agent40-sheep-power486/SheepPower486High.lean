import SheepPower486RootGate
import SheepOddGap
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower486

private theorem stable_gap (D S A : Nat)
    (hA : 2 ≤ A) (hD : 0 < D)
    (hbase : 1 < D*(2*A-3)+S ∧ D*(2*A-3)+S < 2^A)
    (hdbl : 2*D ≤ 2^A) :
    ∀ a : Nat, A ≤ a →
    1 < D*(2*a-3)+S ∧ D*(2*a-3)+S < 2^a ∧ 2*D ≤ 2^a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    by_cases heq : a=A
    · subst a
      exact ⟨hbase.1, hbase.2, hdbl⟩
    have hh : A≤a-1 := by omega
    have hlt : a-1<a := by omega
    have hprev := ih (a-1) hlt hh
    have hrepl : a-1+1=a := by omega
    have haexpr : 2*(a-1+1)-3 = 2*a-3 := by omega
    have hp : 2^a = 2*2^(a-1) := by
      calc
        2^a = 2^((a-1)+1) := by rw [hrepl]
        _ = 2*2^(a-1) := by rw [Nat.pow_succ]; omega
    have hk : D*(2*a-3)+S = (D*(2*(a-1)-3)+S)+2*D := by
      have hsub : 2*a-3 = (2*(a-1)-3)+2 := by omega
      rw [hsub, Nat.mul_add]
      omega
    rw [hk, hp]
    constructor
    · omega
    constructor
    · omega
    · omega

/-- The signed-power interval holds uniformly above each sixth-stratum cutoff. -/
theorem high_cutoff (h a : Nat) (hh : h ≤ 6)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a) :
    1 < 3^h*(2*a-3)+2^(h+1) ∧
    3^h*(2*a-3)+2^(h+1) < 2^a := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 from by omega) with h0|h1|h2|h3|h4|h5|h6
  · subst h
    have hA : 2 ≤ a := by simpa using ha
    have hg := stable_gap 1 2 2 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 5 ≤ a := by simpa using ha
    have hg := stable_gap 3 4 5 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 7 ≤ a := by simpa using ha
    have hg := stable_gap 9 8 7 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 9 ≤ a := by simpa using ha
    have hg := stable_gap 27 16 9 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 11 ≤ a := by simpa using ha
    have hg := stable_gap 81 32 11 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 13 ≤ a := by simpa using ha
    have hg := stable_gap 243 64 13 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩
  · subst h
    have hA : 15 ≤ a := by simpa using ha
    have hg := stable_gap 729 128 15 (by decide) (by decide) (by decide) (by decide) a hA
    exact ⟨hg.1, hg.2.1⟩

private theorem odd_three_pow (h : Nat) : ((3:Int)^h)%2=1 := by
  induction h with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ, Int.mul_emod, ih]
    decide

/-- All generic source valuations above their signed-power cutoffs are impossible. -/
theorem no_high_source (h a t v : Nat) (hh : h ≤ 6)
    (ha : (if h=0 then 2 else 2*h+3) ≤ a)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(486*t+h+1)+3*3^h) : False := by
  have hgap := high_cutoff h a hh ha
  have ha2 : 2≤a := by split at ha <;> omega
  let K : Int := (3:Int)^h*(2*(a:Int)-3)+(2:Int)^(h+1)
  have hK_eq : K = ((3^h*(2*a-3)+2^(h+1):Nat):Int) := by
    dsimp [K]
    have hsub : (↑(2*a-3):Int) = 2*(a:Int)-3 := by omega
    rw [←hsub]
  have hKlow : 1 < K := by
    rw [hK_eq]
    exact_mod_cast hgap.1
  have hKhigh : K < (2:Int)^a := by
    rw [hK_eq]
    exact_mod_cast hgap.2
  have hKodd : K%2=1 := by
    dsimp [K]
    have hodd := odd_three_pow h
    have heven : ((2:Int)^(h+1))%2=0 := by
      rw [Int.pow_succ, Int.mul_emod]
      simp
    have hlinodd : (2*(a:Int)-3)%2=1 := by omega
    rw [Int.add_emod, Int.mul_emod, hodd, hlinodd, heven]
    decide
  have heq_int : (3:Int)^h*((2:Int)^(a+1)+1)*(v:Int) +
      2*(a:Int)*(3:Int)^h + (2:Int)^(h+1)
      = (2:Int)^(486*t+h+1)+3*(3:Int)^h := by
    exact_mod_cast heq
  have hdiv : ((2:Int)^(a+1)+1) ∣ (2:Int)^(486*t+h+1)-K := by
    refine ⟨(3:Int)^h*(v:Int), ?_⟩
    dsimp [K]
    let D : Int := (3:Int)^h
    let B : Int := ((2:Int)^(a+1)+1)
    let N : Int := (2:Int)^(486*t+h+1)
    let S : Int := (2:Int)^(h+1)
    have hmul : D*(2*(a:Int)-3) = 2*(a:Int)*D-3*D := by
      dsimp [D]
      rw [Int.mul_sub]
      have h1 : (3:Int)^h*(2*(a:Int))= 2*(a:Int)*(3:Int)^h := by ac_rfl
      rw [h1]
      have h2 : (3:Int)^h*3=3*(3:Int)^h := by ac_rfl
      rw [h2]
    have hmul2 : D*B*(v:Int)=B*(D*(v:Int)) := by ac_rfl
    have heq2 : D*B*(v:Int)+2*(a:Int)*D+S=N+3*D := by
      simpa only [D, B, N, S] using heq_int
    calc
      N-(D*(2*(a:Int)-3)+S) = D*B*(v:Int) := by
        rw [hmul]
        omega
      _ = B*(D*(v:Int)) := hmul2
  exact (SheepOddGap.no_power_signed_small_odd a K hKlow hKodd hKhigh (486*t+h+1)).1 hdiv

/-- Entire generic even-section predecessor exclusion, no bound on a. -/
theorem no_generic_all_a (h a t v : Nat)
    (hh : h ≤ 6) (ha : 1 ≤ a)
    (ht4 : t%4=0) (ht7 : t%7≠1) (ht9 : t%9≠2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(486*t+h+1)+3*3^h) : False := by
  by_cases high : (if h=0 then 2 else 2*h+3) ≤ a
  · exact no_high_source h a t v hh high heq
  · have hzero : h=0 → a=1 := by
      intro hz
      subst h
      simp at high
      omega
    have hpos : 0<h → a≤2*h+2 := by
      intro hhpos
      have hnz : h≠0 := by omega
      simp only [hnz, ↓reduceIte] at high
      omega
    exact no_generic_forbidden h a t v hh ha hzero hpos ht4 ht7 ht9 heq

#print axioms high_cutoff
#print axioms no_high_source
#print axioms no_generic_all_a
end SheepPower486
