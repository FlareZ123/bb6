import UniformPrecisionStep
import PredicateList

namespace BB6.Agent8Adaptive
open BB6.Precision
open BB6.Agent8FiniteBridge

/-- Shadow-language lift with statewise precision D-m. -/
def lifted (D r : Nat) (S : Nat → Nat → Prop) (m z : Nat) : Prop :=
  ∃ z0 s, S m z0 ∧ z=z0+2^(D-m)*(s*r)

theorem root (D r zbase c : Nat) (S : Nat → Nat → Prop)
    (hroot : S 0 zbase) :
    lifted D r S 0 (zbase+2^D*(c*r)) := by
  exact ⟨zbase,c,hroot,by simp⟩

theorem cost (D r M : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M) :
    ∀ m z, lifted D r S m z → m≤M := by
  intro m z ⟨z0,s,hs,_⟩
  exact hsmall m z0 hs

/-- A lifted shadow cannot gain 1024-divisibility when its base coordinate
is nondivisible by 1024 and the local precision 2^(D-m). -/
theorem no1024 (D M r : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M)
    (hM : M≤D)
    (hstate : ∀ m z, S m z → ¬2^(D-m)∣z)
    (h1024 : ∀ m z, S m z → ¬1024∣z) :
    ∀ m z, lifted D r S m z → ¬1024∣z := by
  intro m z ⟨z0,s,hs,hz⟩ h1024z
  have hm : m≤D := Nat.le_trans (hsmall m z0 hs) hM
  have hdiff : 2^(D-m) ∣ 2^(D-m)*(s*r) := by exact ⟨s*r,rfl⟩
  by_cases he : D-m≤10
  · have hpow : (2:Nat)^(D-m) ∣ 1024 := by
      simpa using Nat.pow_dvd_pow 2 he
    have htotal : 2^(D-m) ∣ z0+2^(D-m)*(s*r) := by
      rw [←hz]
      exact Nat.dvd_trans hpow h1024z
    exact hstate m z0 hs ((Nat.dvd_add_iff_left hdiff).mpr htotal)
  · have he' : 10≤D-m := by omega
    have hpow : 1024 ∣ (2:Nat)^(D-m) := by
      simpa using Nat.pow_dvd_pow 2 he'
    have hchange : 1024 ∣ 2^(D-m)*(s*r) := by
      rcases hpow with ⟨d,hpow⟩
      refine ⟨d*(s*r), ?_⟩
      rw [hpow]
      ac_rfl
    have htotal : 1024 ∣ z0+2^(D-m)*(s*r) := by
      rw [←hz]
      exact h1024z
    exact h1024 m z0 hs ((Nat.dvd_add_iff_left hchange).mpr htotal)

/-- Reuse the source-independent dyadic step theorem with K'=D-m,
M'=m. This transports every lifted edge while preserving adaptive precision. -/
theorem closed (D L0 r M : Nat) (S : Nat → Nat → Prop)
    (hsmall : ∀ m z, S m z → m≤M)
    (hM : M≤D)
    (hstate : ∀ m z, S m z → ¬2^(D-m)∣z)
    (hclosed : ∀ m z t v zp, S m z → z=2^t*v →
        2*zp+1=L0+m+t+v → S (m+t+1) zp) :
    ∀ m z t v zp, lifted D r S m z → z=2^t*v →
    2*zp+1=(L0+16*2^D*r)+m+t+v →
    lifted D r S (m+t+1) zp := by
  intro m z t v zp hmem hd hn
  obtain ⟨z0,s,hs,heq⟩ := hmem
  have hm : m≤D := Nat.le_trans (hsmall m z0 hs) hM
  have hd0 : z0+2^(D-m)*(s*r)=2^t*v := by rw [←heq]; exact hd
  have he : (D-m)+m=D := Nat.sub_add_cancel hm
  have ht := depth_lt_K (D-m) m m z0 (s*r) t v
    (by omega) (hstate m z0 hs) (by simpa only [he] using hd0)
  have hn' : 2*zp+1=16*2^((D-m)+m)*r+L0+m+t+v := by
    simpa only [he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
  obtain ⟨v0,z0',s',hb0,hb,hzp,hs'⟩ :=
    precision_step (D-m) m L0 r m z0 (s*r) t v zp
       (by omega) ht (by simpa only [he] using hd0) hn'
  refine ⟨z0',s+8*2^(m+t+1),hclosed m z0 t v0 z0' hs hb0 hb,?_⟩
  rw [hzp,hs']
  simp [he, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

#print axioms no1024
#print axioms closed
end BB6.Agent8Adaptive
