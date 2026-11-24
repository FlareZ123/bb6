import Type1Sufficiency
import EvenReach
namespace SheepWeightedResidual
open SheepEven

/-- The exact first-even edge with its hidden odd-run length retained. -/
def HiddenEdge (x y H : Nat) : Prop :=
  ∃ z v, Step x z ∧ 5≤z ∧ v%2=1 ∧ z=1+2^H*v ∧ y=1+3^H*v

theorem hidden_to_even {x y H : Nat} (he : HiddenEdge x y H) : EvenEdge x y := by
  obtain ⟨z,v,hs,hz,hv,h1,h2⟩ := he
  exact ⟨z,H,v,hs,hz,hv,h1,h2⟩

theorem hidden_terminal_iff (x d H B : Nat) (hs : Step x (1+d))
    (hd : 5≤1+d) (hB : 1≤B) :
    HiddenEdge x (2^B) H ↔ 3^H*d=2^H*(2^B-1) := by
  constructor
  · rintro ⟨z,v,hs',hz,hv,h1,h2⟩
    have hh := step_unique hs hs'
    have he : d=2^H*v := by omega
    have he' : 2^B-1=3^H*v := by omega
    rw [he,he']
    ac_rfl
  · intro he
    have hdvd : 2^H ∣ 3^H*d := ⟨2^B-1,he⟩
    have hcop : (2^H).Coprime (3^H) := Nat.Coprime.pow H H (by decide)
    obtain ⟨v,hv⟩ := hcop.dvd_of_dvd_mul_left hdvd
    rw [hv] at he
    have hh : 2^H*(3^H*v)=2^H*(2^B-1) := by
      rw [←he]
      ac_rfl
    have heq := Nat.mul_left_cancel (Nat.pow_pos (by decide : 0<2)) hh
    have hBpos : 1≤2^B := Nat.one_le_pow B 2 (by decide)
    have h2 : 2^B%2=0 := by
      obtain ⟨b,hb⟩ : ∃ b : Nat, B=b+1 := ⟨B-1,by omega⟩
      rw [hb,Nat.pow_succ]
      simp
    have h3 : 3^H%2=1 := by rw [Nat.pow_mod]; simp
    have h3v : (3^H*v)%2=1 := by omega
    rw [Nat.mul_mod,h3,Nat.one_mul,Nat.mod_mod] at h3v
    exact ⟨1+d,v,hs,hd,h3v,by rw [hv],by omega⟩

theorem type1_first (k : Nat) (hk : 1≤k) :
    HiddenEdge (2*(1+32*k)) (4*(1+30*k)) 1 := by
  have hs := Step.generic 1 (1+32*k) (by omega) (by omega)
  change Step (2*(1+32*k)) (2*(1+32*k)+1+((1+32*k)-1)/2) at hs
  have he : 2*(1+32*k)+1+((1+32*k)-1)/2=1+2*(1+40*k) := by omega
  rw [he] at hs
  exact ⟨1+2*(1+40*k),1+40*k,hs,by omega,by omega,by omega,by omega⟩

theorem type3_first (k : Nat) (hk : 1≤k) :
    HiddenEdge (8*(1+128*k)) (16*(1+102*k)) 1 := by
  have hs := Step.generic 3 (1+128*k) (by omega) (by omega)
  change Step (8*(1+128*k)) (8*(1+128*k)+3+((1+128*k)-1)/2) at hs
  have he : 8*(1+128*k)+3+((1+128*k)-1)/2=1+2*(5+544*k) := by omega
  rw [he] at hs
  exact ⟨1+2*(5+544*k),5+544*k,hs,by omega,by omega,by omega,by omega⟩

theorem type1_second_step (k : Nat) (hk : 1≤k) :
    Step (4*(1+30*k)) (1+(5+135*k)) := by
  have hs := Step.generic 2 (1+30*k) (by omega) (by omega)
  change Step (4*(1+30*k)) (4*(1+30*k)+2+((1+30*k)-1)/2) at hs
  have he : 4*(1+30*k)+2+((1+30*k)-1)/2=1+(5+135*k) := by omega
  rwa [he] at hs

theorem type3_second_step (k : Nat) (hk : 1≤k) :
    Step (16*(1+102*k)) (1+(19+1683*k)) := by
  have hs := Step.generic 4 (1+102*k) (by omega) (by omega)
  change Step (16*(1+102*k)) (16*(1+102*k)+4+((1+102*k)-1)/2) at hs
  have he : 16*(1+102*k)+4+((1+102*k)-1)/2=1+(19+1683*k) := by omega
  rwa [he] at hs

theorem type1_source_iff (k H B : Nat) (hk : 1≤k) (hB : 1≤B) :
    HiddenEdge (4*(1+30*k)) (2^B) H ↔ 3^H*(5+135*k)=2^H*(2^B-1) :=
  hidden_terminal_iff _ _ _ _ (type1_second_step k hk) (by omega) hB

theorem type3_source_iff (k H B : Nat) (hk : 1≤k) (hB : 1≤B) :
    HiddenEdge (16*(1+102*k)) (2^B) H ↔ 3^H*(19+1683*k)=2^H*(2^B-1) :=
  hidden_terminal_iff _ _ _ _ (type3_second_step k hk) (by omega) hB

theorem type1_prepared_iff (H : Nat) :
    (∃ k B : Nat, 1≤k ∧ 1≤B ∧ HiddenEdge (2*(1+32*k)) (4*(1+30*k)) 1 ∧
      HiddenEdge (4*(1+30*k)) (2^B) H) ↔ 1≤H := by
  constructor
  · rintro ⟨k,B,hk,hB,_,h⟩
    exact (type1_hidden_iff H).mp ⟨k,B,hk,hB,(type1_source_iff k H B hk hB).mp h⟩
  · intro hH
    obtain ⟨k,B,hk,hB,he⟩ := (type1_hidden_iff H).mpr hH
    exact ⟨k,B,hk,hB,type1_first k hk,(type1_source_iff k H B hk hB).mpr he⟩

theorem type3_prepared_iff (H : Nat) :
    (∃ k B : Nat, 1≤k ∧ 1≤B ∧ HiddenEdge (8*(1+128*k)) (16*(1+102*k)) 1 ∧
      HiddenEdge (16*(1+102*k)) (2^B) H) ↔ allowedType3 H := by
  constructor
  · rintro ⟨k,B,hk,hB,_,h⟩
    exact (type3_hidden_iff H).mp ⟨k,B,hk,hB,(type3_source_iff k H B hk hB).mp h⟩
  · intro hH
    obtain ⟨k,B,hk,hB,he⟩ := (type3_hidden_iff H).mpr hH
    exact ⟨k,B,hk,hB,type3_first k hk,(type3_source_iff k H B hk hB).mpr he⟩

theorem type1_source_bound (k H B : Nat) (hk : 1≤k) (hB : 1≤B)
    (he : HiddenEdge (4*(1+30*k)) (2^B) H) : 32≤B :=
  type1_terminal_all k H B hB ((type1_source_iff k H B hk hB).mp he)

theorem type3_source_bound (k H B : Nat) (hk : 1≤k) (hB : 1≤B)
    (he : HiddenEdge (16*(1+102*k)) (2^B) H) : 11502≤B :=
  type3_terminal_all k H B hB ((type3_source_iff k H B hk hB).mp he)

#print axioms type1_prepared_iff
#print axioms type3_prepared_iff
#print axioms type1_source_bound
#print axioms type3_source_bound
end SheepWeightedResidual
