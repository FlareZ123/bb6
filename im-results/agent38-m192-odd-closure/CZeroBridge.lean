import CZeroLarge
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Agent38M192
open Agent41M192

theorem high_period2 (a k c:Nat) :
 high a k c ↔ high (a%192) (k%192) (c%192) := by
  have hd : (a+192-c%192)%192 = (a%192+192-(c%192)%192)%192 := by omega
  have ht : (a+k)%192 = (a%192+k%192)%192 := by omega
  simp only [high]
  rw [hd,ht]

theorem czero_large_parent (a k:Nat) (ha:2≤a) (hk:4≤k)
    (hh: high (a-2) 1 (2*k+1)) : low a k 0 := by
  have hea : (a-2)%192=(a%192+190)%192 := by omega
  have hek : (2*k+1)%192=(2*(k%192)+1)%192 := by omega
  have hmod : high ((a%192+190)%192) 1 (2*(k%192)+1) := by
    apply (high_period2 ((a%192+190)%192) 1 (2*(k%192)+1)).2
    have hv := (high_period2 (a-2) 1 (2*k+1)).1 hh
    simpa only [Nat.mod_mod, Nat.one_mod, ← hea, ← hek] using hv
  have hcore := finite_c0 ⟨a%192,Nat.mod_lt _ (by decide)⟩
                             ⟨k%192,Nat.mod_lt _ (by decide)⟩ hmod
  have hk8 : 8≤k := by
    by_cases hk8:8≤k
    · exact hk8
    · change lowCore (a%192) (k%192) at hcore
      have hkm : k%192=k := by omega
      rw [hkm] at hcore
      have hs : k≤7 := by omega
      unfold lowCore at hcore
      omega
  dsimp [low]
  refine ⟨by decide, ?_⟩
  have hx : (a+192)%192=a%192 := by omega
  rw [hx]
  exact ⟨hcore,Or.inl hk8⟩

#print axioms czero_large_parent
end Agent38M192
