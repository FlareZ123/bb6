import Core192All
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Agent38M192
open Agent41M192

theorem high_no_sum0 (a k c:Nat) (hz:(a+k)%4=0) : ¬ high a k c := by
  simp only [high]
  intro hh
  have ht : ((a+k)%192)%4=0 := by omega
  have hu : (((a+k)%192+48*((a+192-c%192)%192/96))%96)%4=0 := by omega
  rcases hh with h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega

theorem low_at_k2_c5to7 (a c:Nat) (hc:5≤c) (hd:c≤7) : ¬low a 2 c := by
  dsimp [low]
  intro hh
  rcases hh with ⟨_,_,hb⟩
  rcases hb with hk|hsp
  · omega
  · have hw : (2+c)%192≠11 := by omega
    exact hw hsp.2.1

theorem high_zero_even (k c:Nat) (hk:k%2=0) (hc:8≤c):
  ¬ bad (2*k+2) 2 (c-3) := by
  by_cases hlarge:11≤c
  · have hcc : ¬c-3<8 := by omega
    simp only [bad, if_neg hcc]
    apply high_no_sum0
    omega
  · have hcc : c-3<8 := by omega
    simp only [bad, if_pos hcc]
    apply low_at_k2_c5to7
    · omega
    · omega

#print axioms high_zero_even
end Agent38M192
