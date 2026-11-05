import GenericCritical11
import Cost11Q942
namespace BB6.Agent8Cost11Q942
open BB6.Agent8Generic11

theorem critical_15074_mod16384_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(15074+16384*r)-2*(15074+16384*r)-10) := by
  have ht := critical_unreachable_of_shadow11 (942+1024*r) (by omega)
      (l0Nodes r) (l1Nodes r)
      (by simp [l0Nodes]; omega)
      (by simp [l1Nodes]; omega)
      (fun m z t v zp hm hd hn => l0_closed r m z t v zp hm hd hn)
      (fun m z t v zp hm hd hn => l1_closed r m z t v zp hm hd hn)
      (fun m z hm => l0_small r m z hm)
      (fun m z hm => l1_small r m z hm)
      (fun m z hm => l0_no256 r m z hm)
      (fun m z hm => l1_no256 r m z hm)
  have he : 16*(942+1024*r)+2=15074+16384*r := by omega
  simpa only [he] using ht

#print axioms critical_15074_mod16384_unreachable
end BB6.Agent8Cost11Q942
