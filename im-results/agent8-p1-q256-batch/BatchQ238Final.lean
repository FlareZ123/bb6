import GenericCritical
import BatchQ238
namespace BB6.Agent8BatchQ238
open BB6.Agent8Generic

theorem critical_3810_mod4096_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(3810+4096*r)-2*(3810+4096*r)-10) := by
  have ht := critical_unreachable_of_shadow (238+256*r) (by omega)
      (l0Nodes r) (l1Nodes r)
      (by simp [l0Nodes]; omega)
      (by simp [l1Nodes]; omega)
      (fun m z t v zp hm hd hn => l0_closed r m z t v zp hm hd hn)
      (fun m z t v zp hm hd hn => l1_closed r m z t v zp hm hd hn)
      (fun m z hm => l0_small r m z hm)
      (fun m z hm => l1_small r m z hm)
      (fun m z hm => l0_no256 r m z hm)
      (fun m z hm => l1_no256 r m z hm)
  have he : 16*(238+256*r)+2=3810+4096*r := by omega
  simpa only [he] using ht

#print axioms critical_3810_mod4096_unreachable
end BB6.Agent8BatchQ238
