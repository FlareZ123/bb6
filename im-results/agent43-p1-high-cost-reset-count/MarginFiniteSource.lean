import MarginSource
import Margin30
import Margin350

namespace BB6.Agent43MarginSource
open BB6.Agent43CarryCert
theorem critical_reset_no_reach_30 :
    ¬ BB6.Agent1.Reach 2 (14*2^30-2*30-10) :=
  critical_reset_no_reach_of_margin 30 82 (by decide) (by decide) margin30

theorem critical_reset_no_reach_350 :
    ¬ BB6.Agent1.Reach 2 (14*2^350-2*350-10) :=
  critical_reset_no_reach_of_margin 350 586 (by decide) (by decide) margin350

#print axioms critical_reset_no_reach_30
#print axioms critical_reset_no_reach_350
end BB6.Agent43MarginSource
