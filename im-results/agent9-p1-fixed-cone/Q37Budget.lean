import Q37Proof0
import Q37Proof1
import UniformUniversalParamK
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent9Q37
theorem blank_no_critical_594_plus_2pow264 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(37+2^(10+250)*r)+2) -
       2*(16*(37+2^(10+250)*r)+2)-10) := by
  exact BB6.Agent9UniformParamK.universal_blank_critical_cylinder_param_K_of_predicates
    10 250 37 (by decide) (by decide)
    BB6.Agent9Q37Rows0.S0 BB6.Agent9Q37Rows1.S1
    BB6.Agent9Q37Rows0.root0 BB6.Agent9Q37Rows1.root1
    BB6.Agent9Q37Rows0.closed0 BB6.Agent9Q37Rows1.closed1
    BB6.Agent9Q37Rows0.small0 BB6.Agent9Q37Rows1.small1
    BB6.Agent9Q37Rows0.noCutoff0 BB6.Agent9Q37Rows1.noCutoff1 r
#print axioms blank_no_critical_594_plus_2pow264
end BB6.Agent9Q37
