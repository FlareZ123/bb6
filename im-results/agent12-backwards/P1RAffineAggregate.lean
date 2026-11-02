import P1RAffineGeneral
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace BB6.Agent12Affine

/-- Exact 187 disjoint new residual critical-index families modulo 65536. -/
def extraResidues : List Nat := [
  382, 542, 574, 942, 1054, 1262, 1406, 1550, 1838, 2174, 2398, 2446,
  2654, 2798, 3214, 3614, 3678, 5358, 6062, 6286, 6414, 6670, 6734, 6894,
  7134, 7486, 7918, 7934, 9134, 10030, 10558, 10638, 11006, 11054, 11070, 11390,
  11406, 11614, 11662, 12254, 12318, 12526, 12670, 12862, 13230, 13310, 13550, 13838,
  14254, 14478, 14606, 14862, 14926, 15086, 16110, 16190, 16350, 16558, 16606, 18350,
  18430, 19246, 19534, 19678, 19854, 20046, 20206, 20222, 20558, 20718, 21022, 21422,
  21534, 22030, 22878, 23134, 23294, 23342, 23358, 23678, 23774, 24094, 24158, 24750,
  24814, 25598, 25870, 26542, 26766, 27614, 27726, 28238, 28398, 28478, 28750, 28846,
  29742, 30078, 30846, 31534, 31710, 32094, 32798, 33006, 34062, 34958, 35582, 36158,
  36190, 36830, 36894, 37038, 37086, 37934, 39230, 40014, 40526, 40766, 41006, 41038,
  41342, 41502, 41534, 42014, 42030, 42366, 43134, 43358, 43614, 44206, 44254, 44574,
  44638, 45598, 46110, 46350, 47502, 47870, 48206, 48446, 48718, 48894, 49198, 49230,
  50174, 50222, 51470, 51518, 51726, 51790, 52030, 52190, 52350, 52398, 53054, 53294,
  53630, 53822, 54542, 54654, 55086, 55422, 55694, 56462, 56494, 56670, 56718, 57310,
  57374, 58606, 58894, 59662, 59918, 59982, 60142, 60734, 61182, 61486, 61662, 63278,
  63806, 63838, 64094, 64318, 64910, 65054, 65118
]

def residueOK (R:Nat) : Bool :=
  decide (32≤R ∧ R%2=0 ∧ 2*R+16≤131072) &&
    goodAff 12 (131072,131072-2*R-16) (0,3)

theorem all_extra_checked : extraResidues.all residueOK = true := by
  decide +kernel

/-- One kernel-checking theorem for the full 187-parameter new P1 class set. -/
theorem blank_no_critical_extra (R q:Nat)
    (h : R ∈ extraResidues) :
    ¬BB6.Agent1.Reach 2
       (14*2^(65536*q+R)-2*(65536*q+R)-10) := by
  have hcheck := (List.all_eq_true.mp all_extra_checked) R h
  simp only [residueOK] at hcheck
  obtain ⟨hb,hgood⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hR,he,hConst⟩ := of_decide_eq_true hb
  exact blank_no_critical_of_affine_check R q hR he hConst hgood

#print axioms all_extra_checked
#print axioms blank_no_critical_extra
end BB6.Agent12Affine
