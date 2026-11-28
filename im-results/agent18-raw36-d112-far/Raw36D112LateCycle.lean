import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent18Raw36D112LateCycle
open BB6Coverage BB6Coverage.Agent10ZipAudit BB6Coverage.FAR
namespace M22
def table : PartialMachine := FAR.fromCodes [7, 16, 11, 20, 13, 3, 12, 2, 6, 0, 24, 1]
theorem checked : zipCycle table 965 334 false (7) = true := by decide
theorem never : ∀ m, compatible table m → NeverHalts m := zipCycle_sound table 965 334 false (7) (by decide) checked
#print axioms never
end M22
namespace M71
def table : PartialMachine := FAR.fromCodes [7, 19, 11, 3, 13, 24, 12, 2, 5, 21, 14, 20]
theorem checked : zipCycle table 1391 462 false (-11) = true := by decide
theorem never : ∀ m, compatible table m → NeverHalts m := zipCycle_sound table 1391 462 false (-11) (by decide) checked
#print axioms never
end M71
namespace M72
def table : PartialMachine := FAR.fromCodes [7, 19, 11, 3, 13, 24, 12, 2, 2, 21, 14, 17]
theorem checked : zipCycle table 505 1110 true (2) = true := by decide
theorem never : ∀ m, compatible table m → NeverHalts m := zipCycle_sound table 505 1110 true (2) (by decide) checked
#print axioms never
end M72
namespace M73
def table : PartialMachine := FAR.fromCodes [7, 19, 11, 3, 13, 24, 12, 2, 15, 21, 14, 17]
theorem checked : zipCycle table 730 317 true (8) = true := by decide
theorem never : ∀ m, compatible table m → NeverHalts m := zipCycle_sound table 730 317 true (8) (by decide) checked
#print axioms never
end M73
end BB6.Agent18Raw36D112LateCycle
