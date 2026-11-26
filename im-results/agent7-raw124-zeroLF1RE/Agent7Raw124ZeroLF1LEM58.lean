import Raw124ZeroLF1LE1393
namespace BB6.Agent7Raw124ZeroLF1LEM58
open BB6Coverage
abbrev table : PartialMachine := BB6.Agent2Raw124ZeroLF1LE1393.table
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent2Raw124ZeroLF1LE1393.never m hm
#print axioms never
end BB6.Agent7Raw124ZeroLF1LEM58
