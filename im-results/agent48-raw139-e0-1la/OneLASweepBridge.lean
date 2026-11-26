import Sweep4494
import Sweep9011
open BB6Coverage

namespace BB6.Agent48Raw139E0OneLASweeps.Sweep4494
def ctr : PartialMachine := BB6Coverage.Agent48.E0OneLA.p false
theorem never (m : Machine) (h : compatible ctr m) : NeverHalts m := BB6Coverage.Agent48.E0OneLA.nonhalt false m h
#print axioms never
end BB6.Agent48Raw139E0OneLASweeps.Sweep4494

namespace BB6.Agent48Raw139E0OneLASweeps.Sweep4700
def ctr : PartialMachine := BB6Coverage.Agent48.E0OneLA.p true
theorem never (m : Machine) (h : compatible ctr m) : NeverHalts m := BB6Coverage.Agent48.E0OneLA.nonhalt true m h
#print axioms never
end BB6.Agent48Raw139E0OneLASweeps.Sweep4700

namespace BB6.Agent48Raw139E0OneLASweeps.Sweep9011
def ctr : PartialMachine := BB6Coverage.Agent48.E0OneLA9011.p false
theorem never (m : Machine) (h : compatible ctr m) : NeverHalts m := BB6Coverage.Agent48.E0OneLA9011.nonhalt false m h
#print axioms never
end BB6.Agent48Raw139E0OneLASweeps.Sweep9011

namespace BB6.Agent48Raw139E0OneLASweeps.Sweep9012
def ctr : PartialMachine := BB6Coverage.Agent48.E0OneLA9011.p true
theorem never (m : Machine) (h : compatible ctr m) : NeverHalts m := BB6Coverage.Agent48.E0OneLA9011.nonhalt true m h
#print axioms never
end BB6.Agent48Raw139E0OneLASweeps.Sweep9012
