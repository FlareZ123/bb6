"""Make side-cycle proof composition explicit to avoid reducing long runs in unification."""
from pathlib import Path
import re,sys
root=Path(sys.argv[1]);p=root/'RayCycleProof.lean';s=p.read_text();a=s.index('theorem check :');j=s[:a]+'end BB6.Agent14LongCycle3732\n'
times=[*range(0,3273,128),3273,*range(3273+128,5814,128),5814]
pat=r'theorem join(\d+)_(\d+) : (finitePartialRun p|finiteWindow p true 99) (\d+) c\d+ = some c\d+ := (join_run|join_win) (\w+) (\w+)'
def explicit(x):
    a,z=int(x[1]),int(x[2]);m=(a+z)//2;args='p true 99' if x[5]=='join_win' else 'p'
    return x[0].replace(f'{x[5]} {x[6]} {x[7]}',f'@{x[5]} {args} {times[m]-times[a]} {times[z]-times[m]} c{a} c{m} c{z} {x[6]} {x[7]}')
j,n=re.subn(pat,explicit,j);assert n==44,n
(root/'RayCycleJoin.lean').write_text(j)
p.write_text('''import RayCycleJoin
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent50SideCycle BB6.Agent14RayLong
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent14LongCycle3732

theorem assemble (p : PartialMachine) (e k : Nat) (r : Bool) (b : Int) (c d : FinRayCfg)
    (h1 : finitePartialRun p e finiteBlank = some c) (h2 : finiteWindow p r b k c = some d)
    (h3 : finiteTailEq r b c d = true) : fastSideCycleCheck p e k r b = true := by
  simp only [fastSideCycleCheck,h1,h2,h3]

theorem tail : finiteTailEq true 99 c26 c46 = true := by decide +kernel
theorem check : fastSideCycleCheck p 3273 2541 true 99 = true := assemble p 3273 2541 true 99 c26 c46 join0_26 join26_46 tail
theorem never : ∀ m, compatible p m → NeverHalts m := fastSideCycleCheck_sound p 3273 2541 true 99 (by decide) check
#print axioms never
end BB6.Agent14LongCycle3732
''')
