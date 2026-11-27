import Raw140DoubleClosure
import Raw140Sweep
namespace Raw140Double
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Sweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace X4
def s0 : RState := ⟨2,true,[(S 6,1)],[]⟩
def s1 : RState := ⟨2,true,[(S 4,1),(S 5,3),(S 6,4),(S 4,1)],[(S 4,7),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e1 : Raw140Sweep.execute M4 512 s0 = some (1824,s1) := by decide +kernel
def s2 : RState := ⟨1,false,[(S 1,1),(S 5,1),(S 4,1),(S 5,14),(S 4,1)],[(S 6,2),(S 2,1)]⟩
theorem e2 : Raw140Sweep.execute M4 512 s1 = some (1542,s2) := by decide +kernel
def s3 : RState := ⟨4,true,[(S 1,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,5),(S 6,28),(S 4,1)],[(S 4,2)]⟩
theorem e3 : Raw140Sweep.execute M4 512 s2 = some (4037,s3) := by decide +kernel
def s4 : RState := ⟨4,true,[(S 0,1),(S 5,5),(S 6,23),(S 4,1)],[(S 4,5),(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e4 : Raw140Sweep.execute M4 512 s3 = some (1556,s4) := by decide +kernel
def s5 : RState := ⟨2,true,[(S 4,1),(S 5,13),(S 6,20),(S 4,1)],[(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e5 : Raw140Sweep.execute M4 512 s4 = some (1533,s5) := by decide +kernel
def s6 : RState := ⟨1,false,[(S 0,1),(S 5,8),(S 6,17),(S 4,1)],[(S 4,8),(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e6 : Raw140Sweep.execute M4 512 s5 = some (1577,s6) := by decide +kernel
def s7 : RState := ⟨1,false,[(S 0,1),(S 4,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,18),(S 6,15),(S 4,1)],[(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e7 : Raw140Sweep.execute M4 512 s6 = some (1528,s7) := by decide +kernel
def s8 : RState := ⟨2,true,[(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,20),(S 6,13),(S 4,1)],[(S 6,1),(S 4,1),(S 2,1),(S 1,1)]⟩
theorem e8 : Raw140Sweep.execute M4 512 s7 = some (1548,s8) := by decide +kernel
def s9 : RState := ⟨2,true,[(S 5,1),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,22),(S 6,11),(S 4,1)],[(S 6,1),(S 4,1),(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e9 : Raw140Sweep.execute M4 512 s8 = some (1566,s9) := by decide +kernel
def s10 : RState := ⟨1,false,[(S 0,1),(S 5,1),(S 4,1),(S 5,24),(S 6,9),(S 4,1)],[(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e10 : Raw140Sweep.execute M4 512 s9 = some (1584,s10) := by decide +kernel
def s11 : RState := ⟨2,true,[(S 5,14),(S 6,7),(S 4,1)],[(S 6,1),(S 4,12),(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 2,1),(S 1,1)]⟩
theorem e11 : Raw140Sweep.execute M4 512 s10 = some (1600,s11) := by decide +kernel
def s12 : RState := ⟨3,false,[(S 5,3),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,27),(S 6,6),(S 4,1)],[(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e12 : Raw140Sweep.execute M4 512 s11 = some (1500,s12) := by decide +kernel
def s13 : RState := ⟨2,true,[(S 4,1),(S 5,23),(S 6,4),(S 4,1)],[(S 4,6),(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1)]⟩
theorem e13 : Raw140Sweep.execute M4 512 s12 = some (1615,s13) := by decide +kernel
def s14 : RState := ⟨2,true,[(S 5,3),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,1),(S 4,1),(S 5,30),(S 6,3),(S 4,1)],[(S 4,1),(S 2,2),(S 1,1)]⟩
theorem e14 : Raw140Sweep.execute M4 512 s13 = some (1513,s14) := by decide +kernel
def s15 : RState := ⟨4,true,[(S 0,1),(S 5,17),(S 6,1),(S 4,1)],[(S 4,15),(S 6,1),(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 2,1),(S 1,1)]⟩
theorem e15 : Raw140Sweep.execute M4 512 s14 = some (1654,s15) := by decide +kernel
def s16 : RState := ⟨1,false,[(S 1,1),(S 5,1),(S 4,1),(S 5,1),(S 4,1),(S 5,33),(S 4,1)],[(S 6,2),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 0,1),(S 5,1)]⟩
theorem e16 : Raw140Sweep.execute M4 512 s15 = some (1524,s16) := by decide +kernel
def s17 : RState := ⟨3,false,[(S 5,1),(S 2,1),(S 4,2),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,70)],[(S 6,1),(S 2,1)]⟩
theorem e17 : Raw140Sweep.execute M4 512 s16 = some (11596,s17) := by decide +kernel
def s18 : RState := ⟨1,true,[(S 5,78)],[(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1)]⟩
theorem e18 : Raw140Sweep.execute M4 62 s17 = some (2834,s18) := by decide +kernel
theorem entry : run M4 42133 primBlank = some (section 78 5 .s62) := by
  have h0 : run M4 2 primBlank = some s0.prim := run_ext M4 (fill_extends _ _) _ _ _ base_start
  have h1 := join h0 (Raw140Sweep.execute_sound M4 512 1824 s0 s1 e1)
  have h2 := join h1 (Raw140Sweep.execute_sound M4 512 1542 s1 s2 e2)
  have h3 := join h2 (Raw140Sweep.execute_sound M4 512 4037 s2 s3 e3)
  have h4 := join h3 (Raw140Sweep.execute_sound M4 512 1556 s3 s4 e4)
  have h5 := join h4 (Raw140Sweep.execute_sound M4 512 1533 s4 s5 e5)
  have h6 := join h5 (Raw140Sweep.execute_sound M4 512 1577 s5 s6 e6)
  have h7 := join h6 (Raw140Sweep.execute_sound M4 512 1528 s6 s7 e7)
  have h8 := join h7 (Raw140Sweep.execute_sound M4 512 1548 s7 s8 e8)
  have h9 := join h8 (Raw140Sweep.execute_sound M4 512 1566 s8 s9 e9)
  have h10 := join h9 (Raw140Sweep.execute_sound M4 512 1584 s9 s10 e10)
  have h11 := join h10 (Raw140Sweep.execute_sound M4 512 1600 s10 s11 e11)
  have h12 := join h11 (Raw140Sweep.execute_sound M4 512 1500 s11 s12 e12)
  have h13 := join h12 (Raw140Sweep.execute_sound M4 512 1615 s12 s13 e13)
  have h14 := join h13 (Raw140Sweep.execute_sound M4 512 1513 s13 s14 e14)
  have h15 := join h14 (Raw140Sweep.execute_sound M4 512 1654 s14 s15 e15)
  have h16 := join h15 (Raw140Sweep.execute_sound M4 512 1524 s15 s16 e16)
  have h17 := join h16 (Raw140Sweep.execute_sound M4 512 11596 s16 s17 e17)
  have h18 := join h17 (Raw140Sweep.execute_sound M4 62 2834 s17 s18 e18)
  exact h18
theorem good : Good (section 78 5 .s62) := ⟨39,3,_,by decide,rfl⟩
theorem forever (k : Nat) : ∃ c, run M4 k primBlank = some c := foreverEntry M4 progress4 42133 _ good entry k
#print axioms forever
end X4
namespace X13
def s0 : RState := ⟨2,true,[(S 6,1)],[]⟩
def s1 : RState := ⟨2,true,[(S 4,1),(S 5,3),(S 6,4),(S 4,1)],[(S 4,7),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e1 : Raw140Sweep.execute M13 512 s0 = some (1824,s1) := by decide +kernel
def s2 : RState := ⟨1,false,[(S 1,1),(S 5,1),(S 4,1),(S 5,14),(S 4,1)],[(S 6,2),(S 2,1)]⟩
theorem e2 : Raw140Sweep.execute M13 512 s1 = some (1542,s2) := by decide +kernel
def s3 : RState := ⟨1,false,[(S 1,1),(S 5,5),(S 6,29),(S 4,1)],[(S 6,1),(S 4,3),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e3 : Raw140Sweep.execute M13 512 s2 = some (4100,s3) := by decide +kernel
def s4 : RState := ⟨2,true,[(S 5,4),(S 6,24),(S 4,1)],[(S 6,1),(S 4,10),(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e4 : Raw140Sweep.execute M13 512 s3 = some (1576,s4) := by decide +kernel
def s5 : RState := ⟨3,false,[(S 4,1),(S 5,12),(S 6,21),(S 4,1)],[(S 6,1),(S 4,4),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 0,1),(S 5,1)]⟩
theorem e5 : Raw140Sweep.execute M13 512 s4 = some (1555,s5) := by decide +kernel
def s6 : RState := ⟨3,false,[(S 4,1),(S 5,8),(S 6,18),(S 4,1)],[(S 6,1),(S 4,11),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e6 : Raw140Sweep.execute M13 512 s5 = some (1583,s6) := by decide +kernel
def s7 : RState := ⟨4,true,[(S 1,1),(S 5,21),(S 6,16),(S 4,1)],[(S 6,2),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 2,1),(S 1,1)]⟩
theorem e7 : Raw140Sweep.execute M13 512 s6 = some (1548,s7) := by decide +kernel
def s8 : RState := ⟨2,true,[(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,24),(S 6,14),(S 4,1)],[(S 6,2),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e8 : Raw140Sweep.execute M13 512 s7 = some (1552,s8) := by decide +kernel
def s9 : RState := ⟨4,true,[(S 0,1),(S 4,1),(S 5,2),(S 4,1),(S 5,2),(S 4,1),(S 5,26),(S 6,12),(S 4,1)],[(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e9 : Raw140Sweep.execute M13 512 s8 = some (1574,s9) := by decide +kernel
def s10 : RState := ⟨1,false,[(S 0,1),(S 5,26),(S 6,10),(S 4,1)],[(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 2,1),(S 1,1)]⟩
theorem e10 : Raw140Sweep.execute M13 512 s9 = some (1594,s10) := by decide +kernel
def s11 : RState := ⟨4,true,[(S 0,1),(S 5,15),(S 6,8),(S 4,1)],[(S 4,15),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e11 : Raw140Sweep.execute M13 512 s10 = some (1608,s11) := by decide +kernel
def s12 : RState := ⟨4,true,[(S 1,1),(S 5,31),(S 6,7),(S 4,1)],[(S 4,3),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1)]⟩
theorem e12 : Raw140Sweep.execute M13 512 s11 = some (1531,s12) := by decide +kernel
def s13 : RState := ⟨4,true,[(S 0,1),(S 5,24),(S 6,5),(S 4,1)],[(S 4,9),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e13 : Raw140Sweep.execute M13 512 s12 = some (1603,s13) := by decide +kernel
def s14 : RState := ⟨1,false,[(S 1,1),(S 5,2),(S 4,1),(S 5,34),(S 6,4),(S 4,1)],[(S 4,3),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,1),(S 0,1),(S 5,1)]⟩
theorem e14 : Raw140Sweep.execute M13 512 s13 = some (1543,s14) := by decide +kernel
def s15 : RState := ⟨4,true,[(S 1,1),(S 5,19),(S 6,2),(S 4,1)],[(S 6,1),(S 4,16),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1),(S 5,1),(S 4,1),(S 2,1)]⟩
theorem e15 : Raw140Sweep.execute M13 512 s14 = some (1631,s15) := by decide +kernel
def s16 : RState := ⟨4,true,[(S 0,1),(S 5,1),(S 4,1),(S 5,2),(S 4,1),(S 5,37),(S 6,1),(S 4,1)],[(S 4,1),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,1)]⟩
theorem e16 : Raw140Sweep.execute M13 512 s15 = some (1520,s16) := by decide +kernel
def s17 : RState := ⟨4,false,[(S 2,1)],[(S 1,1),(S 5,1),(S 4,38),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e17 : Raw140Sweep.execute M13 512 s16 = some (1688,s17) := by decide +kernel
def s18 : RState := ⟨1,true,[(S 5,80)],[(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 4,2),(S 6,1),(S 2,2),(S 1,1)]⟩
theorem e18 : Raw140Sweep.execute M13 311 s17 = some (14855,s18) := by decide +kernel
theorem entry : run M13 44429 primBlank = some (section 80 5 .s6221) := by
  have h0 : run M13 2 primBlank = some s0.prim := run_ext M13 (fill_extends _ _) _ _ _ base_start
  have h1 := join h0 (Raw140Sweep.execute_sound M13 512 1824 s0 s1 e1)
  have h2 := join h1 (Raw140Sweep.execute_sound M13 512 1542 s1 s2 e2)
  have h3 := join h2 (Raw140Sweep.execute_sound M13 512 4100 s2 s3 e3)
  have h4 := join h3 (Raw140Sweep.execute_sound M13 512 1576 s3 s4 e4)
  have h5 := join h4 (Raw140Sweep.execute_sound M13 512 1555 s4 s5 e5)
  have h6 := join h5 (Raw140Sweep.execute_sound M13 512 1583 s5 s6 e6)
  have h7 := join h6 (Raw140Sweep.execute_sound M13 512 1548 s6 s7 e7)
  have h8 := join h7 (Raw140Sweep.execute_sound M13 512 1552 s7 s8 e8)
  have h9 := join h8 (Raw140Sweep.execute_sound M13 512 1574 s8 s9 e9)
  have h10 := join h9 (Raw140Sweep.execute_sound M13 512 1594 s9 s10 e10)
  have h11 := join h10 (Raw140Sweep.execute_sound M13 512 1608 s10 s11 e11)
  have h12 := join h11 (Raw140Sweep.execute_sound M13 512 1531 s11 s12 e12)
  have h13 := join h12 (Raw140Sweep.execute_sound M13 512 1603 s12 s13 e13)
  have h14 := join h13 (Raw140Sweep.execute_sound M13 512 1543 s13 s14 e14)
  have h15 := join h14 (Raw140Sweep.execute_sound M13 512 1631 s14 s15 e15)
  have h16 := join h15 (Raw140Sweep.execute_sound M13 512 1520 s15 s16 e16)
  have h17 := join h16 (Raw140Sweep.execute_sound M13 512 1688 s16 s17 e17)
  have h18 := join h17 (Raw140Sweep.execute_sound M13 311 14855 s17 s18 e18)
  exact h18
theorem good : Good (section 80 5 .s6221) := ⟨40,3,_,by decide,rfl⟩
theorem forever (k : Nat) : ∃ c, run M13 k primBlank = some c := foreverEntry M13 progress13 44429 _ good entry k
#print axioms forever
end X13
end Raw140Double
