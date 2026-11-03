import EvenPeriod
set_option maxRecDepth 32768
set_option exponentiation.threshold 10000
namespace SheepEvenCert

/-- No h above the listed uniform cutoff for case 138, node 0. -/
theorem root138_node0_hstop (k : Nat) : 2^(138+4860*k)%27 ≠ 1 := by
  have hp : 2^18%27=1 := by decide
  have h := pow_mod_period 27 18 138 (270*k) (by decide) hp
  have he : 138+4860*k=138+18*(270*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 138, node 1. -/
theorem root138_node1_hstop (k : Nat) : 2^(141+4860*k)%1215 ≠ 17 := by
  have hp : 2^324%1215=1 := by decide
  have h := pow_mod_period 1215 324 141 (15*k) (by decide) hp
  have he : 141+4860*k=141+324*(15*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 138, node 2. -/
theorem root138_node2_hstop (k : Nat) : 2^(143+4860*k)%729 ≠ 149 := by
  have hp : 2^486%729=1 := by decide
  have h := pow_mod_period 729 486 143 (10*k) (by decide) hp
  have he : 143+4860*k=143+486*(10*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 402, node 0. -/
theorem root402_node0_hstop (k : Nat) : 2^(402+4860*k)%27 ≠ 1 := by
  have hp : 2^18%27=1 := by decide
  have h := pow_mod_period 27 18 402 (270*k) (by decide) hp
  have he : 402+4860*k=402+18*(270*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 402, node 1. -/
theorem root402_node1_hstop (k : Nat) : 2^(405+4860*k)%135 ≠ 17 := by
  have hp : 2^36%135=1 := by decide
  have h := pow_mod_period 135 36 405 (135*k) (by decide) hp
  have he : 405+4860*k=405+36*(135*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 402, node 2. -/
theorem root402_node2_hstop (k : Nat) : 2^(411+4860*k)%13365 ≠ 6173 := by
  have hp : 2^1620%13365=1 := by decide
  have h := pow_mod_period 13365 1620 411 (3*k) (by decide) hp
  have he : 411+4860*k=411+1620*(3*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1218, node 0. -/
theorem root1218_node0_hstop (k : Nat) : 2^(1218+4860*k)%27 ≠ 1 := by
  have hp : 2^18%27=1 := by decide
  have h := pow_mod_period 27 18 1218 (270*k) (by decide) hp
  have he : 1218+4860*k=1218+18*(270*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1218, node 1. -/
theorem root1218_node1_hstop (k : Nat) : 2^(1221+4860*k)%1215 ≠ 17 := by
  have hp : 2^324%1215=1 := by decide
  have h := pow_mod_period 1215 324 1221 (15*k) (by decide) hp
  have he : 1221+4860*k=1221+324*(15*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1218, node 2. -/
theorem root1218_node2_hstop (k : Nat) : 2^(1223+4860*k)%243 ≠ 149 := by
  have hp : 2^162%243=1 := by decide
  have h := pow_mod_period 243 162 1223 (30*k) (by decide) hp
  have he : 1223+4860*k=1223+162*(30*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1738, node 0. -/
theorem root1738_node0_hstop (k : Nat) : 2^(1738+4860*k)%9 ≠ 1 := by
  have hp : 2^6%9=1 := by decide
  have h := pow_mod_period 9 6 1738 (810*k) (by decide) hp
  have he : 1738+4860*k=1738+6*(810*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1738, node 1. -/
theorem root1738_node1_hstop (k : Nat) : 2^(1741+4860*k)%45 ≠ 17 := by
  have hp : 2^12%45=1 := by decide
  have h := pow_mod_period 45 12 1741 (405*k) (by decide) hp
  have he : 1741+4860*k=1741+12*(405*k) := by omega
  rw [he,h]
  decide

/-- No h above the listed uniform cutoff for case 1738, node 2. -/
theorem root1738_node2_hstop (k : Nat) : 2^(1744+4860*k)%3645 ≠ 331 := by
  have hp : 2^972%3645=1 := by decide
  have h := pow_mod_period 3645 972 1744 (5*k) (by decide) hp
  have he : 1744+4860*k=1744+972*(5*k) := by omega
  rw [he,h]
  decide

#print axioms root138_node0_hstop
#print axioms root138_node1_hstop
#print axioms root138_node2_hstop
#print axioms root402_node0_hstop
#print axioms root402_node1_hstop
#print axioms root402_node2_hstop
#print axioms root1218_node0_hstop
#print axioms root1218_node1_hstop
#print axioms root1218_node2_hstop
#print axioms root1738_node0_hstop
#print axioms root1738_node1_hstop
#print axioms root1738_node2_hstop
end SheepEvenCert
