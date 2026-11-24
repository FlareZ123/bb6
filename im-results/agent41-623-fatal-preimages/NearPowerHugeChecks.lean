import NearPowerGenerate

/-! Optional Lean 4.36.0-rc2 kernel reduction of the googol-exponent certificate. -/
namespace BB6.Agent41NearPower

def certHuge : Cert := Cert.fork
  (-13333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333611)
  (-39999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999729)
  Cert.stop Cert.stop

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem checkedHuge : check (fatalState (10^100)) certHuge=true := by decide +kernel

#print axioms checkedHuge
end BB6.Agent41NearPower
