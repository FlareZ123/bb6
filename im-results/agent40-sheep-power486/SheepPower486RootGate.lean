import SheepPower486All
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace SheepPower486

/-- Exclude every generic source admitted by the signed-power cutoff. -/
theorem no_generic_forbidden (h a t v : Nat)
    (hh : h ≤ 6) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (ht4 : t%4=0) (ht7 : t%7≠1) (ht9 : t%9≠2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(486*t+h+1)+3*3^h) : False := by
  rcases all_generic_gates h a t v hh ha hzero hpos heq with
    h1 | h2 | h3 | h4 | h5 | h6
  all_goals omega

#print axioms no_generic_forbidden
end SheepPower486
