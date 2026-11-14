import SheepPower1458Special
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SheepPower1458
theorem no_inverse_source_cases (t h a u v : Nat)
    (ht : 1≤t) (ht3 : t%3≠0) (ha : 1≤a)
    (ht4 : t%4=0) (ht7 : t%7≠5) (ht9 : t%9≠1) (ht15 : t%15≠8)
    (hy : 2^(1458*t)=1+3^h*u)
    (heq :
      (3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)=2^(1458*t+h+1)+3*3^h) ∨
      (3^h*(3*2^a+a+2)+2^h=2^(1458*t+h))) : False := by
  have hh : h≤7 := target_hidden_le7 t h u ht3 hy
  rcases heq with hgen | hspe
  · exact no_generic_all_a h a t v hh ha ht4 ht7 ht9 ht15 hgen
  · exact no_special_all_a h a t hh ht hspe
#print axioms no_inverse_source_cases
end SheepPower1458
