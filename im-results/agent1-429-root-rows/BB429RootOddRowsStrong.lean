import BB429NewResidue
import BB429NewRootRows
import Lean.Elab.Tactic.Omega

namespace BB429RootOddRowsStrong

open BB429NewResidue

set_option maxHeartbeats 15000000
set_option maxRecDepth 16000

/--
A two-step inverse obstruction: a genuine root-reachable state with
a >= 33, a = 9 mod 16, and b = 5 mod 8 cannot occur.
-/
theorem rooted_not_9_5 (a b : Nat) (hr : Reach a b)
    (ha : 33 <= a) (ha16 : a % 16 = 9) (hb8 : b % 8 = 5) : False := by
  have hao : a % 2 = 1 := by omega
  rcases odd_back a b (by omega) hao hr with
    ⟨p,q,hpq,hpa,hqb⟩ |
    ⟨p,q,hpq,hpa,hqb,hb4⟩
  · have hp15 : 15 <= p := by omega
    have hpodd : p % 2 = 1 := by omega
    have hp4 : p % 4 = 3 := by omega
    have hq8 : q % 8 = 6 := by omega
    rcases odd_back p q (by omega) hpodd hpq with
      ⟨r,s,hrs,hpr,hsq⟩ |
      ⟨r,s,hrs,hpr,hsq,hq4⟩
    · have hr6 : 6 <= r := by omega
      have hrEven : r % 2 = 0 := by omega
      have hs4 : s % 4 = 1 := by omega
      rcases even_back r s hr6 hrEven hrs with ⟨u,v,huv,h1,h2,hs2⟩
      omega
    · have hb5 : 5 <= b := by omega
      have hq38 : 38 <= q := by omega
      have hr6 : 6 <= r := by omega
      have hrEven : r % 2 = 0 := by omega
      have hs4 : s % 4 = 1 := by omega
      rcases even_back r s hr6 hrEven hrs with ⟨u,v,huv,h1,h2,hs2⟩
      omega
  · omega

/--
A two-step inverse obstruction: a root-reachable state with
a ≥ 33, a = 13 mod 32, and b = 1 mod 8 cannot occur.
-/
theorem rooted_not_13_1 (a b : Nat) (hr : Reach a b)
    (ha : 33 ≤ a) (ha32 : a % 32 = 13) (hb8 : b % 8 = 1) : False := by
  have hao : a % 2 = 1 := by omega
  rcases odd_back a b (by omega) hao hr with
    ⟨p,q,hpq,hpa,hqb⟩ |
    ⟨p,q,hpq,hpa,hqb,hb4⟩
  · have hp15 : 15 ≤ p := by omega
    have hp16 : p % 16 = 5 := by omega
    have hq8 : q % 8 = 6 := by omega
    rcases odd_back p q (by omega) (by omega) hpq with
      ⟨r,s,hrs,hpr,hsq⟩ |
      ⟨r,s,hrs,hpr,hsq,hq4⟩
    · have hr8 : r % 8 = 1 := by omega
      have hs4 : s % 4 = 3 := by omega
      have hall := reach_allowed r s hrs
      unfold BB429Mod8.Allowed at hall
      omega
    · have hr6 : 6 ≤ r := by omega
      have hrEven : r % 2 = 0 := by omega
      have hs4 : s % 4 = 1 := by omega
      obtain ⟨u,v,huv,h1,h2,hs2⟩ := even_back r s hr6 hrEven hrs
      omega
  · omega

#print axioms rooted_not_13_1

end BB429RootOddRowsStrong
