import BB429Rank
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace BB429ElevenSeed

set_option maxHeartbeats 3000000 in
/-- Every genuine non-first accelerated transition which enters the
    u=11 reset ray has the second counter exactly 2 modulo 4. -/
theorem reset_to_eleven_mod4 (u w v : Nat)
    (hfirst : w < 2*u+3)
    (hs : BB429.next (u,w) = some (11,v)) :
    v%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- For a u=11 seed with v=2 mod4, an exact first-branch burst ending on
    the halting gateway has burst length n≡1 (mod4). -/
theorem eleven_burst_gateway_length (v n a b : Nat)
    (hv : v%4=2)
    (hr : BB429Burst.firstRun n (11,v)=some (a,b))
    (hg : b+1=2*a) : n%4=1 := by
  have he := (BB429Burst.gateway_iff_exponential 11 v n a b hr).mp hg
  omega

/-- Any actual non-first incoming u=11 reset, followed by an exact
    first-only burst that reaches a halt, must have n≡1 (mod4). -/
theorem reset_eleven_halting_burst (u w v n a b : Nat)
    (hfirst : w < 2*u+3)
    (hs : BB429.next (u,w)=some (11,v))
    (hr : BB429Burst.firstRun n (11,v)=some (a,b))
    (hg : b+1=2*a) : n%4=1 :=
  eleven_burst_gateway_length v n a b (reset_to_eleven_mod4 u w v hfirst hs) hr hg

#print axioms reset_to_eleven_mod4
#print axioms eleven_burst_gateway_length
#print axioms reset_eleven_halting_burst
end BB429ElevenSeed
