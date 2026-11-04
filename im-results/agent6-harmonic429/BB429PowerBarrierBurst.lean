import BB429Burst
import BB429PowerBarrier
namespace BB429PowerBarrierBurst

/-- Every certified first-branch prefix of length at least k terminates in
    first counter a satisfying a+3 divisible by 2^k. -/
theorem first_run_endpoint_mod (u w n a b k : Nat)
    (h : BB429Burst.firstRun n (u,w) = some (a,b))
    (hk : k ≤ n) : (a+3)%(2^k)=0 :=
  BB429PowerBarrier.long_first_burst_divisible u a n k hk
    (BB429Burst.prefix_formula u w n a b h).1

/-- Long first-branch prefix endpoints have a ≡ 29 (mod 32), a surviving
    global BB429 halting-gate residue. -/
theorem first_run_long_mod32 (u w n a b : Nat)
    (h : BB429Burst.firstRun n (u,w) = some (a,b))
    (hn : 5 ≤ n) : a%32=29 :=
  BB429PowerBarrier.any_long_burst_terminal_mod32 u a n hn
    (BB429Burst.prefix_formula u w n a b h).1

#print axioms first_run_endpoint_mod
#print axioms first_run_long_mod32
end BB429PowerBarrierBurst
