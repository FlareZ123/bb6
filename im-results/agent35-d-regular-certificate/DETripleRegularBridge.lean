import DETripleLadder
namespace DETripleRegularBridge

/-- Exact natural 3-adic selector: 2*rise(n)+1=3^(n+1). -/
def rise : Nat → Nat
  | 0 => 1
  | n+1 => 3*rise n+1

theorem rise_power (n : Nat) : 2*rise n+1=3^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [rise, Nat.pow_succ]
    omega

def depth (v : Nat) : Nat := 2*v+1
def exceptionalK (v : Nat) : Nat := 9*rise (depth v)+4
def exceptionalQ (v : Nat) : Nat := 3*v+6

/-- The third exceptional F/0 packet in Agent31's k=9u+4 family,
    q=3v+6, is *exactly* the input to our arbitrary-depth E ladder of
    odd depth m=2v+1 and parameter u_ladder=256, r=4. This algebraic
    matching holds for every v with no finite sampling assumptions.

    The source three-return F/0 claim and the subsequent source E-lemma
    are distinct, explicit obligations for a genuine machine certificate. -/
theorem third_packet_is_ladder_input (v : Nat) :
    512*rise (depth v)+257 =
      DETripleLadder.unary (depth v) 256 ∧
    2*exceptionalQ v-6 = 3*(depth v)+3 ∧
    exceptionalK v = 9*rise (depth v)+4 := by
  have hp := rise_power (depth v)
  constructor
  · unfold DETripleLadder.unary
    omega
  constructor
  · simp [exceptionalQ, depth]
    omega
  · rfl

#print axioms rise_power
#print axioms third_packet_is_ladder_input
end DETripleRegularBridge
