import S4LengthBridge
import S4Suffix

namespace S4Length

theorem source_compact_terminal_tail (T U : List Nat)
    (h : _root_.compactNext T = some U)
    (k t : Nat) (hp : _root_.W T + 45 = 2^k*(2*t+1))
    (hk : 1 ≤ k) (hlen : T.length ≤ k+1) :
    Tail2 t U := by
  apply F_terminal_tail T U ((F_eq_original T).trans h) k t
  · simpa [W_eq_original] using hp
  · exact hk
  · exact hlen

#print axioms source_compact_terminal_tail
end S4Length
