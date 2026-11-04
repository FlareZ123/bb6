import S4NativeCompact
import S4LengthBridge
import S4SuffixBridge

namespace S4NativeCompact

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

def nativeReduced (T : List Nat) : Option (List Nat) :=
  (stepEpoch 27 (S4SourceShape.bumpN 31 T) [0,6,5,3,1]).map
    (fun s => _root_.bump17 ((unwrap s).2.drop 4))

theorem nativeReduced_eq_compactNext (T : List Nat) :
    nativeReduced T = _root_.compactNext T :=
  compact_exact_native_epoch T

theorem nativeReduced_exact_length (T U : List Nat)
    (hs : nativeReduced T = some U) (k t : Nat)
    (hp : _root_.W T + 45 = 2^k*(2*t+1)) :
    U.length = max T.length (k+2) := by
  exact S4Length.source_compact_length T U
    ((nativeReduced_eq_compactNext T).symm ▸ hs) k t hp

theorem nativeReduced_exact_tail (T U : List Nat)
    (hs : nativeReduced T = some U) (k t : Nat)
    (hp : _root_.W T + 45 = 2^k*(2*t+1))
    (hk : 1 ≤ k) (hlen : T.length ≤ k+1) :
    S4Length.Tail2 t U := by
  exact S4Length.source_compact_terminal_tail T U
    ((nativeReduced_eq_compactNext T).symm ▸ hs) k t hp hk hlen

#print axioms nativeReduced_eq_compactNext
#print axioms nativeReduced_exact_length
#print axioms nativeReduced_exact_tail
end S4NativeCompact
