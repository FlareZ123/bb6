import Raw11Extra28AllChildren

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The source-checked twelve-child Extra28 frontier can consume a bank of
independently certified literal partial tables without assuming any order,
without identifying machine count with quotient count, and without relying
on a fixed encoding. The parent proof uses only an injective table key
and independently checked key coverage.
-/
namespace BB6.Agent44Extra28CodeBank
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent44Extra28AllChildren

abbrev CertificateBank (B : Nat) :=
  List { p : PartialMachine // ∀ m, compatible p m → WeightedBound B m }

/-- A source-safe exact-key join. The proof bank's key values may be in
any order and may contain other certified tables; every one of the
twelve retained parent-child codes must appear in the bank. -/
theorem consume_bank (B : Nat) (hB : 42 ≤ B)
    (key : PartialMachine → Nat) (key_injective : Function.Injective key)
    (bank : CertificateBank B)
    (key_cover : ∀ k ∈ remaining.map key,
      k ∈ bank.map (fun e => key e.val)) :
    Cover (WeightedBound B) parent :=
  consume B hB (by
    intro q hq m hm
    have hk : key q ∈ remaining.map key :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    have hkb : key q ∈ bank.map (fun e => key e.val) :=
      key_cover (key q) hk
    obtain ⟨e, _, he⟩ := List.mem_map.mp hkb
    have hp : e.val = q := key_injective he
    rw [← hp] at hm
    exact e.property m hm)

#print axioms consume_bank
end BB6.Agent44Extra28CodeBank
