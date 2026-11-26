import Raw13GuardReturn
import Raw13CoupledEntry

namespace BB6.Agent46Raw13CoupledLive
open BB6.Agent46Raw13TapeValue
open BB6.Agent46Raw13CoupledEntry
open BB6.Agent46Raw13GuardReturn
open BB6.Agent46Raw13Detour

def Guard (z : NConf) : Prop := ∃ X : List Bool, z=F [true] ([true,true,true]++X++V)

theorem base_live : live base := by
  obtain ⟨n,_,he⟩ := entry
  apply invariant_live Guard n (F [true] guardWord) he
  · obtain ⟨X,hX⟩ := guard_shape
    exact ⟨X,congrArg (F [true]) (by simpa [V,List.append_assoc,BB6.Agent46Raw13RightCounter.zeros] using hX)⟩
  · intro z hz
    obtain ⟨X,rfl⟩ := hz
    obtain ⟨Q,hQ⟩ := guardReturn X
    exact ⟨_,hQ,⟨Q,rfl⟩⟩

#print axioms base_live
end BB6.Agent46Raw13CoupledLive
