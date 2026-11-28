import TraceLogic
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (pre_append zeros_blank b)
open PrefixCheck

def blankStart : Config := ⟨Q.A, blank, blank⟩
theorem seed_first : Reach blankStart (state 1 (enc "TA") e) := by
  refine ⟨129, ?_⟩
  rfl

-- The finite checker uses zero padding on both stacks, including the deepest tail.
def blankGuard (L R : Word) (lp rp : Nat) : C :=
  ⟨.B, L ++ [true] ++ List.replicate lp false, [false,false] ++ R ++ List.replicate rp false⟩

theorem blankGuard_embed (L R : Word) (lp rp : Nat) :
    physical (embed (blankGuard L R lp rp) blank blank) = b (pre L e) (pre R blank) := by
  simp only [blankGuard,embed,physical,pre_append,zeros_blank,e,b]

theorem blank_reset (n n' : Nat) (W Y : Word) (lp rp lp' rp' steps cost : Nat)
    (h : exec steps (blankGuard (flat P n ++ W) [true] lp rp) =
      some (cost,blankGuard (flat P n' ++ Y) [true] lp' rp')) :
    Reach (state n W e) (state n' Y e) := by
  have hs := exec_sound steps (blankGuard (flat P n ++ W) [true] lp rp)
    (blankGuard (flat P n' ++ Y) [true] lp' rp') cost blank blank h
  rw [blankGuard_embed,blankGuard_embed,pre_append,pre_append,flat_pre,flat_pre] at hs
  exact ⟨cost,hs⟩

#print axioms seed_first
#print axioms blank_reset
end F197.Agent2Self
