from search import scan
from emit_family import code_name,bl
from pathlib import Path
import sys
P=[7,24,11,24,14,24,9,16,8,11,24,24]
bounds={1:188,2:72,3:616,6:85,20:84,21:134,22:87,23:191}
source='import FastThreeHoleAudit\nimport Raw139E0ZeroLCD0ZeroRCC1ZeroLF\n'+''.join('import A6E0LCD0RCC1'+code_name(k)+'Cover\n' for k in bounds if k!=20)+'''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroLC.D0ZeroRC
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6Coverage.Agent50SideCycle

def parent : PartialMachine := fromCodes [7,24,11,24,14,24,9,16,8,11,24,24]
def child (mv : Move) := refine parent (2,true) (some mv)

theorem cycleCover (B : Nat) (mv : Move) (e k : Nat) (r : Bool) (x : Int)
    (hk : 0 < k) (h : fastSideCycleCheck (child mv) e k r x = true) : Cover (WeightedBound B) (child mv) :=
  Cover.leaf _ (fun m hm => weighted_never B m (fastSideCycleCheck_sound _ _ _ _ _ hk h m hm))

theorem ordinary (B : Nat) (hB : 616 ≤ B) (mv : Move) : Cover (WeightedBound B) (child mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
'''
for code in range(24):
 p=P.copy();p[5]=code
 if code in bounds:
  ns='BB6.Agent6E0ZeroLC.D0ZeroRC.C1'+code_name(code)
  source+=f'''  · have he : child ⟨{bl(code&2)},{bl(code&1)},{code//4}⟩ = {ns}.parent := by
      apply BB6.Agent31ThreeHole.tableOK_sound
      decide
    rw [he]
    exact Cover.leaf _ (fun m hm k d hk hd => Nat.le_trans ({ns}.all_completions_weighted m hm k d hk hd) (by omega))
'''
 else:
  k,e,t,r,b=scan(p);assert k=='cycle'
  source+=f'  · exact cycleCover B _ {e} {t} {bl(r)} ({b}) (by decide) (by decide)\n'
source+='''
theorem cover (B : Nat) (hB : 616 ≤ B) : Cover (WeightedBound B) parent := by
  apply Cover.branch parent (2,true) (by decide)
  intro t _
  cases t with
  | some mv => exact ordinary B hB mv
  | none =>
    apply Cover.leaf
    let c := (knownRun parent 10).getD blank
    have hr : knownRun parent 10 = some c := by rfl
    have hs : readSlot c = (2,true) := by decide
    have hh : parent (readSlot c) = none := by rw [hs]; decide
    have hw : ∀ d ∈ possibleDelays (refine parent (readSlot c) none) 0, d + 10 + 1 ≤ B := by
      intro d hd
      have h6 : d < 6 := by unfold possibleDelays at hd; exact List.mem_range.mp (List.mem_filter.mp hd).1
      omega
    have hc := first_hole_weighted_halt B parent 10 c (by decide) hr hh hw
    simpa only [hs] using hc

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 616 m := by
  intro m hm
  exact (cover 616 (by decide)).sound m hm

#print axioms ordinary
#print axioms cover
#print axioms all_completions_weighted
end BB6.Agent6E0ZeroLC.D0ZeroRC
'''
Path(sys.argv[1]+'/Raw139E0ZeroLCD0ZeroRC.lean').write_text(source)
