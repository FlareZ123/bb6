import H5ForcedSpine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34H5Exact
open BB6.Agent42ModularCone
open BB6.Agent34H5Precision
open BB6.Agent34H5Spine
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- An exact, non-approximated source inverse path. Each prescribed
    predecessor satisfies its full original-source arithmetic equation. -/
def ExactPath : List (Option Nat) → Nat → Nat → Nat → Nat → Prop
  | [], x, y, a, t => a=x ∧ t=y
  | choice::rest, x, y, a, t =>
      ∃ p q, StepEq choice p q x y ∧ ExactPath rest p q a t

/-- Every one-open-leaf spine certificate carries all the actual
    predecessor equations, in addition to source reachability. -/
theorem source_spine_exact (choices : List (Option Nat)) (b : Nat) (s : Pair)
    (hc : spineCert choices b s=true)
    (x y : Nat) (hr : BB6.Agent3.CReach x y)
    (hl : Large b y) (hm : Matches b x y s) :
    ∃ a t, BB6.Agent3.CReach a t ∧
      Large (spineBits choices b) t ∧
      Matches (spineBits choices b) a t (spineResidue choices b s) ∧
      ExactPath choices x y a t := by
  induction choices generalizing b s x y with
  | nil =>
      exact ⟨x,y,hr,hl,hm,⟨rfl,rfl⟩⟩
  | cons choice rest ih =>
      have hs : forcedAt b s choice=true ∧
          spineCert rest (branchBits b choice) (branchResidue b s choice)=true := by
        simpa only [spineCert, Bool.and_eq_true] using hc
      obtain ⟨p,q,hrp,hlp,hmp,hstep⟩ :=
        source_forced_one b s choice hs.1 x y hr hl hm
      obtain ⟨a,t,hra,hla,hma,hpath⟩ :=
        ih (branchBits b choice) (branchResidue b s choice)
          hs.2 p q hrp hlp hmp
      refine ⟨a,t,hra,?_,?_,?_⟩
      · simpa only [spineBits] using hla
      · simpa only [spineResidue] using hma
      · change ∃ p' q', StepEq choice p' q' x y ∧
          ExactPath rest p' q' a t
        exact ⟨p,q,hstep,hpath⟩

/-- Exact affine unfolding of the ten selected inverse edges. The
    source arithmetic forces the endpoint, not merely its residue. -/
theorem h5_affine_path (r B a t : Nat)
    (h : ExactPath h5Spine (2*J r+1) (49726+8388608*B) a t) :
    a=1735479+3388496*r+6776976*B ∧
    t=1280448+2500056*r+5000120*B := by
  have hx : 2*J r+1=4196993+8388608*r := by unfold J; omega
  rw [hx] at h
  dsimp [h5Spine,ExactPath,StepEq,P] at h
  rcases h with ⟨x1,y1,h1,x2,y2,h2,x3,y3,h3,x4,y4,h4,x5,y5,h5,x6,y6,h6,x7,y7,h7,x8,y8,h8,x9,y9,h9,x10,y10,h10,hend⟩
  have he1 :
      x1=1061677+2097152*r+2097152*B ∧
      y1=1617379+3145728*r+7340032*B := by
    omega
  have he2 :
      x2=334880+655360*r+1179648*B ∧
      y2=1980771+3866624*r+7798784*B := by
    rcases he1 with ⟨he1x,he1y⟩
    omega
  have he3 :
      x3=1157823+2260992*r+4489216*B ∧
      y3=1569296+3063808*r+6144000*B := by
    rcases he2 with ⟨he2x,he2y⟩
    omega
  have he4 :
      x4=2727117+5324800*r+10633216*B ∧
      y4=784647+1531904*r+3072000*B := by
    rcases he3 with ⟨he3x,he3y⟩
    omega
  have he5 :
      x5=1755880+3428352*r+6852608*B ∧
      y5=1270262+2480128*r+4962304*B := by
    rcases he4 with ⟨he4x,he4y⟩
    omega
  have he6 :
      x6=3026140+5908480*r+11814912*B ∧
      y6=635130+1240064*r+2481152*B := by
    rcases he5 with ⟨he5x,he5y⟩
    omega
  have he7 :
      x7=3661268+7148544*r+14296064*B ∧
      y7=317564+620032*r+1240576*B := by
    rcases he6 with ⟨he6x,he6y⟩
    omega
  have he8 :
      x8=994706+1942144*r+3884160*B ∧
      y8=1650840+3223232*r+6446528*B := by
    rcases he7 with ⟨he7x,he7y⟩
    omega
  have he9 :
      x9=2645544+5165376*r+10330688*B ∧
      y9=825419+1611616*r+3223264*B := by
    rcases he8 with ⟨he8x,he8y⟩
    omega
  have he10 :
      x10=1735479+3388496*r+6776976*B ∧
      y10=1280448+2500056*r+5000120*B := by
    rcases he9 with ⟨he9x,he9y⟩
    omega
  rcases he10 with ⟨ha,ht⟩
  rcases hend with ⟨hxeq,hyeq⟩
  omega

/-- Original-source theorem: every genuine blank-reachable high stop in
    this full odd H5 family must encounter precisely the affine E-state
    identified in Agent21's non-power parent fan. This is a structural
    forcing theorem, not an assertion that any stop is reachable. -/
theorem h5_stop_forces_E (r w B : Nat)
    (he : (49726+8388608*B)+J r+3*M r w+4 =
      2^(2*M r w+2)*(J r+2))
    (hr : BB6.Agent3.CReach (2*J r+1) (49726+8388608*B)) :
    BB6.Agent3.CReach
      (1735479+3388496*r+6776976*B)
      (1280448+2500056*r+5000120*B) := by
  have hl : Large 23 (49726+8388608*B) :=
    large_weaken (by unfold M; omega : 23≤2*M r w+1)
      (stop_size (J r) (M r w) (49726+8388608*B) he)
  have hm := h5_root_matches23 r w (49726+8388608*B) he
  obtain ⟨a,t,hra,_,_,hpath⟩ :=
    source_spine_exact h5Spine 23
      (stopResidue (J 0) (M 0 0)) h5SpineCert
      (2*J r+1) (49726+8388608*B) hr hl hm
  obtain ⟨ha,ht⟩ := h5_affine_path r B a t hpath
  simpa only [ha,ht] using hra

#print axioms source_spine_exact
#print axioms h5_affine_path
#print axioms h5_stop_forces_E
end BB6.Agent34H5Exact
