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
      · simpa only [spineBits,spineResidue] using hma
      · change ∃ p' q', StepEq choice p' q' x y ∧
          ExactPath rest p' q' a t
        exact ⟨p,q,hstep,hpath⟩

private theorem affineStep1 (r B p q : Nat)
    (h : StepEq (some 1) p q (4196993+8388608*r+0*B) (49726+0*r+8388608*B)) :
    p=(1061677+2097152*r+2097152*B) ∧ q=(1617379+3145728*r+7340032*B) := by
  change (4196993+8388608*r+0*B)+(49726+0*r+8388608*B)+((4196993+8388608*r+0*B)+(49726+0*r+8388608*B))%2 =
      4*(p+2+((4196993+8388608*r+0*B)+(49726+0*r+8388608*B))%2) ∧
      2*q+p+10=(4196993+8388608*r+0*B)+2*(49726+0*r+8388608*B) at h
  omega

private theorem affineStep2 (r B p q : Nat)
    (h : StepEq (some 2) p q (1061677+2097152*r+2097152*B) (1617379+3145728*r+7340032*B)) :
    p=(334880+655360*r+1179648*B) ∧ q=(1980771+3866624*r+7798784*B) := by
  change (1061677+2097152*r+2097152*B)+(1617379+3145728*r+7340032*B)+((1061677+2097152*r+2097152*B)+(1617379+3145728*r+7340032*B))%2 =
      8*(p+2+((1061677+2097152*r+2097152*B)+(1617379+3145728*r+7340032*B))%2) ∧
      2*q+p+13=(1061677+2097152*r+2097152*B)+2*(1617379+3145728*r+7340032*B) at h
  omega

private theorem affineStep3 (r B p q : Nat)
    (h : StepEq (some 0) p q (334880+655360*r+1179648*B) (1980771+3866624*r+7798784*B)) :
    p=(1157823+2260992*r+4489216*B) ∧ q=(1569296+3063808*r+6144000*B) := by
  change (334880+655360*r+1179648*B)+(1980771+3866624*r+7798784*B)+((334880+655360*r+1179648*B)+(1980771+3866624*r+7798784*B))%2 =
      2*(p+2+((334880+655360*r+1179648*B)+(1980771+3866624*r+7798784*B))%2) ∧
      2*q+p+7=(334880+655360*r+1179648*B)+2*(1980771+3866624*r+7798784*B) at h
  omega

private theorem affineStep4 (r B p q : Nat)
    (h : StepEq none p q (1157823+2260992*r+4489216*B) (1569296+3063808*r+6144000*B)) :
    p=(2727117+5324800*r+10633216*B) ∧ q=(784647+1531904*r+3072000*B) := by
  change p+2=(1157823+2260992*r+4489216*B)+(1569296+3063808*r+6144000*B) ∧ 2*q+2=(1569296+3063808*r+6144000*B) at h
  omega

private theorem affineStep5 (r B p q : Nat)
    (h : StepEq (some 0) p q (2727117+5324800*r+10633216*B) (784647+1531904*r+3072000*B)) :
    p=(1755880+3428352*r+6852608*B) ∧ q=(1270262+2480128*r+4962304*B) := by
  change (2727117+5324800*r+10633216*B)+(784647+1531904*r+3072000*B)+((2727117+5324800*r+10633216*B)+(784647+1531904*r+3072000*B))%2 =
      2*(p+2+((2727117+5324800*r+10633216*B)+(784647+1531904*r+3072000*B))%2) ∧
      2*q+p+7=(2727117+5324800*r+10633216*B)+2*(784647+1531904*r+3072000*B) at h
  omega

private theorem affineStep6 (r B p q : Nat)
    (h : StepEq none p q (1755880+3428352*r+6852608*B) (1270262+2480128*r+4962304*B)) :
    p=(3026140+5908480*r+11814912*B) ∧ q=(635130+1240064*r+2481152*B) := by
  change p+2=(1755880+3428352*r+6852608*B)+(1270262+2480128*r+4962304*B) ∧ 2*q+2=(1270262+2480128*r+4962304*B) at h
  omega

private theorem affineStep7 (r B p q : Nat)
    (h : StepEq none p q (3026140+5908480*r+11814912*B) (635130+1240064*r+2481152*B)) :
    p=(3661268+7148544*r+14296064*B) ∧ q=(317564+620032*r+1240576*B) := by
  change p+2=(3026140+5908480*r+11814912*B)+(635130+1240064*r+2481152*B) ∧ 2*q+2=(635130+1240064*r+2481152*B) at h
  omega

private theorem affineStep8 (r B p q : Nat)
    (h : StepEq (some 1) p q (3661268+7148544*r+14296064*B) (317564+620032*r+1240576*B)) :
    p=(994706+1942144*r+3884160*B) ∧ q=(1650840+3223232*r+6446528*B) := by
  change (3661268+7148544*r+14296064*B)+(317564+620032*r+1240576*B)+((3661268+7148544*r+14296064*B)+(317564+620032*r+1240576*B))%2 =
      4*(p+2+((3661268+7148544*r+14296064*B)+(317564+620032*r+1240576*B))%2) ∧
      2*q+p+10=(3661268+7148544*r+14296064*B)+2*(317564+620032*r+1240576*B) at h
  omega

private theorem affineStep9 (r B p q : Nat)
    (h : StepEq none p q (994706+1942144*r+3884160*B) (1650840+3223232*r+6446528*B)) :
    p=(2645544+5165376*r+10330688*B) ∧ q=(825419+1611616*r+3223264*B) := by
  change p+2=(994706+1942144*r+3884160*B)+(1650840+3223232*r+6446528*B) ∧ 2*q+2=(1650840+3223232*r+6446528*B) at h
  omega

private theorem affineStep10 (r B p q : Nat)
    (h : StepEq (some 0) p q (2645544+5165376*r+10330688*B) (825419+1611616*r+3223264*B)) :
    p=(1735479+3388496*r+6776976*B) ∧ q=(1280448+2500056*r+5000120*B) := by
  change (2645544+5165376*r+10330688*B)+(825419+1611616*r+3223264*B)+((2645544+5165376*r+10330688*B)+(825419+1611616*r+3223264*B))%2 =
      2*(p+2+((2645544+5165376*r+10330688*B)+(825419+1611616*r+3223264*B))%2) ∧
      2*q+p+7=(2645544+5165376*r+10330688*B)+2*(825419+1611616*r+3223264*B) at h
  omega

/-- Exact affine unfolding of ten selected original-source inverse edges,
    proved by isolated linear arithmetic certificates rather than relying
    on any giant monolithic decision procedure. -/
theorem h5_affine_path (r B a t : Nat)
    (h : ExactPath h5Spine (2*J r+1) (49726+8388608*B) a t) :
    a=(1735479+3388496*r+6776976*B) ∧
    t=(1280448+2500056*r+5000120*B) := by
  have hx : 2*J r+1=(4196993+8388608*r+0*B) := by unfold J; omega
  rw [hx] at h
  rcases h with ⟨x1,y1,h1,rest1⟩
  obtain ⟨he1x,he1y⟩ := affineStep1 r B x1 y1 h1
  subst x1
  subst y1
  rcases rest1 with ⟨x2,y2,h2,rest2⟩
  obtain ⟨he2x,he2y⟩ := affineStep2 r B x2 y2 h2
  subst x2
  subst y2
  rcases rest2 with ⟨x3,y3,h3,rest3⟩
  obtain ⟨he3x,he3y⟩ := affineStep3 r B x3 y3 h3
  subst x3
  subst y3
  rcases rest3 with ⟨x4,y4,h4,rest4⟩
  obtain ⟨he4x,he4y⟩ := affineStep4 r B x4 y4 h4
  subst x4
  subst y4
  rcases rest4 with ⟨x5,y5,h5,rest5⟩
  obtain ⟨he5x,he5y⟩ := affineStep5 r B x5 y5 h5
  subst x5
  subst y5
  rcases rest5 with ⟨x6,y6,h6,rest6⟩
  obtain ⟨he6x,he6y⟩ := affineStep6 r B x6 y6 h6
  subst x6
  subst y6
  rcases rest6 with ⟨x7,y7,h7,rest7⟩
  obtain ⟨he7x,he7y⟩ := affineStep7 r B x7 y7 h7
  subst x7
  subst y7
  rcases rest7 with ⟨x8,y8,h8,rest8⟩
  obtain ⟨he8x,he8y⟩ := affineStep8 r B x8 y8 h8
  subst x8
  subst y8
  rcases rest8 with ⟨x9,y9,h9,rest9⟩
  obtain ⟨he9x,he9y⟩ := affineStep9 r B x9 y9 h9
  subst x9
  subst y9
  rcases rest9 with ⟨x10,y10,h10,rest10⟩
  obtain ⟨he10x,he10y⟩ := affineStep10 r B x10 y10 h10
  subst x10
  subst y10
  exact rest10

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
