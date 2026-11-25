import Raw107RootCut
import Raw107RDData
import Raw107RCData
import Raw107REData
import Raw107B1REData
import Raw107B1LCData
import Raw107B1LEData
import Raw107B1LBData
import Raw107B0RFData
import Raw107B1RFData
import Raw107B0LEData
import Raw107LF180Bridge
import Raw107LABridge
import Raw107LFBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw107ParentClosure

open BB6Coverage BB6.Agent13BlankDelay

/-- A child certificate at a smaller weighted threshold is valid at 815. -/
theorem lift_bound {A : Nat} (hA : A ≤ 815) {m : Machine}
    (h : WeightedBound A m) : WeightedBound 815 m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hA

/-- All thirteen live B1 children close, so the entire raw107 six-hole
    parent has weighted score at most 815. -/
theorem all_completions :
    ∀ m, compatible BB6.Agent10Raw107Root.parent m → WeightedBound 815 m :=
  BB6.Agent10Raw107Root.all_completions (by
    intro mv hmv m hm
    simp [BB6.Agent10Raw107Root.remaining] at hmv
    rcases hmv with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
    · subst mv
      exact lift_bound (by decide : 90 ≤ 815)
        (BB6.Agent11Raw107B0LE.all_completions m hm)
    · subst mv
      exact BB6.Agent10Raw107LF180Bridge.all_completions m hm
    · subst mv
      exact lift_bound (by decide : 200 ≤ 815)
        (BB6.Agent11Raw107RC.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 129 ≤ 815)
        (BB6.Agent11Raw107RD.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 201 ≤ 815)
        (BB6.Agent11Raw107RE.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 536 ≤ 815)
        (BB6.Agent11Raw107B0RF.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 282 ≤ 815)
        (BB6.Agent1Raw107LABridge.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 212 ≤ 815)
        (BB6.Agent11Raw107B1LB.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 194 ≤ 815)
        (BB6.Agent11Raw107B1LC.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 231 ≤ 815)
        (BB6.Agent11Raw107B1LE.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 753 ≤ 815)
        (BB6.Agent10Raw107LFBridge.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 158 ≤ 815)
        (BB6.Agent11Raw107B1RE.all_completions m hm)
    · subst mv
      exact lift_bound (by decide : 160 ≤ 815)
        (BB6.Agent11Raw107B1RF.all_completions m hm)
  )

#print axioms lift_bound
#print axioms all_completions

end BB6.Agent11Raw107ParentClosure
