import Lean.Elab.Tactic.Omega
import Y3SafeNormalizer
import PacketShift

/-!
  A source-sound Hensel cylinder lifting principle for the exceptional
  D E/p=2 packet reset.  The rank-normalized B/E source path of any
  accepted seed (r,Q) lifts to EVERY k = r + 3^(2Q+7)*t, with unchanged
  terminal B/E/A phase and q,p.  The exponent is one larger than the
  initial packet resource q+p=2Q+6, guaranteeing the terminal a-index
  residue mod3 is stable.

  Uses Agent31PacketShift's original-source costed path equivariance.
  No future state of the true blank-root trajectory is assumed.
-/

namespace BB6.Agent36Y3Lift

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent31PacketPaths BB6.Agent31PacketShift
open BB6.BoundaryPadding

set_option maxHeartbeats 18000000
set_option maxRecDepth 8192

/-- Every accepted seed (r,Q) generates an entire infinite 3-adic
    cylinder of source-machine E/p2 inputs, not merely a finite sample.
    Exact original-machine transitions, physical blank-extension Eq. -/
theorem lift_safe_seed (r Q t : Nat)
    (hs : BB6.Agent36Y3Safe.safeY3 ⟨8*r+5,0,2*Q+6⟩) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet (3*(r+3^(2*Q+7)*t)+4) Q 2
            (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let c : Packet := ⟨8*r+5,0,2*Q+6⟩
  let d : Packet := (normalizeWithCount c).2
  let n : Nat := (normalizeWithCount c).1
  let N : Nat := 2*Q+7
  let x : Nat := 8*3^(N-n)*t
  let y : Nat := 8^n*x
  have hc : c.a ≥ 4 := by change 8*r+5≥4; omega
  obtain ⟨cost,hpath⟩ := normalized_path c hc
  have hbound : n ≤ 2*Q+6 := by
    have h := path_count_bound hpath
    change n ≤ c.q+c.p at h
    dsimp [c] at h
    omega
  have hpowadd : n+(N-n)=N := by dsimp [N]; omega
  have hx : 3^n*x = 8*3^N*t := by
    calc
      3^n*x = 3^n*(8*3^(N-n)*t) := rfl
      _ = 8*(3^(n+(N-n)))*t := by
        rw [Nat.pow_add]
        ac_rfl
      _ = 8*3^N*t := by rw [hpowadd]
  have hNnext : N-n=(2*Q+6-n)+1 := by dsimp [N]; omega
  have hy : y=3*(8^(n+1)*3^(2*Q+6-n)*t) := by
    dsimp [y,x]
    rw [hNnext,Nat.pow_succ,Nat.pow_succ]
    ac_rfl
  have hmod : (d.a+y)%3=d.a%3 := by
    rw [hy]
    omega
  have hsafeBase : BB6.Agent36Y3Safe.terminalY3 d := hs
  have hsafeShift :
      BB6.Agent36Y3Safe.terminalY3 (⟨d.a+y,d.q,d.p⟩ : Packet) := by
    unfold BB6.Agent36Y3Safe.terminalY3 at hsafeBase ⊢
    simpa only [hmod] using hsafeBase
  have hamin : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c hc
  obtain ⟨tail,a,q,b,htail⟩ :=
    BB6.Agent36Y3Safe.terminalY3_source
      (⟨d.a+y,d.q,d.p⟩ : Packet) (by omega) hsafeShift
  obtain ⟨linear,hshift⟩ :=
    BB6.Agent31PacketShift.source_path_shift hpath
      BB6.Agent2PacketP2Reset.marker
  obtain ⟨costShift,hpathShift,_⟩ := hshift x
  have hpathRaw :
      run costShift
        (packet (c.a+3^n*x) c.q c.p
          BB6.Agent2PacketP2Reset.marker) =
      packet (d.a+y) d.q d.p
        BB6.Agent2PacketP2Reset.marker := by
    change run costShift
      (packet (c.a+3^n*x) c.q c.p
        BB6.Agent2PacketP2Reset.marker) =
      packet (d.a+y) d.q d.p
        BB6.Agent2PacketP2Reset.marker at hpathShift
    exact hpathShift
  have hinput :
      8*(r+3^N*t)+5 = c.a+3^n*x := by
    dsimp [c]
    rw [hx]
    omega
  refine ⟨BB6.Agent2PacketP2Reset.eTwoTime
    (r+3^N*t) Q+(costShift+tail),a,q,b,?_⟩
  rw [run_add,BB6.Agent2PacketP2Reset.e_two_reset]
  change ObsEq
    (run (costShift+tail)
      (packet (8*(r+3^N*t)+5) 0 (2*Q+6)
        BB6.Agent2PacketP2Reset.marker))
    (BB6.Agent2BoundaryBZero.regularSection a q b)
  rw [run_add,hinput,hpathRaw]
  exact htail

#print axioms lift_safe_seed
end BB6.Agent36Y3Lift
