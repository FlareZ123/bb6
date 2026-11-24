import Q0CrossGateCore
import Q0StripCross

namespace BB429Q0Macro.HalfStep
set_option maxHeartbeats 8000000

theorem DelayTrace.terminal {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) :
    stripOK a (phase s v) W Q F := by
  induction h with
  | nil s w q e ok => simpa [phase] using ok
  | cons s r d ok he ht ih => rw [phase_cons]; exact ih

theorem DelayTrace.append {a s w q e v U R G z W Q F}
    (h : DelayTrace a s w q e v U R G)
    (t : DelayTrace a (phase s v) U R G z W Q F) :
    DelayTrace a s w q e (v++z) W Q F := by
  induction h with
  | nil => simpa [phase] using t
  | cons s r d ok he ht ih =>
    rw [phase_cons] at t
    exact .cons s r d ok he (ih t)

theorem DelayTrace.rank_bounds {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) :
    q+(v.length:Int)≤Q ∧ Q≤q+9*(v.length:Int) := by
  induction h with
  | nil => simp
  | cons s r d ok he ht ih => cases s <;> cases d <;> simp [len] at * <;> omega

theorem strip_gate_bounds {a s w q e} (h : stripOK a s w q e) : CrossGate.strip a (q,e) :=
  ⟨h.2.2.2.1,h.2.2.2.2⟩

theorem strip_gate_parity {a s r w q e} (h : stripOK a s (r::w) q e) :
    CrossGate.parity a (q,e) r := by
  unfold CrossGate.parity
  intro hq
  have hp := h.2.1
  have hs : s=false := by cases s <;> simp [bit] at * <;> omega
  have he := h.2.2.1 hs
  simp only [digits] at he
  have hmul : (a:Int)*(bit r+4*digits w)=(a:Int)*bit r+4*((a:Int)*digits w) := by grind
  rw [hmul] at he
  change ((a:Int)*CrossGate.bit r+e)%2=0
  cases r <;> simp [CrossGate.bit,bit] at * <;> omega

theorem strip_gate_step {a s r d w U q e E}
    (h : stripOK a s (r::w) q e)
    (h' : stripOK a (!s) U (q+len s d) E)
    (he : 4*E=e+(a:Int)*bit r+(bit d:Int)*q+off s d) :
    CrossGate.Step a (q,e) (q+len s d,E) := by
  refine ⟨r,d,strip_gate_bounds h,strip_gate_bounds h',strip_gate_parity h,?_,?_⟩
  · have hp := h.2.1
    cases s <;> cases d <;> simp [bit,len,CrossGate.len] at * <;> omega
  · have hp := h.2.1
    cases s <;> cases r <;> cases d <;> simp [bit,off,CrossGate.bit,CrossGate.off] at * <;> omega

theorem DelayTrace.empty_eq {a s w q e U Q F} (h : DelayTrace a s w q e [] U Q F) :
    U=w ∧ Q=q ∧ F=e := by cases h; exact ⟨rfl,rfl,rfl⟩

theorem DelayTrace.single_gate {a s w q e d U Q F} (h : DelayTrace a s w q e [d] U Q F) :
    CrossGate.Step a (q,e) (Q,F) := by
  cases h with
  | cons s r d ok he ht =>
    obtain ⟨hU,hQ,hF⟩ := ht.empty_eq
    rw [hQ,hF]
    exact strip_gate_step ok ht.initial he

/-- Preserve the exact delayed history at the first nonnegative rank, rather
    than merely retaining any overshoot of the chosen near-power rank. -/
theorem DelayTrace.first_cross {a s w q e v W Q F}
    (h : DelayTrace a s w q e v W Q F) (hq : q<0) (hQ : 0≤Q) :
    ∃ (pre post U V : List Bool) (d : Bool) (r f R G : Int),
      v=pre++d::post ∧ r<0 ∧ 0≤R ∧ R<9 ∧
      DelayTrace a s w q e pre U r f ∧
      DelayTrace a (phase s pre) U r f [d] V R G ∧
      DelayTrace a (phase (phase s pre) [d]) V R G post W Q F := by
  induction h with
  | nil => omega
  | @cons s r d w v W q e E Q F ok he ht ih =>
    by_cases hcross : 0≤q+len s d
    · have hlt : q+len s d<9 := by cases s <;> cases d <;> simp [len] at * <;> omega
      refine ⟨[],v,r::w,w++[d],d,q,e,q+len s d,E,rfl,hq,hcross,hlt,.nil s _ _ _ ok,?_,?_⟩
      · simpa [phase] using DelayTrace.cons s r d ok he (.nil (!s) _ _ _ ht.initial)
      · simpa [phase] using ht
    · obtain ⟨pre,post,U,V,b,R,G,R',G',hv,hr,hR,hR',hpre,hstep,hpost⟩ := ih (by omega) hQ
      refine ⟨d::pre,post,U,V,b,R,G,R',by simp [hv],hr,hR,hR',.cons s r d ok he hpre,?_,?_⟩
      · simpa only [phase_cons] using hstep
      · simpa only [phase_cons] using hpost

/-- A gate-aware strip keeps the seed and the complete delayed path, now
    centered at the first actual threshold crossing. At most eight steps
    have moved from the past to the future. -/
def GateStrip (a k N : Nat) : Prop :=
  ∃ (s : Bool) (w v z U W : List Bool) (q e b E Q F : Int),
    w.length=k ∧ N-k-8≤v.length ∧ v.length≤N-k ∧ N≤z.length ∧ z.length≤N+8 ∧
    seedOK a s w q e ∧
    DelayTrace a (phase s w) w q e v U b E ∧
    DelayTrace a (phase (phase s w) v) U b E z W Q F ∧
    ((a=1 ∧ (b,E) ∈ CrossGate.gate1) ∨ (a=2 ∧ (b,E) ∈ CrossGate.gate2))

theorem gate_of_strip {a b k N : Nat} (ha : a=1 ∨ a=2) (hb : b<9)
    (hN : k+10≤N) (h : StripCross a b k N) : GateStrip a k N := by
  obtain ⟨s,w,v,z,U,W,q,e,E,Q,F,hw,hv,hz,hs,h₁,h₂⟩ := h
  have hr := h₁.rank_bounds
  have hq : q<0 := by omega
  obtain ⟨pre,post,U0,U1,d,r,f,R,G,heq,hr0,hR,hR',hpre,hstep,hpost⟩ := h₁.first_cross hq (by omega)
  have hp : post.length≤8 := by
    have hh := hpost.rank_bounds
    omega
  have hl : pre.length+1+post.length=v.length := by rw [heq]; simp; omega
  have hprelen : 1≤pre.length := by omega
  let m := pre.length-1
  obtain ⟨U00,r0,f0,hpre0,hpre1⟩ := hpre.split m
  have hlen : (pre.drop m).length=1 := by simp [m]; omega
  obtain ⟨d0,hd0⟩ := List.length_eq_one_iff.mp hlen
  rw [hd0] at hpre1
  have g0 := hpre1.single_gate
  have g1 := hstep.single_gate
  have hphase : phase (phase (phase s w) pre) [d] = phase (phase s w) (pre++[d]) :=
    (phase_append _ _ _).symm
  have hphase2 : phase (phase (phase (phase s w) pre) [d]) post = phase (phase s w) v := by
    rw [hphase,←phase_append,heq]
    simp
  rw [←hphase2] at h₂
  have hall := hpost.append h₂
  have hlen2 : 2≤(post++z).length := by simp [hz]; omega
  obtain ⟨V0,r1,f1,hpost0,hpost1⟩ := hall.split 1
  have hlen1 : ((post++z).take 1).length=1 := by simp; omega
  obtain ⟨d1,hd1⟩ := List.length_eq_one_iff.mp hlen1
  rw [hd1] at hpost0
  have g2 := hpost0.single_gate
  obtain ⟨V1,r2,f2,hpost2,hpost3⟩ := hpost1.split 1
  have hlen3 : (((post++z).drop 1).take 1).length=1 := by simp; omega
  obtain ⟨d2,hd2⟩ := List.length_eq_one_iff.mp hlen3
  rw [hd2] at hpost2
  have g3 := hpost2.single_gate
  have hg := CrossGate.central_gate ha g0 g1 g2 g3 hr0 ⟨hR,hR'⟩
  have hfront := hpre.append hstep
  rw [hphase] at hall
  refine ⟨s,w,pre++[d],post++z,U1,W,q,e,R,G,Q,F,hw,?_,?_,?_,?_,hs,hfront,hall,hg⟩ <;>
    simp [hz] <;> omega

#print axioms gate_of_strip
end BB429Q0Macro.HalfStep
