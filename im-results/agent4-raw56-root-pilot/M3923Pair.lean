import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw56RootE11LB.M3923Pair
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

-- short=39234; long=39233
 def table (long : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => if long then some (some ⟨false,true,4⟩) else some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def Valid (z : Z0) : Prop := z.q = 4 → z.r.headD false = true

def cost (z : Z0) : Nat := if z.q = 4 ∧ z.l.headD false = false then 3 else 1

theorem cost_pos (z : Z0) : 0 < cost z := by unfold cost; split <;> decide

theorem preserve (z w : Z0) (h : step0 (table false) z = some w) : Valid w := by
  rcases z with ⟨⟨q,hq⟩,l,r⟩
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases l with
    | nil => simp [step0,table,move0] at h; try subst w; simp [Valid]
    | cons b L => cases b <;> simp [step0,table,move0] at h <;> try subst w <;> simp [Valid]

theorem simulate (z : Z0) (h : Valid z) : run0 (table true) (cost z) z = step0 (table false) z := by
  rcases z with ⟨⟨q,hq⟩,l,r⟩
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl|rfl <;> cases l with
    | nil => first | rfl | (simp [Valid] at h; cases r with
        | nil => simp at h
        | cons b R => cases b <;> simp_all <;> rfl)
    | cons b L => cases b <;> first | rfl | (simp [Valid] at h; cases r with
        | nil => simp at h
        | cons b R => cases b <;> simp_all <;> rfl)

def Live (p : PartialMachine) (z : Z0) : Prop := ∀ n : Nat, ∃ w, run0 p n z = some w

theorem prefixLive {p : PartialMachine} {z : Z0} {n t : Nat} {w : Z0} (h : n ≤ t) (hr : run0 p t z = some w) : ∃ v, run0 p n z = some v := by
  rw [show t = n + (t-n) by omega,run0_add] at hr
  cases e : run0 p n z with
  | none => simp [e] at hr
  | some v => exact ⟨v,rfl⟩

theorem suffixLive {p : PartialMachine} {z w : Z0} {k : Nat} (h : Live p z) (hr : run0 p k z = some w) : Live p w := by
  intro n
  obtain ⟨v,hv⟩ := h (k+n)
  rw [run0_add,hr] at hv
  exact ⟨v,hv⟩

theorem lift_prefix {z : Z0} (hz : Valid z) (h : Live (table false) z) (n : Nat) :
    ∃ t w, n ≤ t ∧ run0 (table true) t z = some w := by
  induction n generalizing z with
  | zero => exact ⟨0,z,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := h 1
    have hw' : step0 (table false) z = some w := by
      rw [run0.eq_2] at hw
      cases e : step0 (table false) z <;> simp [e,run0.eq_1] at hw ⊢
      exact hw
    obtain ⟨t,v,ht,hv⟩ := ih (preserve z w hw') (suffixLive h hw)
    exact ⟨cost z+t,v,by have := cost_pos z; omega,join0 ((simulate z hz).trans hw') hv⟩

theorem reduce_prefix {z : Z0} (hz : Valid z) (h : Live (table true) z) (n : Nat) : ∃ w, run0 (table false) n z = some w := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := h (cost z)
    have hw' := (simulate z hz).symm.trans hw
    obtain ⟨v,hv⟩ := ih (preserve z w hw') (suffixLive h hw)
    exact ⟨v,by rw [run0.eq_2,hw']; exact hv⟩

theorem live_iff {z : Z0} (hz : Valid z) : Live (table false) z ↔ Live (table true) z := by
  constructor
  · intro h n
    obtain ⟨t,w,ht,hr⟩ := lift_prefix hz h n
    exact prefixLive ht hr
  · intro h n
    exact reduce_prefix hz h n

def haltFill (p : PartialMachine) : Machine := fun s => (p s).bind id

theorem fillCompatible (p : PartialMachine) : compatible p (haltFill p) := by
  intro s t h
  simp [haltFill,h]

theorem fill_stuck {p : PartialMachine} {z : Z} (h : step p z = none) : rawStep (haltFill p) (embed z) = none := by
  unfold step at h
  unfold rawStep haltFill
  rw [read_embed]
  change Option.map (fun mv => move mv z) ((p (z.q,z.l.headD false)).bind id) = none at h
  cases e : p (z.q,z.l.headD false) with
  | none => rfl
  | some t => cases t <;> simp_all

theorem fill_complete (p : PartialMachine) (n : Nat) (z : Z) (h : (run (haltFill p) n (embed z)).isSome = true) : ∃ w, zrun p n z = some w := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl⟩
  | succ n ih =>
    rw [show n+1 = 1+n by omega,run_append,run.eq_2,run.eq_1] at h
    change ((rawStep (haltFill p) (embed z)).bind (run (haltFill p) n)).isSome = true at h
    cases e : step p z with
    | none => rw [fill_stuck e] at h; simp at h
    | some w =>
      rw [step_sound p (haltFill p) (fillCompatible p) z w e] at h
      simp at h
      obtain ⟨v,hv⟩ := ih w h
      exact ⟨v,by rw [zrun.eq_2,e]; exact hv⟩

theorem cover_iff_live (p : PartialMachine) : Cover NeverHalts p ↔ Live p (project start) := by
  constructor
  · intro h n
    have hn := h.sound (haltFill p) (fillCompatible p) n
    rw [←start_embed] at hn
    obtain ⟨w,hw⟩ := fill_complete p n start hn
    exact ⟨project w,by rw [←run_project,hw]; rfl⟩
  · intro h
    apply Cover.leaf
    intro m hm n
    obtain ⟨w,hw⟩ := h n
    rw [←run_project] at hw
    cases e : zrun p n start with
    | none => simp [e] at hw
    | some v => rw [←start_embed,zrun_sound p m hm n start v e]; rfl

theorem paired_cover : Cover NeverHalts (table false) ↔ Cover NeverHalts (table true) := by
  rw [cover_iff_live,cover_iff_live]
  exact live_iff (by simp [Valid,project,start])

#print axioms paired_cover
#print axioms simulate
end BB6.Agent4Raw56RootE11LB.M3923Pair
