import Raw13BinarySiblings

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Detour
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent46Raw13BinarySiblings (never_of_return)

def base : PartialMachine := FAR.fromCodes [7,14,11,5,2,19,22,0,13,13,10,24]
def detour : PartialMachine := FAR.fromCodes [7,14,11,5,2,19,22,0,10,13,10,24]
def blank0 : Z0 := ⟨0,[],[]⟩
def good (z : Z0) : Prop := z.q = 4 → z.l.getD 1 false = true

theorem good_start : good blank0 := by simp [good,blank0]

theorem step_good (z w : Z0) (h : step0 base z = some w) : good w := by
  obtain ⟨q,l,r⟩ := z
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q
  · cases l with
    | nil =>
      change some ⟨1,r.headD false::true::[],r.tail⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨1,r.headD false::true::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change some ⟨3,l,true::r⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
  · cases l with
    | nil =>
      change some ⟨2,r.headD false::true::[],r.tail⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨2,r.headD false::true::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change some ⟨1,r.headD false::false::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
  · cases l with
    | nil =>
      change some ⟨0,[],true::r⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨0,l,true::r⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change some ⟨4,r.headD false::true::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
  · cases l with
    | nil =>
      change some ⟨5,[],true::r⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨5,l,true::r⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change some ⟨0,l,false::r⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
  · cases l with
    | nil =>
      change some ⟨3,r.headD false::false::[],r.tail⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨3,r.headD false::false::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change some ⟨3,r.headD false::false::l,r.tail⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
  · cases l with
    | nil =>
      change some ⟨2,[],true::r⟩ = some w at h
      have hw := Option.some.inj h
      subst w
      simp [good]
    | cons a l =>
      cases a with
      | false =>
        change some ⟨2,l,true::r⟩ = some w at h
        have hw := Option.some.inj h
        subst w
        simp [good]
      | true =>
        change none = some w at h
        contradiction

theorem step_sim (z w : Z0) (g : good z) (h : step0 base z = some w) :
    ∃ k, 0 < k ∧ run0 detour k z = some w := by
  obtain ⟨q,l,r⟩ := z
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q
  all_goals try (cases l with
    | nil => exact ⟨1,by decide,h⟩
    | cons a l => cases a <;> exact ⟨1,by decide,h⟩)
  · have hg := g rfl
    cases l with
    | nil => contradiction
    | cons a l =>
      cases a with
      | true => exact ⟨1,by decide,h⟩
      | false =>
        cases l with
        | nil => contradiction
        | cons b l =>
          cases b with
          | false => contradiction
          | true => exact ⟨3,by decide,h⟩

theorem run_sim (n : Nat) (z w : Z0) (g : good z) (h : run0 base n z = some w) :
    ∃ k, n ≤ k ∧ run0 detour k z = some w ∧ good w := by
  induction n generalizing z with
  | zero => simp [run0] at h; subst w; exact ⟨0,by omega,rfl,g⟩
  | succ n ih =>
    cases hs : step0 base z with
    | none => simp [run0,hs] at h
    | some t =>
      have ht : run0 base n t = some w := by simpa [run0,hs] using h
      obtain ⟨k,hk,h1⟩ := step_sim z t g hs
      obtain ⟨j,hj,h2,hg⟩ := ih t (step_good z t hs) ht
      exact ⟨k+j,by omega,join0 h1 h2,hg⟩

def live (p : PartialMachine) : Prop := ∀ n, ∃ z, run0 p n blank0 = some z

theorem live_detour (h : live base) : live detour := by
  intro n
  obtain ⟨z,hz⟩ := h n
  obtain ⟨k,hk,hr,_⟩ := run_sim n blank0 z good_start hz
  rw [show k=n+(k-n) by omega,run0_add] at hr
  cases he : run0 detour n blank0 with
  | none => simp [he] at hr
  | some w => exact ⟨w,rfl⟩

theorem step_defined (z : Z0) (h : (step0 detour z).isSome) :
    (step0 base z).isSome := by
  obtain ⟨q,l,r⟩ := z
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;>
    cases l with
    | nil => rfl
    | cons b l => cases b <;> first | rfl | exact h

theorem live_base (h : live detour) : live base := by
  have hs : ∀ n, ∃ z k, run0 base n blank0 = some z ∧ run0 detour k blank0 = some z ∧ good z := by
    intro n
    induction n with
    | zero => exact ⟨blank0,0,rfl,rfl,good_start⟩
    | succ n ih =>
      obtain ⟨z,k,hb,hd,hg⟩ := ih
      obtain ⟨w,hw⟩ := h (k+1)
      rw [run0_add,hd] at hw
      have hstep : (step0 detour z).isSome := by
        cases ht : step0 detour z with
        | none => simp [run0,ht] at hw
        | some t => rfl
      have ht := step_defined z hstep
      cases hb' : step0 base z with
      | none => simp [hb'] at ht
      | some t =>
        obtain ⟨j,_,hj⟩ := step_sim z t hg hb'
        exact ⟨t,k+j,join0 hb (by simp [run0,hb']),join0 hd hj,step_good z t hb'⟩
  intro n
  obtain ⟨z,_,hb,_,_⟩ := hs n
  exact ⟨z,hb⟩

theorem live_iff : live base ↔ live detour := ⟨live_detour,live_base⟩

open BB6Coverage.Agent50Zipper in
theorem live_never (p : PartialMachine) (h : live p) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨w,hw⟩ := h n
  have hh : (zrun p n start).map project = some w := (run_project p n start).trans hw
  cases he : zrun p n start with
  | none => simp [he] at hh
  | some z =>
    have H := zrun_sound p m hm n start z he
    rw [start_embed] at H
    rw [H]
    rfl

theorem both_never (h : live base) : (∀ m, compatible base m → NeverHalts m) ∧
    (∀ m, compatible detour m → NeverHalts m) :=
  ⟨live_never base h, live_never detour (live_detour h)⟩

#print axioms live_iff
#print axioms both_never
end BB6.Agent46Raw13Detour
