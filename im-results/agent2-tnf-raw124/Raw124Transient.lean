import Raw108LongRead
import ZipThreeHoleAudit
namespace BB6.Agent4.Raw124Transient
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole
abbrev old := BB6.Agent10Raw108Long.table
def new (a1 : Option (Option Move)) : PartialMachine :=
  fun s => if s=(4,true) then some (some ⟨true,false,5⟩) else old a1 s
def safe (a1 : Option (Option Move)) : Prop :=
  ∀ mv, a1 = some (some mv) → mv.next = 4 → mv.right = true ∧ mv.write = true
def good (z : Z0) : Prop := z.q = 4 → z.l.headD false = true → z.l.tail.headD false = true
def rel (z w : Z0) : Prop := (z = w ∧ good z) ∨
  (z.q=1 ∧ w.q=5 ∧ z.l=w.l ∧ z.r=w.r ∧ z.l.headD false=true)
inductive ORel : Option Z0 → Option Z0 → Prop
  | none : ORel none none
  | some : rel z w → ORel (some z) (some w)
theorem enter_E (a1 : Option (Option Move)) (hs : safe a1) (q : Fin 6) (b : Bool) (mv : Move)
    (h : old a1 (q,b) = some (some mv)) (hn : mv.next=4) : mv.right=true ∧ mv.write=true := by
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp only [old,BB6.Agent10Raw108Long.table,Option.some.injEq] at h
  all_goals try { contradiction }
  all_goals try { subst mv; contradiction }
  · exact hs mv h hn
  · subst mv; exact ⟨rfl,rfl⟩
theorem next_good (a1 : Option (Option Move)) (hs : safe a1) (z : Z0) (mv : Move)
    (h : old a1 (z.q,z.l.headD false) = some (some mv)) : good (move0 mv z) := by
  intro hq hb
  have hn : mv.next=4 := by unfold move0 at hq; split at hq <;> exact hq
  have hw := enter_E a1 hs z.q (z.l.headD false) mv h hn
  simp [move0,hw.1,hw.2]
theorem step_rel (a1 : Option (Option Move)) (hs : safe a1) {z w : Z0}
    (h : rel z w) : ORel (step0 (old a1) z) (step0 (new a1) w) := by
  rcases h with ⟨rfl,hgood⟩|⟨hz,hw,hl,hr,hb⟩
  · by_cases he : (z.q,z.l.headD false) = (4,true)
    · have hq : z.q=4 := congrArg Prod.fst he
      have hb : z.l.headD false=true := congrArg Prod.snd he
      have ht := hgood hq hb
      have ho : old a1 (z.q,z.l.headD false) = some (some ⟨true,false,1⟩) := by rw [he]; rfl
      have hn : new a1 (z.q,z.l.headD false) = some (some ⟨true,false,5⟩) := by rw [he]; rfl
      unfold step0
      rw [ho,hn]
      apply ORel.some
      right
      exact ⟨rfl,rfl,rfl,rfl,ht⟩
    · have hn : new a1 (z.q,z.l.headD false) = old a1 (z.q,z.l.headD false) := by unfold new; rw [if_neg he]
      unfold step0
      rw [hn]
      cases h : old a1 (z.q,z.l.headD false) with
      | none => exact ORel.none
      | some v =>
        cases v with
        | none => exact ORel.none
        | some mv => exact ORel.some (Or.inl ⟨rfl,next_good a1 hs z mv h⟩)
  · have hwb : w.l.headD false = true := by rw [← hl,hb]
    have he : move0 ⟨false,false,1⟩ z = move0 ⟨false,false,1⟩ w := by simp [move0,hl,hr]
    have hg : good (move0 ⟨false,false,1⟩ z) := by simp [good,move0]
    unfold step0
    simp only [old,BB6.Agent10Raw108Long.table,new,hz,hw,hb,hwb]
    change ORel (some (move0 ⟨false,false,1⟩ z)) (some (move0 ⟨false,false,1⟩ w))
    exact ORel.some (Or.inl ⟨he,hg⟩)
theorem bind_rel {x y : Option Z0} (H : ORel x y) (f g : Z0 → Option Z0)
    (hg : ∀ z w, rel z w → ORel (f z) (g w)) : ORel (x.bind f) (y.bind g) := by
  cases H with
  | none => exact ORel.none
  | some hr => exact hg _ _ hr
theorem run_rel (a1 : Option (Option Move)) (hs : safe a1) (n : Nat) {z w : Z0}
    (h : rel z w) : ORel (run0 (old a1) n z) (run0 (new a1) n w) := by
  induction n generalizing z w with
  | zero => exact ORel.some h
  | succ n ih =>
    simp only [run0]
    exact bind_rel (step_rel a1 hs h) _ _ (fun _ _ h' => ih h')
def slot0 (z : Z0) : Slot := (z.q,z.l.headD false)
theorem read0 (p : PartialMachine) (n : Nat) :
    zipRead p n = (run0 p n ⟨0,[],[]⟩).map slot0 := by
  have J := run_project p n start
  rw [← show (zrun p n start).map project = run0 p n ⟨0,[],[]⟩ from J]
  unfold zipRead
  rw [Option.map_map]
  rfl
theorem read_rel {x y : Option Z0} (H : ORel x y) (s : Slot)
    (hs1 : s.1 ≠ 1) (hs5 : s.1 ≠ 5) (hr : x.map slot0 = some s) : y.map slot0 = some s := by
  cases H with
  | none => contradiction
  | some h =>
    rcases h with ⟨rfl,_⟩|⟨hq,_,_,_,_⟩
    · exact hr
    · have he := Option.some.inj hr
      have hs := congrArg Prod.fst he
      exact False.elim (hs1 (hs.symm.trans hq))
theorem read_transfer (a1 : Option (Option Move)) (hs : safe a1) (n : Nat) (s : Slot)
    (hs1 : s.1 ≠ 1) (hs5 : s.1 ≠ 5) (hr : zipRead (old a1) n = some s) :
    zipRead (new a1) n = some s := by
  rw [read0] at hr ⊢
  have H := run_rel a1 hs n (z := ⟨0,[],[]⟩) (w := ⟨0,[],[]⟩) (Or.inl ⟨rfl,by simp [good]⟩)
  exact read_rel H s hs1 hs5 hr
theorem live_of_never (p : PartialMachine)
    (h : ∀ m, compatible p m → NeverHalts m) (n : Nat) : ∃ z, run0 p n ⟨0,[],[]⟩ = some z := by
  have hn := h (weightedTNFDefaultCompletion p) (weightedTNFDefaultCompletion_compatible p) n
  rw [← weightedTNFKnownRun_eq_defaultRun,knownRun_zip] at hn
  have hp := run_project p n start
  change (zrun p n start).map project = run0 p n ⟨0,[],[]⟩ at hp
  cases hz : zrun p n start with
  | none => simp [hz] at hn
  | some z => exact ⟨project z,by simpa [hz] using hp.symm⟩
theorem rel_live {x y : Option Z0} (H : ORel x y) (hx : ∃ z, x = some z) : ∃ w, y = some w := by
  cases H with
  | none => obtain ⟨z,hz⟩ := hx; contradiction
  | some h => exact ⟨_,rfl⟩
theorem never_of_live (p : PartialMachine)
    (h : ∀ n, ∃ z, run0 p n ⟨0,[],[]⟩ = some z)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := h n
  have hp := (run_project p n start).trans hz
  cases ht : zrun p n start with
  | none => simp [ht] at hp
  | some t =>
    have H := zrun_sound p m hm n start t ht
    rw [start_embed] at H
    rw [H]
    rfl
theorem never_transfer (a1 : Option (Option Move)) (hs : safe a1)
    (h : ∀ m, compatible (old a1) m → NeverHalts m)
    (m : Machine) (hm : compatible (new a1) m) : NeverHalts m := by
  apply never_of_live (new a1) _ m hm
  intro n
  have H := run_rel a1 hs n (z := ⟨0,[],[]⟩) (w := ⟨0,[],[]⟩) (Or.inl ⟨rfl,by simp [good]⟩)
  exact rel_live H (live_of_never (old a1) h n)
#print axioms read_transfer
#print axioms never_transfer
end BB6.Agent4.Raw124Transient
