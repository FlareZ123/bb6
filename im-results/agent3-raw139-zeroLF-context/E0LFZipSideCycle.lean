import FastFAR
import SparseZipper
import SideCycle

namespace BB6Coverage.Agent3ZipSideCycle
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50SideCycle

/-- Single-pass primitive zipper replay restricted to the left half-line. -/
def zwindow (p : PartialMachine) (b : Int) : Nat → Z → Option Z
  | 0,z => some z
  | n+1,z => if z.h ≤ b then (step p z).bind (zwindow p b n) else none

theorem zwindow_add (p : PartialMachine) (b : Int) (n k : Nat) (z : Z) :
    zwindow p b (n+k) z = (zwindow p b n z).bind (zwindow p b k) := by
  induction n generalizing z with
  | zero => simp [zwindow]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [zwindow]
    split
    · cases step p z with
      | none => rfl
      | some t => exact ih t
    · rfl

theorem window_join {p : PartialMachine} {b : Int} {n k : Nat} {a c d : Z}
    (h : zwindow p b n a = some c) (g : zwindow p b k c = some d) :
    zwindow p b (n+k) a = some d := by
  rw [zwindow_add,h]; exact g

theorem zwindow_sound (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (b : Int) (n : Nat) (z z' : Z) (hs : zwindow p b n z = some z') :
    run m n (embed z) = some (embed z') ∧
    ∀ j < n, ∀ e, run m j (embed z) = some e → side false b e.head := by
  induction n generalizing z with
  | zero =>
    have he : z = z' := Option.some.inj hs
    subst z'; exact ⟨rfl,fun j hj => by omega⟩
  | succ n ih =>
    by_cases hb : z.h ≤ b
    · cases hz : step p z with
      | none => simp [zwindow,hb,hz] at hs
      | some t =>
        have ht : zwindow p b n t = some z' := by simpa [zwindow,hb,hz] using hs
        obtain ⟨hr,hw⟩ := ih t ht
        have hfirst : run m 1 (embed z) = some (embed t) := by
          simpa [run] using step_sound p m hm z t hz
        constructor
        · rw [show n+1=1+n by omega,run_append,hfirst]; exact hr
        · intro j hj e he
          cases j with
          | zero =>
            have heq : embed z = e := Option.some.inj he
            subst e; exact hb
          | succ j =>
            rw [show j+1=1+j by omega,run_append,hfirst] at he
            exact hw j (by omega) e he
    · simp [zwindow,hb] at hs

theorem leftRel (a c : Z) (b : Int) (k : Nat)
    (hq : a.q = c.q) (hl : a.l = c.l) (hr : a.r.take k = c.r.take k)
    (hk : b ≤ a.h+(k:Int)) :
    TailRel false b (c.h-a.h) (embed a) (embed c) := by
  refine ⟨hq,by simp [embed]; omega,?_⟩
  intro x hx
  change x ≤ b at hx
  change atCell c (x+(c.h-a.h)) = atCell a x
  unfold atCell
  by_cases h : x ≤ a.h
  · have hc : x+(c.h-a.h) ≤ c.h := by omega
    rw [if_pos hc,if_pos h,← hl,show c.h-(x+(c.h-a.h))=a.h-x by omega]
  · have hc : ¬ x+(c.h-a.h) ≤ c.h := by omega
    rw [if_neg hc,if_neg h,show x+(c.h-a.h)-c.h-1=x-a.h-1 by omega]
    have hn : (x-a.h-1).toNat < k := by omega
    have H : ∀ (l : List Bool) (i k : Nat), i < k → (l.take k).getD i false = l.getD i false := by
      intro l i k hi
      induction l generalizing i k with
      | nil => simp
      | cons a l ih =>
        cases k with
        | zero => omega
        | succ k =>
          cases i with
          | zero => rfl
          | succ i => exact ih i k (by omega)
    rw [← H c.r _ k hn,← H a.r _ k hn,hr]

theorem zipCycle_never (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (entry period : Nat) (b : Int) (k : Nat) (a c : Z)
    (hn : 0 < period)
    (ha : zrun p entry ⟨0,0,[],[]⟩ = some a)
    (hc : zwindow p b period a = some c)
    (hd : c.h ≤ a.h) (hq : a.q = c.q) (hl : a.l = c.l)
    (hr : a.r.take k = c.r.take k) (hk : b ≤ a.h+(k:Int)) : NeverHalts m := by
  have hb : embed ⟨0,0,[],[]⟩ = blank := by
    unfold embed blank; congr 1; funext x; simp [atCell]
  have hstart := zrun_sound p m hm entry _ _ ha
  rw [hb] at hstart
  obtain ⟨hloop,hwindow⟩ := zwindow_sound p m hm b period a c hc
  exact sideCycle_never m false b (c.h-a.h) (embed a) (embed c) entry period hn
    (by change c.h-a.h ≤ 0; omega) hstart hwindow hloop (leftRel a c b k hq hl hr hk)

#print axioms zipCycle_never
end BB6Coverage.Agent3ZipSideCycle
