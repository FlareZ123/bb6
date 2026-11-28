import M44Parser2
import M44Checker
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump

-- The only controls requiring an empty left stack are entered by an actual
-- empty left pop or by the first reset parser control.
def wellCheck (q b : Nat) : Bool :=
  match action q b with
  | none => true
  | some a => decide ((a.q=12 → q=10 ∧ b=17 ∧ a.l=[]) ∧
      (a.q=13 → q=12 ∧ b=6 ∧ a.l=[]))

theorem wellChecked : (List.range 14).all (fun q => (List.range 18).all (wellCheck q)) = true := by decide

theorem action_well (q b : Nat) (a : Act) (hq : q<14) (hb : b≤17)
    (h : action q b = some a) (s d : List Nat)
    (he : endOK q b s d) (hw : well q (beforeL q b s)) : well a.q (a.l++s) := by
  have H := (List.all_eq_true.mp wellChecked) q (List.mem_range.mpr hq)
  have hb' : b<18 := by omega
  have H2 := (List.all_eq_true.mp H) b (List.mem_range.mpr hb')
  have H3 : (a.q=12 → q=10 ∧ b=17 ∧ a.l=[]) ∧
      (a.q=13 → q=12 ∧ b=6 ∧ a.l=[]) := by simpa only [wellCheck,h,decide_eq_true_eq] using H2
  intro ha
  rcases ha with ha | ha
  · obtain ⟨rfl,rfl,hl⟩ := H3.1 ha
    rw [hl,List.nil_append]
    exact he rfl
  · obtain ⟨rfl,rfl,hl⟩ := H3.2 ha
    rw [hl,List.nil_append]
    exact hw (Or.inl rfl)

structure Macro where
  q : Nat
  s : List Nat
  d : List Nat
  j : Nat
  z : Nat

def Macro.raw (x : Macro) := interpret x.q x.s x.d x.j x.z

def Invariant (c : Cert) (x : Macro) : Prop :=
  well x.q x.s ∧ ∃ l r, Represents c.left x.s l ∧ Represents c.right x.d r ∧ c.good x.q l r = true

-- One checked abstract edge yields a concrete parser step. It either
-- performs positive raw work or strictly decreases the finite parser rank.
theorem advance (c : Cert) (hc : closed c)
    (hL : (17,0) ∈ c.left.pred.get 0) (hR : (17,0) ∈ c.right.pred.get 0)
    (x : Macro) (hx : Invariant c x) :
    ∃ y n, Invariant c y ∧ run0 table n x.raw = some y.raw ∧
      (0<n ∨ rank y.q < rank x.q) := by
  obtain ⟨hw,l,r,hls,hrs,hg⟩ := hx
  have hq := (good_bounds c x.q l r hg).1
  cases hs : isLeft x.q with
  | false =>
    obtain ⟨b,d,k,hb,hd,hend,hrd,hedge⟩ := pop_sound c.right hR x.d r hrs
    have he : (b,k) ∈ (if isLeft x.q then c.left.pred.get l else c.right.pred.get r) := by simpa [hs] using hedge
    obtain ⟨a,i',j',hb',ha,hi,hj,hg'⟩ := edge_success c x.q l r (b,k) (edge_checked c hc x.q l r hg (b,k) he)
    have hbi : beforeL x.q b x.s = x.s := by simp [beforeL,hs]
    have hbr : beforeR x.q b d = x.d := by simp [beforeR,hs,hd]
    have he' : endOK x.q b x.s d := by simpa [endOK,hs] using hend
    have hw' : well x.q (beforeL x.q b x.s) := by rwa [hbi]
    have hw2 := action_well x.q b a hq hb ha x.s d he' hw'
    have hsem := action_semantics x.q b a hq hb ha x.s d x.j x.z he' hw'
    rw [hbi,hbr] at hsem
    have hli := pushWord_sound c.left a.l x.s l i' hls (by simpa [hs] using hi)
    have hrj := pushWord_sound c.right a.r d k j' hrd (by simpa [hs] using hj)
    have hp := (action_progress x.q b a hq hb ha).2
    refine ⟨⟨a.q,a.l++x.s,a.r++d,x.j+a.inc,padNext a.pad x.z⟩,cost a x.j,⟨hw2,i',j',hli,hrj,hg'⟩,hsem,?_⟩
    rcases hp with hp | hp
    · exact Or.inl (by unfold cost; omega)
    · exact Or.inr hp
  | true =>
    obtain ⟨b,s,k,hb,hd,hend,hls',hedge⟩ := pop_sound c.left hL x.s l hls
    have he : (b,k) ∈ (if isLeft x.q then c.left.pred.get l else c.right.pred.get r) := by simpa [hs] using hedge
    obtain ⟨a,i',j',hb',ha,hi,hj,hg'⟩ := edge_success c x.q l r (b,k) (edge_checked c hc x.q l r hg (b,k) he)
    have hbi : beforeL x.q b s = x.s := by simp [beforeL,hs,hd]
    have hbr : beforeR x.q b x.d = x.d := by simp [beforeR,hs]
    have he' : endOK x.q b s x.d := by simpa [endOK,hs] using hend
    have hw' : well x.q (beforeL x.q b s) := by rwa [hbi]
    have hw2 := action_well x.q b a hq hb ha s x.d he' hw'
    have hsem := action_semantics x.q b a hq hb ha s x.d x.j x.z he' hw'
    rw [hbi,hbr] at hsem
    have hli := pushWord_sound c.left a.l s k i' hls' (by simpa [hs] using hi)
    have hrj := pushWord_sound c.right a.r x.d r j' hrs (by simpa [hs] using hj)
    have hp := (action_progress x.q b a hq hb ha).2
    refine ⟨⟨a.q,a.l++s,a.r++x.d,x.j+a.inc,padNext a.pad x.z⟩,cost a x.j,⟨hw2,i',j',hli,hrj,hg'⟩,hsem,?_⟩
    rcases hp with hp | hp
    · exact Or.inl (by unfold cost; omega)
    · exact Or.inr hp

-- Rank bounds make infinite zero-cost bookkeeping impossible.
theorem live_from (c : Cert) (hc : closed c)
    (hL : (17,0) ∈ c.left.pred.get 0) (hR : (17,0) ∈ c.right.pred.get 0)
    (x : Macro) (hx : Invariant c x) (N : Nat) :
    ∃ y t, N ≤ 7*t + (6-rank y.q) ∧ Invariant c y ∧ run0 table t x.raw = some y.raw := by
  induction N with
  | zero => exact ⟨x,0,by omega,hx,rfl⟩
  | succ N ih =>
    obtain ⟨y,t,ht,hy,hr⟩ := ih
    obtain ⟨w,n,hw,hs,hp⟩ := advance c hc hL hR y hy
    have ry := rank_le y.q
    have rw := rank_le w.q
    refine ⟨w,t+n,?_,hw,join0 hr hs⟩
    rcases hp with hp | hp <;> omega

#print axioms advance
#print axioms live_from
end BB6.Agent38M44
