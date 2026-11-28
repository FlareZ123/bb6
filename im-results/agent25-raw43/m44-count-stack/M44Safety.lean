import M44Macro
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25M44
open BB6Coverage BB6Coverage.Agent31Pump

-- Exact counts on the left; the right has an arbitrary-length word over 18 symbols.
def cls (g : Nat) : Nat := if g<13 then g else 13+g%4
abbrev endSym : Nat := 17
abbrev alphabet : Nat := 18

theorem cls_lt (g : Nat) : cls g < endSym := by unfold cls endSym; split <;> omega

theorem cls_small (g : Nat) (h : g<13) : cls g = g := by simp [cls,h]

def incSym (d x : Nat) : Nat :=
  if x=endSym then endSym else if x<13 then cls (d+x) else 13+(d+(x-13))%4

theorem incSym_cls (d g : Nat) : incSym d (cls g) = cls (d+g) := by
  by_cases h : g<13
  · simp [cls_small g h,incSym,h,show g≠endSym by unfold endSym; omega]
  · have hge : 13≤g := by omega
    have hge' : ¬d+g<13 := by omega
    simp only [cls,if_neg h,if_neg hge',incSym]
    have h1 : 13+g%4≠endSym := by unfold endSym; omega
    have h2 : ¬13+g%4<13 := by omega
    rw [if_neg h1,if_neg h2]
    have h3 : 13+g%4-13=g%4 := by omega
    rw [h3]
    omega

def down4 (x : Nat) : List Nat :=
  if x<13 then [x-4] else
  match x with
  | 13 => [12,13]
  | 14 => [9,14]
  | 15 => [10,15]
  | 16 => [11,16]
  | _ => []

theorem down4_cls (g : Nat) : cls g ∈ down4 (cls (g+4)) := by
  by_cases h : g+4<13
  · have hg : g<13 := by omega
    simp [cls_small _ h,cls_small _ hg,down4,h]
  · have hg : 13≤g+4 := by omega
    by_cases hs : g<13
    · have H : g=9 ∨ g=10 ∨ g=11 ∨ g=12 := by omega
      rcases H with rfl|rfl|rfl|rfl <;> decide
    · have hm : g%4=0 ∨ g%4=1 ∨ g%4=2 ∨ g%4=3 := by omega
      have he : (g+4)%4=g%4 := by omega
      simp only [cls,if_neg hs,if_neg h,he]
      rcases hm with H|H|H|H <;> rw [H] <;> decide

def word (r : List Nat) : List Nat := r.map cls ++ [endSym]
def symHead (r : List Nat) : Nat := if r=[] then endSym else cls (r.headD 0)
def symTail (r : List Nat) : List Nat := if r=[] then [] else word r.tail

theorem word_view (r : List Nat) : word r = symHead r :: symTail r := by cases r <;> simp [word,symHead,symTail]
theorem word_cons (g : Nat) (r : List Nat) : word (g::r)=cls g::word r := rfl

theorem symHead_lt (r : List Nat) : symHead r < alphabet := by
  cases r with
  | nil => decide
  | cons g r => simpa [symHead] using Nat.lt_trans (cls_lt g) (by decide : endSym<alphabet)

theorem symHead_nonzero (r : List Nat) (h : r=[] ∨ r.headD 0≠0) : symHead r≠0 := by
  cases r with
  | nil => decide
  | cons g r =>
    have hg : g≠0 := by simpa using h
    simp only [symHead,List.cons_ne_nil,ite_false,List.headD_cons,cls]
    by_cases hg13 : g<13 <;> simp [hg13,hg]

theorem symHead_zero_iff (r : List Nat) : symHead r=0 ↔ ∃ t, r=0::t := by
  cases r with
  | nil => simp [symHead,endSym]
  | cons g r =>
    simp only [symHead,List.cons_ne_nil,ite_false,List.headD_cons,List.cons.injEq, and_true]
    by_cases hg : g<13
    · simp [cls,hg]
    · simp [cls,hg,show g≠0 by omega]

theorem word_inc (d : Nat) (r : List Nat) : word (incR d r) = incSym d (symHead r)::symTail r := by
  cases r with
  | nil => simp [incR,word,symHead,symTail,incSym]
  | cons g r =>
    simp only [incR,word_cons,symHead,symTail,List.cons_ne_nil,ite_false,List.headD_cons,List.tail_cons,incSym_cls]

def validWord (w : List Nat) : Prop := ∀ x∈w, x<alphabet

theorem word_valid (r : List Nat) : validWord (word r) := by
  intro x hx
  rcases List.mem_append.mp hx with h|h
  · obtain ⟨g,_,rfl⟩ := List.mem_map.mp h
    exact Nat.lt_trans (cls_lt g) (by decide)
  · simp at h
    subst x
    decide

theorem symTail_valid (r : List Nat) : validWord (symTail r) := by
  cases r with
  | nil => simp [symTail,validWord]
  | cons g r => simpa [symTail] using word_valid r

-- Only partial left edges are allowed, and every missing push is an unsafe guard.
structure Cert where
  n : Nat
  head : Nat → Nat
  next : Nat → Nat → Option Nat
  prev : Nat → List Nat
  start : Nat → Nat
  edges : Nat → Nat → List Nat
  final : Nat

def push (c : Cert) (s a : Nat) : Option Nat :=
  if s=0 ∧ a=0 then some 0 else if a<13 then c.next s a else none

def push2 (c : Cert) (t a b : Nat) : Option Nat := (push c t b).bind (fun u => push c u a)
def push3 (c : Cert) (t a b d : Nat) : Option Nat := (push c t d).bind (fun u => push2 c u a b)

def edgeOK (c : Cert) (s a : Nat) : Bool :=
  match push c s a with
  | none => true
  | some t => decide (t<c.n ∧ c.head t=a ∧ s∈c.prev t ∧ (t=0 → s=0 ∧ a=0))

def graphCheck (c : Cert) (s : Nat) : Bool :=
  decide (c.head s<13) && (List.range 13).all (edgeOK c s)

structure GraphOK (c : Cert) : Prop where
  nonempty : 0<c.n
  head0 : c.head 0=0
  prev0 : 0∈c.prev 0
  checks : ∀ s, s<c.n → graphCheck c s = true

theorem push_lt {c : Cert} {s a t : Nat} (h : push c s a=some t) : a<13 := by
  unfold push at h
  split at h
  · omega
  · split at h
    · assumption
    · contradiction

theorem graph_edge {c : Cert} (hc : GraphOK c) {s a t : Nat} (hs : s<c.n) (hp : push c s a=some t) :
    t<c.n ∧ c.head t=a ∧ s∈c.prev t ∧ (t=0 → s=0 ∧ a=0) := by
  have hh := (Bool.and_eq_true _ _).mp (hc.checks s hs)
  have ha : a∈List.range 13 := List.mem_range.mpr (push_lt hp)
  have h := List.all_eq_true.mp hh.2 a ha
  unfold edgeOK at h
  rw [hp] at h
  exact of_decide_eq_true h

inductive Rep (c : Cert) : List Nat → Nat → Prop
  | nil : Rep c [] 0
  | cons {a l s t} : Rep c l s → (a≠0 ∨ l≠[]) → push c s a=some t → Rep c (a::l) t

theorem rep_bound {c : Cert} (hc : GraphOK c) {l s} (h : Rep c l s) : s<c.n := by
  induction h with
  | nil => exact hc.nonempty
  | cons _ _ hp ih => exact (graph_edge hc ih hp).1

theorem rep_empty {c : Cert} (hc : GraphOK c) {l s} (h : Rep c l s) : s=0 ↔ l=[] := by
  cases h with
  | nil => simp
  | cons h hr hp =>
    have H := (graph_edge hc (rep_bound hc h) hp).2.2.2
    constructor
    · intro ht
      obtain ⟨hs,ha⟩ := H ht
      rcases hr with hn|hn
      · contradiction
      · have hh : _ = [] := (rep_empty hc h).mp hs
        contradiction
    · intro hn; contradiction
 termination_by l.length
 decreasing_by simp_wf

theorem rep_view {c : Cert} (hc : GraphOK c) {l s} (h : Rep c l s) :
    c.head s=l.headD 0 ∧ ∃ t, Rep c l.tail t ∧ t∈c.prev s := by
  cases h with
  | nil => exact ⟨hc.head0,0,Rep.nil,hc.prev0⟩
  | cons hr _ hp =>
    have H := graph_edge hc (rep_bound hc hr) hp
    exact ⟨H.2.1,_,hr,H.2.2.1⟩

theorem rep_push {c : Cert} (hc : GraphOK c) {l s a t} (h : Rep c l s) (hp : push c s a=some t) :
    Rep c (pushL a l) t := by
  unfold pushL
  split
  · obtain ⟨ha,hl⟩ := ‹a=0 ∧ l=[]›
    have hs := (rep_empty hc h).mpr hl
    subst a; subst l; subst s
    have ht : t=0 := (Option.some.inj hp).symm
    subst t
    exact Rep.nil
  · apply Rep.cons h _ hp
    by_cases ha : a=0
    · exact Or.inr (fun hl => ‹¬(a=0 ∧ l=[])› ⟨ha,hl⟩)
    · exact Or.inl ha

theorem rep_push2 {c : Cert} (hc : GraphOK c) {l s a b t} (h : Rep c l s) (hp : push2 c s a b=some t) :
    Rep c (pushL a (pushL b l)) t := by
  obtain ⟨u,hu,hp'⟩ := Option.bind_eq_some_iff.mp hp
  exact rep_push hc (rep_push hc h hu) hp'

theorem rep_push3 {c : Cert} (hc : GraphOK c) {l s a b d t} (h : Rep c l s) (hp : push3 c s a b d=some t) :
    Rep c (pushL a (pushL b (pushL d l))) t := by
  obtain ⟨u,hu,hp'⟩ := Option.bind_eq_some_iff.mp hp
  exact rep_push2 hc (rep_push hc h hu) hp'

theorem pushL_pos (a : Nat) (l : List Nat) (h : a≠0) : pushL a l=a::l := by simp [pushL,h]
theorem pushL_cons (a b : Nat) (l : List Nat) : pushL a (b::l)=a::b::l := by simp [pushL]

-- A finite NFA of bad predecessors. No least-fixed-point assumption is used.
def reach (c : Cert) (p : Nat) : List Nat → List Nat
  | [] => [p]
  | x::w => (c.edges p x).flatMap (fun q => reach c q w)

theorem reach_append (c : Cert) (p s : Nat) (a b : List Nat) :
    s∈reach c p (a++b) ↔ ∃ q∈reach c p a, s∈reach c q b := by
  induction a generalizing p with
  | nil => simp [reach]
  | cons x a ih =>
    simp only [List.cons_append,reach,List.mem_flatMap]
    constructor
    · rintro ⟨q,hq,hs⟩
      obtain ⟨v,hv,hs'⟩ := (ih q).mp hs
      exact ⟨v,⟨q,hq,hv⟩,hs'⟩
    · rintro ⟨v,⟨q,hq,hv⟩,hs⟩
      exact ⟨q,hq,(ih q).mpr ⟨v,hv,hs⟩⟩

def Safe (c : Cert) (s : Nat) (w : List Nat) : Prop := c.final∉reach c (c.start s) w

def ruleOK (c : Cert) (s : Nat) (a : List Nat) (t : Option Nat) (b : List Nat) : Bool :=
  let src := reach c (c.start s) a
  match t with
  | none => decide (c.final∈src)
  | some q => (reach c (c.start q) b).all (fun v => decide (v∈src))

def universalCheck (c : Cert) : Bool := (List.range alphabet).all (fun x => decide (c.final∈c.edges c.final x))

theorem universal_path {c : Cert} (hc : universalCheck c=true) (w : List Nat) (hw : validWord w) :
    c.final∈reach c c.final w := by
  induction w with
  | nil => simp [reach]
  | cons x w ih =>
    have hx : x<alphabet := hw x (by simp)
    have he := of_decide_eq_true (List.all_eq_true.mp hc x (List.mem_range.mpr hx))
    exact List.mem_flatMap.mpr ⟨c.final,he,ih (fun y hy => hw y (by simp [hy]))⟩

theorem rule_bad {c : Cert} {s a b w} (hu : universalCheck c=true)
    (h : ruleOK c s a none b=true) (hw : validWord w) : ¬Safe c s (a++w) := by
  intro hs
  exact hs ((reach_append c (c.start s) c.final a w).mpr ⟨c.final,of_decide_eq_true h,universal_path hu w hw⟩)

theorem rule_safe {c : Cert} {s a t b w} (h : ruleOK c s a (some t) b=true) (hs : Safe c s (a++w)) : Safe c t (b++w) := by
  intro hb
  obtain ⟨v,hv,hf⟩ := (reach_append c (c.start t) c.final b w).mp hb
  have hv' : v∈reach c (c.start s) a := of_decide_eq_true (List.all_eq_true.mp h v hv)
  exact hs ((reach_append c (c.start s) c.final a w).mpr ⟨v,hv',hf⟩)

theorem rule_exists {c : Cert} {s a t b w} (hu : universalCheck c=true)
    (h : ruleOK c s a t b=true) (hs : Safe c s (a++w)) (hw : validWord w) :
    ∃ q, t=some q ∧ Safe c q (b++w) := by
  cases t with
  | none => exact False.elim (rule_bad hu h hw hs)
  | some q => exact ⟨q,rfl,rule_safe h hs⟩

-- Direct macro-prefix checks, derived from the pushdown saturation certificate.
def badCheck (c : Cert) (s : Nat) : Bool :=
  ruleOK c s [0] none [] &&
  (if c.head s<2 then ruleOK c s [1] none [] else true) &&
  (List.range alphabet).all (fun x => if x=1 then true else ruleOK c s [3,x] none [])

def tailCheck (c : Cert) (s t : Nat) : Bool :=
  let a := c.head s
  ruleOK c s [endSym] (some t) [cls (a+2),1,endSym] &&
  (List.range alphabet).all (fun x =>
    (if 4≤x ∧ x<endSym then (down4 x).all (fun y => ruleOK c s [x] (some t) [cls (a+2),1,y]) else true) &&
    (if 2≤a then ruleOK c s [1,x] (push2 c t 2 (a-2)) [incSym 1 x] else true) &&
    (if x=0 then true else ruleOK c s [2,x] (push c t (a+3)) [x]) &&
    ruleOK c s [2,0,x] (some t) [incSym (a+5) x] &&
    (if x=0 then true else ruleOK c s [3,1,x] (push3 c t 2 0 (a+2)) [x]) &&
    ruleOK c s [3,1,0,x] (push2 c t 0 (a+2)) [incSym 4 x])

def stateCheck (c : Cert) (s : Nat) : Bool := graphCheck c s && badCheck c s && (c.prev s).all (tailCheck c s)

structure Valid (c : Cert) : Prop where
  nonempty : 0<c.n
  head0 : c.head 0=0
  prev0 : 0∈c.prev 0
  universal : universalCheck c=true
  root : Safe c 0 [endSym]
  check : ∀ s, s<c.n → stateCheck c s=true

theorem valid_graph {c : Cert} (h : Valid c) : GraphOK c := by
  refine ⟨h.nonempty,h.head0,h.prev0,?_⟩
  intro s hs
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp (h.check s hs)).1).1

theorem valid_bad {c : Cert} (h : Valid c) {s} (hs : s<c.n) : badCheck c s=true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp (h.check s hs)).1).2

theorem valid_tail {c : Cert} (h : Valid c) {s t} (hs : s<c.n) (ht : t∈c.prev s) : tailCheck c s t=true :=
  List.all_eq_true.mp ((Bool.and_eq_true _ _).mp (h.check s hs)).2 t ht

theorem bad_zero {c : Cert} {s} (h : badCheck c s=true) : ruleOK c s [0] none []=true := by
  simp only [badCheck,Bool.and_eq_true] at h
  exact h.1.1

theorem bad_one {c : Cert} {s} (h : badCheck c s=true) (ha : c.head s<2) : ruleOK c s [1] none []=true := by
  simp only [badCheck,Bool.and_eq_true,if_pos ha] at h
  exact h.1.2

theorem bad_three {c : Cert} {s x} (h : badCheck c s=true) (hx : x<alphabet) (hne : x≠1) : ruleOK c s [3,x] none []=true := by
  simp only [badCheck,Bool.and_eq_true] at h
  have H := List.all_eq_true.mp h.2 x (List.mem_range.mpr hx)
  simpa only [if_neg hne] using H

theorem check_empty {c : Cert} {s t} (h : tailCheck c s t=true) : ruleOK c s [endSym] (some t) [cls (c.head s+2),1,endSym]=true :=
  (Bool.and_eq_true _ _).mp h |>.1

theorem check_symbol {c : Cert} {s t x} (h : tailCheck c s t=true) (hx : x<alphabet) :
    (if 4≤x ∧ x<endSym then (down4 x).all (fun y => ruleOK c s [x] (some t) [cls (c.head s+2),1,y]) else true)=true ∧
    (if 2≤c.head s then ruleOK c s [1,x] (push2 c t 2 (c.head s-2)) [incSym 1 x] else true)=true ∧
    (if x=0 then true else ruleOK c s [2,x] (push c t (c.head s+3)) [x])=true ∧
    ruleOK c s [2,0,x] (some t) [incSym (c.head s+5) x]=true ∧
    (if x=0 then true else ruleOK c s [3,1,x] (push3 c t 2 0 (c.head s+2)) [x])=true ∧
    ruleOK c s [3,1,0,x] (push2 c t 0 (c.head s+2)) [incSym 4 x]=true := by
  have H := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h).2 x (List.mem_range.mpr hx)
  simp only [Bool.and_eq_true] at H
  exact ⟨H.1.1.1.1.1,H.1.1.1.1.2,H.1.1.1.2,H.1.1.2,H.1.2,H.2⟩

theorem symHead_small {r : List Nat} {k : Nat} (hk : k<13) (h : symHead r=k) : ∃ t, r=k::t := by
  cases r with
  | nil => simp [symHead,endSym] at h; omega
  | cons g r =>
    simp only [symHead,List.cons_ne_nil,ite_false,List.headD_cons,cls] at h
    by_cases hg : g<13
    · simp [hg] at h
      exact ⟨r,by rw [h]⟩
    · simp [hg] at h; omega

def Good (c : Cert) (l r : List Nat) : Prop := ∃ s, Rep c l s ∧ Safe c s (word r)

theorem good_empty {c : Cert} (hc : Valid c) : Good c [] [] := ⟨0,Rep.nil,hc.root⟩

-- Every accepted section has another positive-length live section. No bound on either stack.
theorem good_step {c : Cert} (hc : Valid c) (l r : List Nat) (h : Good c l r) :
    ∃ n l' r', 0<n ∧ runs n (sec l r) (sec l' r') ∧ Good c l' r' := by
  obtain ⟨s,hr,hs⟩ := h
  have hg := valid_graph hc
  have hb := rep_bound hg hr
  obtain ⟨ha,t,ht,htm⟩ := rep_view hg hr
  have htcheck := valid_tail hc hb htm
  have hbcheck := valid_bad hc hb
  cases r with
  | nil =>
    have H := check_empty htcheck
    rw [ha] at H
    have J := rule_safe (w:=[]) H hs
    exact ⟨l.headD 0+9,l.tail,[l.headD 0+2,1],by omega,macro_empty l,
      t,ht,J⟩
  | cons g r =>
    have H : g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ 4≤g := by omega
    rcases H with rfl|rfl|rfl|rfl|hge
    · have H := bad_zero hbcheck
      exact False.elim (rule_bad hc.universal H (word_valid r) hs)
    · have ha2 : 2≤l.headD 0 := by
        by_cases hgood : 2≤l.headD 0
        · exact hgood
        · have H := bad_one hbcheck (by rw [ha]; omega)
          exact False.elim (rule_bad hc.universal H (word_valid r) hs)
      have K := (check_symbol htcheck (symHead_lt r)).2.1
      rw [ha,if_pos ha2] at K
      rw [word_cons,show cls 1=1 by decide,word_view r] at hs
      obtain ⟨q,hp,hq⟩ := rule_exists hc.universal K hs (symTail_valid r)
      have H := rep_push2 hg ht hp
      have Hq : Safe c q (word (incR 1 r)) := by rw [word_inc]; exact hq
      exact ⟨7,_,_,by decide,macro_one l r ha2,q,H,Hq⟩
    · by_cases hz : symHead r=0
      · obtain ⟨r',rfl⟩ := symHead_small (by decide : 0<13) hz
        have K := (check_symbol htcheck (symHead_lt r')).2.2.2.1
        rw [ha] at K
        rw [word_cons,word_cons,show cls 2=2 by decide,show cls 0=0 by decide,word_view r'] at hs
        have J := rule_safe K hs
        have Hq : Safe c t (word (incR (l.headD 0+5) r')) := by rw [word_inc]; exact J
        exact ⟨l.headD 0+7,_,_,by omega,macro_two_long l r',t,ht,Hq⟩
      · have hp : r=[] ∨ r.headD 0≠0 := by
          cases r with
          | nil => exact Or.inl rfl
          | cons x r =>
            apply Or.inr; intro hx
            change x=0 at hx; subst x
            exact hz rfl
        have K := (check_symbol htcheck (symHead_lt r)).2.2.1
        rw [if_neg hz,ha] at K
        rw [word_cons,show cls 2=2 by decide,word_view r] at hs
        obtain ⟨q,hq,hqs⟩ := rule_exists hc.universal K hs (symTail_valid r)
        have Hq := rep_push hg ht hq
        rw [pushL_pos _ _ (by omega)] at Hq
        exact ⟨3,_,_,by decide,macro_two_short l r hp,q,Hq,by rw [word_view r]; exact hqs⟩
    · have h1 : symHead r=1 := by
        by_cases hh : symHead r=1
        · exact hh
        · have H := bad_three hbcheck (symHead_lt r) hh
          rw [word_cons,show cls 3=3 by decide,word_view r] at hs
          exact False.elim (rule_bad hc.universal H (symTail_valid r) hs)
      obtain ⟨r',rfl⟩ := symHead_small (by decide : 1<13) h1
      by_cases hz : symHead r'=0
      · obtain ⟨r'',rfl⟩ := symHead_small (by decide : 0<13) hz
        have K := (check_symbol htcheck (symHead_lt r'')).2.2.2.2.2
        rw [ha] at K
        rw [word_cons,word_cons,word_cons,show cls 3=3 by decide,show cls 1=1 by decide,show cls 0=0 by decide,word_view r''] at hs
        obtain ⟨q,hq,hqs⟩ := rule_exists hc.universal K hs (symTail_valid r'')
        have Hq := rep_push2 hg ht hq
        rw [pushL_pos (l.headD 0+2) _ (by omega),pushL_cons] at Hq
        exact ⟨9,_,_,by decide,macro_three_long l r'',q,Hq,by rw [word_inc]; exact hqs⟩
      · have hp : r'=[] ∨ r'.headD 0≠0 := by
          cases r' with
          | nil => exact Or.inl rfl
          | cons x r' =>
            apply Or.inr; intro hx
            change x=0 at hx; subst x
            exact hz rfl
        have K := (check_symbol htcheck (symHead_lt r')).2.2.2.2.1
        rw [if_neg hz,ha] at K
        rw [word_cons,word_cons,show cls 3=3 by decide,show cls 1=1 by decide,word_view r'] at hs
        obtain ⟨q,hq,hqs⟩ := rule_exists hc.universal K hs (symTail_valid r')
        have Hq := rep_push3 hg ht hq
        rw [pushL_pos (l.headD 0+2) _ (by omega),pushL_cons,pushL_cons] at Hq
        exact ⟨6,_,_,by decide,macro_three_short l r' hp,q,Hq,by rw [word_view r']; exact hqs⟩
    · let k := g-4
      have hkg : k+4=g := by dsimp [k]; omega
      have hg4 : 4≤cls g := by unfold cls; by_cases hh : g<13 <;> simp [hh] <;> omega
      have H := (check_symbol htcheck (Nat.lt_trans (cls_lt g) (by decide : endSym<alphabet))).1
      rw [if_pos ⟨hg4,cls_lt g⟩] at H
      have hm : cls k∈down4 (cls g) := by rw [← hkg]; exact down4_cls k
      -- Rewrite only the right argument g, not the abbreviation k itself.
      have K := List.all_eq_true.mp H (cls k) hm
      rw [ha] at K
      have J := rule_safe K hs
      have Hq : Safe c t (word ([l.headD 0+2,1,k]++r)) := by
        exact J
      exact ⟨l.headD 0+9,_,_,by omega,by rw [← hkg]; exact macro_long l r k,t,ht,Hq⟩

theorem arbitrary_live {c : Cert} (hc : Valid c) (N : Nat) :
    ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩=some z := by
  have H : ∀ N, ∃ t l r, N≤t ∧ runs t ⟨0,[],[]⟩ (sec l r) ∧ Good c l r := by
    intro N
    induction N with
    | zero =>
      refine ⟨0,[],[],by omega,?_,good_empty hc⟩
      exact ⟨⟨0,[],[]⟩,rfl,⟨rfl,bitsEq_symm (zeros_eq_nil 1),bitsEq_refl _⟩⟩
    | succ N ih =>
      obtain ⟨t,l,r,ht,hr,hg⟩ := ih
      obtain ⟨k,l',r',hk,hk',hg'⟩ := good_step hc l r hg
      exact ⟨t+k,l',r',by omega,runs_join hr hk',hg'⟩
  obtain ⟨t,l,r,ht,⟨z,hz,_⟩,_⟩ := H N
  exact ⟨t,z,ht,hz⟩

#print axioms down4_cls
#print axioms graph_edge
#print axioms rep_view
#print axioms rule_exists
#print axioms check_symbol
#print axioms good_step
#print axioms arbitrary_live
end BB6.Agent25M44
