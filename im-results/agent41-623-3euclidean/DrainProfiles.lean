import Lean

/-! Exact MSB ternary fold of entire #623 drain output profiles. Each profile
contains a finite exceptional prefix and one uniform affine tail. The six
recurrence laws are the already established exact source flat-drain laws. -/
namespace BB6.Agent41DrainProfiles

abbrev Outcome := Option (Int × Int)
abbrev Drain := Nat → Nat → Nat → Option (Nat × Nat)

def delta (j e : Int) (v : Outcome) : Outcome :=
  v.map fun z => (z.1+j, z.2+e)

def render (v : Outcome) (a b d : Nat) : Option (Nat × Nat) :=
  v.map fun z => (((a : Int)+z.1).toNat, (((d+3*b : Nat) : Int)+z.2).toNat)

structure Profile where
  front : List Outcome
  tail : Int × Int
  deriving DecidableEq, Repr

/-- The finite prefix stores offsets relative to the uniform affine tail.
Thus a uniform shift changes two integers and shares the entire prefix. -/
def get (p : Profile) (a : Nat) : Outcome :=
  delta p.tail.1 p.tail.2 (p.front.getD a (some (0,0)))
def base : Profile := ⟨[],(0,0)⟩
def shift (p : Profile) (j e : Int) : Profile :=
  ⟨p.front,(p.tail.1+j,p.tail.2+e)⟩
def pop (p : Profile) : Profile := ⟨p.front.tail,p.tail⟩
def relative (v : Outcome) (p : Profile) : Outcome :=
  delta (-p.tail.1) (-p.tail.2) v
/-- Avoid redundant trailing zero offsets. Only an empty prefix may be
trimmed, so pushes and pops remain constant-time list operations. -/
def push (v : Outcome) (p : Profile) : Profile :=
  if p.front=[] ∧ relative v p=some (0,0) then p
  else ⟨relative v p::p.front,p.tail⟩
def up (p : Profile) : Profile := shift (pop p) 1 0
def left (p : Profile) : Profile := push none (shift p (-1) 4)
def right (p q : Profile) : Profile := push (delta 0 1 (get p 0)) (shift q (-1) 2)

private theorem delta_add (v : Outcome) (j e k f : Int) :
    delta j e (delta k f v) = delta (k+j) (f+e) v := by
  cases v with
  | none => rfl
  | some z => simp [delta,Int.add_assoc]
private theorem delta_zero (v : Outcome) : delta 0 0 v = v := by
  cases v <;> simp [delta]
private theorem get_shift (p : Profile) (a : Nat) (j e : Int) :
    get (shift p j e) a = delta j e (get p a) := by
  simp only [get,shift,delta_add]
private theorem get_pop (p : Profile) (a : Nat) :
    get (pop p) a = get p (a+1) := by
  simp [get, pop, List.getD_eq_getElem?_getD, List.getElem?_tail]
private theorem relative_cancel (v : Outcome) (p : Profile) :
    delta p.tail.1 p.tail.2 (relative v p)=v := by
  rw [relative,delta_add,show -p.tail.1+p.tail.1=0 by omega,
    show -p.tail.2+p.tail.2=0 by omega,delta_zero]
private theorem get_push_zero (v : Outcome) (p : Profile) :
    get (push v p) 0 = v := by
  unfold push
  split
  · rename_i h
    rw [get,h.1,List.getD_nil,←h.2,relative_cancel]
  · simp only [get,List.getD_cons_zero,relative_cancel]
private theorem get_push_succ (v : Outcome) (p : Profile) (a : Nat) :
    get (push v p) (a+1) = get p a := by
  unfold push
  split
  · rename_i h
    simp [get,h.1]
  · simp [get]
private theorem get_up (p : Profile) (a : Nat) :
    get (up p) a = delta 1 0 (get p (a+1)) := by
  rw [up,get_shift,get_pop]
private theorem get_left_zero (p : Profile) : get (left p) 0 = none := by rw [left,get_push_zero]
private theorem get_left_succ (p : Profile) (a : Nat) :
    get (left p) (a+1) = delta (-1) 4 (get p a) := by
  rw [left,get_push_succ,get_shift]
private theorem get_right_zero (p q : Profile) :
    get (right p q) 0 = delta 0 1 (get p 0) := by rw [right,get_push_zero]
private theorem get_right_succ (p q : Profile) (a : Nat) :
    get (right p q) (a+1) = delta (-1) 2 (get q a) := by
  rw [right,get_push_succ,get_shift]

private theorem render_delta (v : Outcome) (a b d a' b' d' : Nat)
    (j e : Int) (ha : (a : Int)+j=(a' : Int))
    (hd : ((d+3*b : Nat) : Int)+e=((d'+3*b' : Nat) : Int)) :
    render (delta j e v) a b d = render v a' b' d' := by
  cases v with
  | none => rfl
  | some z =>
    rcases z with ⟨k,f⟩
    simp only [render,delta,Option.map_some]
    have hj : (a : Int)+(k+j)=(a' : Int)+k := by omega
    have he : ((d+3*b : Nat) : Int)+(f+e)=((d'+3*b' : Nat) : Int)+f := by omega
    rw [hj,he]

structure Laws (B : Drain) : Prop where
  zero : ∀ a d, B a 0 d = some (a,d)
  three : ∀ a q d, 0<q → B a (3*q) d = B (a+1) (q-1) (d+6*q+3)
  oneZero : ∀ q d, B 0 (3*q+1) d = none
  oneSucc : ∀ a q d, B (a+1) (3*q+1) d = B a q (d+6*q+7)
  twoZero : ∀ q d, B 0 (3*q+2) d = B 0 q (d+6*q+7)
  twoSucc : ∀ a q d, B (a+1) (3*q+2) d = B a (q+1) (d+6*q+5)

def Represents (B : Drain) (p : Profile) (b : Nat) : Prop :=
  ∀ a d, render (get p a) a b d = B a b d

private theorem rep_base (B : Drain) (h : Laws B) : Represents B base 0 := by
  intro a d
  rw [h.zero]
  simp [base,get,render,delta,List.getD_eq_getElem?_getD]
private theorem rep_up (B : Drain) (h : Laws B) (p : Profile) (q : Nat)
    (hq : 0<q) (hp : Represents B p (q-1)) : Represents B (up p) (3*q) := by
  intro a d
  rw [get_up, render_delta _ _ _ _ (a+1) (q-1) (d+6*q+3) 1 0 (by simp <;> omega) (by simp <;> omega), hp, h.three _ _ _ hq]
private theorem rep_left (B : Drain) (h : Laws B) (p : Profile) (q : Nat)
    (hp : Represents B p q) : Represents B (left p) (3*q+1) := by
  intro a d
  cases a with
  | zero => rw [get_left_zero,h.oneZero]; rfl
  | succ a =>
    rw [get_left_succ, render_delta _ _ _ _ a q (d+6*q+7) (-1) 4 (by simp <;> omega) (by simp <;> omega), hp, h.oneSucc]
private theorem rep_right (B : Drain) (h : Laws B) (p r : Profile) (q : Nat)
    (hp : Represents B p q) (hr : Represents B r (q+1)) : Represents B (right p r) (3*q+2) := by
  intro a d
  cases a with
  | zero =>
    rw [get_right_zero, render_delta _ _ _ _ 0 q (d+6*q+7) 0 1 (by omega) (by simp <;> omega),hp,h.twoZero]
  | succ a =>
    rw [get_right_succ, render_delta _ _ _ _ a (q+1) (d+6*q+5) (-1) 2 (by simp <;> omega) (by simp <;> omega),hr,h.twoSucc]

structure Triple where
  lo : Profile
  mid : Profile
  hi : Profile
  deriving DecidableEq, Repr

def seed : Triple := ⟨base,base,left base⟩

def step (z : Bool) (s : Triple) (r : Nat) : Triple :=
  let em := if z then base else right s.lo s.mid
  let e0 := if z then base else up s.lo
  let e1 := left s.mid
  let e2 := right s.mid s.hi
  let ep := up s.mid
  if r=0 then ⟨em,e0,e1⟩ else if r=1 then ⟨e0,e1,e2⟩ else ⟨e1,e2,ep⟩

def profiles (b : Nat) : Triple :=
  if b=0 then seed else step (b/3 == 0) (profiles (b/3)) (b%3)
termination_by b
decreasing_by omega

def Encodes (B : Drain) (s : Triple) (b : Nat) : Prop :=
  Represents B s.lo (b-1) ∧ Represents B s.mid b ∧ Represents B s.hi (b+1)

private theorem enc_seed (B : Drain) (h : Laws B) : Encodes B seed 0 := by
  have hb := rep_base B h
  exact ⟨hb,hb,rep_left B h base 0 hb⟩

private theorem enc_step (B : Drain) (h : Laws B) (s : Triple) (q r : Nat)
    (hr : r<3) (hs : Encodes B s q) : Encodes B (step (q == 0) s r) (3*q+r) := by
  have em : Represents B (if q == 0 then base else right s.lo s.mid) (3*q-1) := by
    by_cases hz : q=0
    · simpa [hz] using rep_base B h
    · have hq : q-1+1=q := by omega
      have ht : 3*(q-1)+2=3*q-1 := by omega
      have hm : (q == 0) = false := by simp [hz]
      simp only [hm, Bool.false_eq_true, if_false]
      rw [←ht]
      exact rep_right B h _ _ _ hs.1 (by rw [hq]; exact hs.2.1)
  have e0 : Represents B (if q == 0 then base else up s.lo) (3*q) := by
    by_cases hz : q=0
    · simpa [hz] using rep_base B h
    · have hm : (q == 0) = false := by simp [hz]
      simp only [hm, Bool.false_eq_true, if_false]
      exact rep_up B h _ _ (by omega) hs.1
  have e1 := rep_left B h _ _ hs.2.1
  have e2 := rep_right B h _ _ _ hs.2.1 hs.2.2
  have ep : Represents B (up s.mid) (3*q+3) := by
    have ht : 3*(q+1)=3*q+3 := by omega
    rw [←ht]
    exact rep_up B h _ _ (by omega) (by simpa using hs.2.1)
  have hh : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases hh with rfl|rfl|rfl
  · exact ⟨em,e0,e1⟩
  · have ht : 3*q+1-1=3*q := by omega
    simp only [Encodes,step,Nat.one_ne_zero,if_false,if_true,ht]
    exact ⟨e0,e1,e2⟩
  · have ht : 3*q+2-1=3*q+1 := by omega
    have ht' : 3*q+2+1=3*q+3 := by omega
    simp only [Encodes,step,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide,if_false,ht,ht']
    exact ⟨e1,e2,ep⟩

/-- Exact simultaneous profiles for the three neighboring block counts. -/
theorem profiles_correct (B : Drain) (h : Laws B) (b : Nat) : Encodes B (profiles b) b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    rw [profiles]
    by_cases hb : b=0
    · simpa [hb] using enc_seed B h
    · simp only [if_neg hb]
      have hq : b/3 < b := by omega
      have he : 3*(b/3)+b%3=b := by omega
      simpa only [he] using enc_step B h (profiles (b/3)) (b/3) (b%3)
        (Nat.mod_lt _ (by decide)) (ih _ hq)

/-- No arbitrary budget restriction: every first and third counter is covered. -/
theorem drain_exact (B : Drain) (h : Laws B) (a b d : Nat) :
    B a b d = render (get (profiles b).mid a) a b d :=
  ((profiles_correct B h b).2.1 a d).symm

/-- Once the finite exceptional prefix is passed, the output is a translation
    of the first and third counters with constant drift and excess. -/
theorem tail_exact (B : Drain) (h : Laws B) (a b d : Nat)
    (ha : (profiles b).mid.front.length ≤ a) :
    B a b d = some (((a : Int)+(profiles b).mid.tail.1).toNat,
      (((d+3*b : Nat) : Int)+(profiles b).mid.tail.2).toNat) := by
  rw [drain_exact B h]
  have ht : get (profiles b).mid a = some (profiles b).mid.tail := by
    simp only [get,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    simp [delta]
  rw [ht]
  rfl

/-- All three neighboring profiles preserve any property closed under the
three elementary profile operations. -/
theorem fold_preserves (P : Profile → Prop) (hbase : P base)
    (hup : ∀ p, P p → P (up p)) (hleft : ∀ p, P p → P (left p))
    (hright : ∀ p q, P p → P q → P (right p q)) (b : Nat) :
    P (profiles b).lo ∧ P (profiles b).mid ∧ P (profiles b).hi := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    rw [profiles]
    by_cases hz : b=0
    · simp only [hz,if_true,seed]
      exact ⟨hbase,hbase,hleft _ hbase⟩
    · simp only [if_neg hz]
      obtain ⟨ha,hb,hc⟩ := ih (b/3) (by omega)
      have hem : P (if b/3 == 0 then base else right (profiles (b/3)).lo (profiles (b/3)).mid) := by
        split <;> first | exact hbase | exact hright _ _ ha hb
      have he0 : P (if b/3 == 0 then base else up (profiles (b/3)).lo) := by
        split <;> first | exact hbase | exact hup _ ha
      have he1 := hleft _ hb
      have he2 := hright _ _ hb hc
      have hep := hup _ hb
      by_cases h0 : b%3=0
      · simp only [step,if_pos h0]
        exact ⟨hem,he0,he1⟩
      · by_cases h1 : b%3=1
        · simp only [step,if_neg h0,if_pos h1]
          exact ⟨he0,he1,he2⟩
        · simp only [step,if_neg h0,if_neg h1]
          exact ⟨he1,he2,hep⟩

def Valid (p : Profile) : Prop :=
  ∀ a j e, get p a = some (j,e) → 0≤(a : Int)+j ∧ 0≤e

private theorem valid_base : Valid base := by
  intro a j e h
  simp [get,base,delta] at h
  obtain ⟨rfl,rfl⟩ := h
  omega
private theorem valid_up (p : Profile) (h : Valid p) : Valid (up p) := by
  intro a j e hj
  rw [get_up] at hj
  cases hg : get p (a+1) with
  | none => simp [delta,hg] at hj
  | some z =>
    rcases z with ⟨k,f⟩
    have hv := h _ _ _ hg
    simp [delta,hg] at hj
    simp at hv
    omega
private theorem valid_left (p : Profile) (h : Valid p) : Valid (left p) := by
  intro a j e hj
  cases a with
  | zero => rw [get_left_zero] at hj; cases hj
  | succ a =>
    rw [get_left_succ] at hj
    cases hg : get p a with
    | none => simp [delta,hg] at hj
    | some z =>
      rcases z with ⟨k,f⟩
      have hv := h _ _ _ hg
      simp [delta,hg] at hj
      simp
      omega
private theorem valid_right (p q : Profile) (hp : Valid p) (hq : Valid q) : Valid (right p q) := by
  intro a j e hj
  cases a with
  | zero =>
    rw [get_right_zero] at hj
    cases hg : get p 0 with
    | none => simp [delta,hg] at hj
    | some z =>
      rcases z with ⟨k,f⟩
      have hv := hp _ _ _ hg
      simp [delta,hg] at hj
      simp at hv ⊢
      omega
  | succ a =>
    rw [get_right_succ] at hj
    cases hg : get q a with
    | none => simp [delta,hg] at hj
    | some z =>
      rcases z with ⟨k,f⟩
      have hv := hq _ _ _ hg
      simp [delta,hg] at hj
      simp
      omega

theorem profile_valid (b : Nat) : Valid (profiles b).mid :=
  (fold_preserves Valid valid_base valid_up valid_left valid_right b).2.1

/-- A canonical prefix does not end with an entry equal to the tail. -/
def Canonical (p : Profile) : Prop := p.front.getLast? ≠ some (some (0,0))
private theorem canonical_base : Canonical base := by simp [Canonical,base]
private theorem canonical_shift (p : Profile) (h : Canonical p) (j e : Int) :
    Canonical (shift p j e) := h
private theorem canonical_pop (p : Profile) (h : Canonical p) : Canonical (pop p) := by
  unfold Canonical pop
  simp only [List.getLast?_tail]
  split
  · simp
  · exact h
private theorem canonical_push (p : Profile) (h : Canonical p) (v : Outcome) : Canonical (push v p) := by
  unfold push
  split
  · exact h
  · rename_i hn
    unfold Canonical
    by_cases he : p.front=[]
    · simp [he] at hn
      simp [he,hn]
    · have hs : p.front.getLast? ≠ none := by
        intro hz
        exact he (List.getLast?_eq_none_iff.mp hz)
      cases hg : p.front.getLast? with
      | none => exact False.elim (hs hg)
      | some x =>
        simp only [List.getLast?_cons,hg,Option.getD_some]
        unfold Canonical at h
        rw [hg] at h
        exact h
private theorem canonical_up (p : Profile) (h : Canonical p) : Canonical (up p) :=
  canonical_shift _ (canonical_pop p h) _ _
private theorem canonical_left (p : Profile) (h : Canonical p) : Canonical (left p) :=
  canonical_push _ (canonical_shift p h _ _) _
private theorem canonical_right (p q : Profile) (_ : Canonical p) (h : Canonical q) : Canonical (right p q) :=
  canonical_push _ (canonical_shift q h _ _) _

theorem profile_canonical (b : Nat) : Canonical (profiles b).mid :=
  (fold_preserves Canonical canonical_base canonical_up canonical_left canonical_right b).2.1

private theorem raw_tail_iff (p : Profile) (a : Nat) :
    get p a = some p.tail ↔ p.front.getD a (some (0,0)) = some (0,0) := by
  unfold get
  cases hg : p.front.getD a (some (0,0)) with
  | none => simp [delta]
  | some z =>
    rcases z with ⟨j,e⟩
    rcases ht : p.tail with ⟨k,f⟩
    simp [delta] <;> omega

theorem get_tail_of_length (p : Profile) (a : Nat) (ha : p.front.length ≤ a) : get p a = some p.tail := by
  apply (raw_tail_iff p a).2
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none ha,Option.getD_none]

/-- The last exception of a nonempty canonical profile genuinely differs
from the affine tail. -/
theorem last_diff (p : Profile) (hc : Canonical p) (hp : 0<p.front.length) :
    get p (p.front.length-1) ≠ some p.tail := by
  intro he
  have h := (raw_tail_iff p _).1 he
  simp only [List.getD_eq_getElem?_getD] at h
  have hi : p.front.length-1<p.front.length := by omega
  rw [List.getElem?_eq_getElem hi,Option.getD_some] at h
  apply hc
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem hi,h]

/-- Exact normalized drift and excess, recovered from a successful output. -/
theorem normalized_exact (B : Drain) (h : Laws B) (a b d x y : Nat)
    (hb : B a b d = some (x,y)) :
    get (profiles b).mid a = some ((x : Int)-(a : Int),(y : Int)-((d+3*b : Nat) : Int)) := by
  rw [drain_exact B h] at hb
  cases hg : get (profiles b).mid a with
  | none => simp [hg,render] at hb
  | some z =>
    rcases z with ⟨j,e⟩
    have hv := profile_valid b a j e hg
    simp [hg,render] at hb
    obtain ⟨hx,hy⟩ := hb
    have hny : 0≤((d+3*b : Nat) : Int)+e := by omega
    have hx' := Int.toNat_of_nonneg hv.1
    have hy' := Int.toNat_of_nonneg hny
    rw [hx] at hx'
    have hy0 : (((d+3*b : Nat) : Int)+e).toNat=y := by simpa using hy
    rw [hy0] at hy'
    congr 1
    exact Prod.ext (by omega) (by omega)

/-- Existence of an exact affine output formula on every a≥k, for all d. -/
def AffineFrom (B : Drain) (b k : Nat) : Prop :=
  ∃ j e : Int, ∀ a d, k≤a → ∃ x y : Nat,
    B a b d = some (x,y) ∧ (x : Int)=(a : Int)+j ∧
      (y : Int)=((d+3*b : Nat) : Int)+e

/-- The computed canonical prefix length is the SHARP affine threshold
for each individual block count, not just a uniform sufficient budget. -/
theorem sharp_affine_threshold (B : Drain) (h : Laws B) (b k : Nat) :
    AffineFrom B b k ↔ (profiles b).mid.front.length≤k := by
  let p := (profiles b).mid
  constructor
  · rintro ⟨j,e,ha⟩
    obtain ⟨x,y,hxy,hx,hy⟩ := ha (k+p.front.length) 0 (by omega)
    have hn := normalized_exact B h _ _ _ _ _ hxy
    have ht := get_tail_of_length p (k+p.front.length) (by omega)
    have hn' : get p (k+p.front.length) = some (j,e) := by
      rw [hn,hx,hy]
      congr 1
      exact Prod.ext (by omega) (by omega)
    have hj : (j,e)=p.tail := Option.some.inj (hn'.symm.trans ht)
    change p.front.length≤k
    by_cases hk : p.front.length≤k
    · exact hk
    · have hp : 0<p.front.length := by omega
      obtain ⟨u,v,huv,hu,hv⟩ := ha (p.front.length-1) 0 (by omega)
      have hnu := normalized_exact B h _ _ _ _ _ huv
      have hnu' : get p (p.front.length-1) = some (j,e) := by
        rw [hnu,hu,hv]
        congr 1
        exact Prod.ext (by omega) (by omega)
      rw [hj] at hnu'
      exact False.elim (last_diff p (profile_canonical b) hp hnu')
  · intro hk
    change p.front.length≤k at hk
    refine ⟨p.tail.1,p.tail.2,?_⟩
    intro a d ha
    have ht := get_tail_of_length p a (by omega)
    have hv := profile_valid b a p.tail.1 p.tail.2 (by simpa using ht)
    have he : 0≤((d+3*b : Nat) : Int)+p.tail.2 := by omega
    refine ⟨((a : Int)+p.tail.1).toNat,(((d+3*b : Nat) : Int)+p.tail.2).toNat,?_,Int.toNat_of_nonneg hv.1,Int.toNat_of_nonneg he⟩
    rw [drain_exact B h,ht]
    rfl

private theorem length_push (p : Profile) (v : Outcome) :
    (push v p).front.length ≤ p.front.length+1 := by
  unfold push
  split <;> simp
private theorem length_up (p : Profile) : (up p).front.length ≤ p.front.length := by
  simp [up,shift,pop]
private theorem length_left (p : Profile) : (left p).front.length ≤ p.front.length+1 :=
  length_push (shift p (-1) 4) none
private theorem length_right (p q : Profile) : (right p q).front.length ≤ q.front.length+1 :=
  length_push (shift q (-1) 2) _

/-- At most n+1 exceptional entries per register for a block count b<3^n. -/
theorem profiles_length (n b : Nat) (hb : b<3^n) :
    (profiles b).lo.front.length≤n+1 ∧
    (profiles b).mid.front.length≤n+1 ∧
    (profiles b).hi.front.length≤n+1 := by
  induction n generalizing b with
  | zero =>
    have hz : b=0 := by simpa using hb
    subst b
    rw [profiles]
    simp only [if_true,seed]
    have hl := length_left base
    simp [base] at hl ⊢
    exact hl
  | succ n ih =>
    rw [profiles]
    by_cases hz : b=0
    · simp only [hz,if_true,seed]
      have hl := length_left base
      simp [base] at hl ⊢
      omega
    · simp only [if_neg hz]
      rw [Nat.pow_succ] at hb
      obtain ⟨ha,hb,hc⟩ := ih (b/3) (by omega)
      have hem : (if b/3 == 0 then base else right (profiles (b/3)).lo (profiles (b/3)).mid).front.length ≤ n+2 := by
        split
        · simp [base]
        · have h := length_right (profiles (b/3)).lo (profiles (b/3)).mid
          omega
      have he0 : (if b/3 == 0 then base else up (profiles (b/3)).lo).front.length ≤ n+2 := by
        split
        · simp [base]
        · have h := length_up (profiles (b/3)).lo
          omega
      have he1 := length_left (profiles (b/3)).mid
      have he2 := length_right (profiles (b/3)).mid (profiles (b/3)).hi
      have hep := length_up (profiles (b/3)).mid
      by_cases h0 : b%3=0
      · simp only [step,if_pos h0]
        omega
      · by_cases h1 : b%3=1
        · simp only [step,if_neg h0,if_pos h1]
          omega
        · simp only [step,if_neg h0,if_neg h1]
          omega

#print axioms sharp_affine_threshold
#print axioms profiles_length

#print axioms profiles_correct
#print axioms drain_exact
#print axioms tail_exact
end BB6.Agent41DrainProfiles
