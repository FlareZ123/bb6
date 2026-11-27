import Std
namespace F421DrainPlan

/-- Far-to-near rows. Zero-P unmarked rows are retained Q-run ghosts. -/
structure Row where
  p : Nat
  q : Nat
  mark : Bool
  deriving DecidableEq, Repr

def bit (c : Row) : Nat := if c.mark then 1 else 0
def visits (h : Nat) (c : Row) : Nat := min c.p (2*h+bit c)
def terminals (h : Nat) (c : Row) : Nat := (visits h c+bit c)/2
def nextH (h : Nat) (c : Row) : Nat := h+terminals h c
def finishRow (h : Nat) (c : Row) : Row := ⟨c.p-visits h c,c.q+terminals h c,false⟩

def goodRow (h : Nat) (c : Row) : Prop :=
  2 ≤ c.q ∧ (c.mark = true → 1 ≤ c.p) ∧ (c.p ≤ 2*h+bit c → c.p%2=bit c)

def good (h : Nat) : List Row → Prop
  | [] => True
  | c::cs => goodRow h c ∧ good (nextH h c) cs

def count (h : Nat) : List Row → Nat
  | [] => h
  | c::cs => count (nextH h c) cs

def finish (h : Nat) : List Row → List Row
  | [] => []
  | c::cs => finishRow h c::finish (nextH h c) cs

def unmarked (xs : List Row) : Prop := ∀ c ∈ xs, c.mark=false

def termStep (c : Row) : Row := ⟨c.p-1,c.q+1,false⟩
def lowStep (c : Row) : Row := if c.p=0 then c else ⟨c.p-1,c.q,true⟩

theorem termPlan (h : Nat) (c : Row) (hm : c.mark=true) (hg : goodRow h c) :
    goodRow h (termStep c) ∧ nextH h c=nextH h (termStep c)+1 ∧
    finishRow h c=finishRow h (termStep c) := by
  rcases c with ⟨p,q,e⟩
  simp only at hm
  subst e
  simp only [goodRow,bit,termStep,nextH,terminals,visits,finishRow,Bool.false_eq_true,ite_true,ite_false,
    true_implies, false_implies, and_true, Row.mk.injEq] at hg ⊢
  rcases hg with ⟨hq,hp0,hpar⟩
  by_cases hcap : p ≤ 2*h+1
  · have hh : p-1 ≤ 2*h+0 := by omega
    rw [Nat.min_eq_left hcap,Nat.min_eq_left hh]
    have hp := hpar hcap
    refine ⟨⟨by omega,trivial,by intro h; omega⟩,by omega,by omega,by omega⟩
  · have hh : 2*h+0 ≤ p-1 := by omega
    rw [Nat.min_eq_right (by omega : 2*h+1≤p),Nat.min_eq_right hh]
    refine ⟨⟨by omega,trivial,by intro h; omega⟩,by omega,by omega,by omega⟩

theorem lowPlan (h : Nat) (c : Row) (hh : 1 ≤ h) (hm : c.mark=false) (hg : goodRow h c) :
    goodRow (h-1) (lowStep c) ∧ nextH h c=nextH (h-1) (lowStep c)+1 ∧
    finishRow h c=finishRow (h-1) (lowStep c) ∧ (c.p=0 ∨ 2≤c.p) := by
  rcases c with ⟨p,q,e⟩
  simp only at hm
  subst e
  by_cases hp : p=0
  · subst p
    simp [lowStep,goodRow,bit,nextH,terminals,visits,finishRow] at hg ⊢
    omega
  · simp only [lowStep,hp,ite_false,goodRow,bit,nextH,terminals,visits,finishRow,Bool.false_eq_true,ite_true,
      true_implies,false_implies,and_true,Row.mk.injEq] at hg ⊢
    omega

theorem lowPlans (xs : List Row) (h : Nat) (hh : 1≤h) (hm : unmarked xs) (hg : good h xs) :
    good (h-1) (xs.map lowStep) ∧ count h xs = count (h-1) (xs.map lowStep)+1 ∧
    finish h xs=finish (h-1) (xs.map lowStep) ∧ ∀ c ∈ xs, c.p=0 ∨ 2≤c.p := by
  induction xs generalizing h with
  | nil => simp [good,count,finish]; omega
  | cons c cs ih =>
    rcases hg with ⟨hcg,hg⟩
    have hmc := hm c (by simp)
    have hms : unmarked cs := by intro x hx; exact hm x (by simp [hx])
    obtain ⟨hc,hH,hF,hp⟩ := lowPlan h c hh hmc hcg
    have hpos : 1≤nextH h c := by unfold nextH; omega
    obtain ⟨hgs,hcount,hfinish,hps⟩ := ih (nextH h c) hpos hms hg
    have hnext : nextH h c-1=nextH (h-1) (lowStep c) := by omega
    rw [hnext] at hgs hcount hfinish
    simp only [List.map_cons,good,count,finish]
    exact ⟨⟨hc,hgs⟩,hcount,by rw [hF,hfinish],by intro x hx; rcases List.mem_cons.mp hx with rfl|hx; exact hp; exact hps x hx⟩

theorem countAppend (xs ys : List Row) (h : Nat) : count h (xs++ys)=count (count h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons c cs ih => simp [count,ih]

theorem finishAppend (xs ys : List Row) (h : Nat) : finish h (xs++ys)=finish h xs++finish (count h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons c cs ih => simp [finish,count,ih]

theorem goodAppend (xs ys : List Row) (h : Nat) : good h (xs++ys) ↔ good h xs ∧ good (count h xs) ys := by
  induction xs generalizing h with
  | nil => simp [good,count]
  | cons c cs ih => simp [good,count,ih, and_assoc]

theorem qGood (h : Nat) (xs : List Row) (hg : good h xs) (x : Row) (hx : x ∈ xs) : 2≤x.q := by
  induction xs generalizing h with
  | nil => simp at hx
  | cons c cs ih =>
    rcases hg with ⟨hc,ht⟩
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hc.1
    · exact ih (nextH h c) ht hx

theorem splitPlan (fs ns : List Row) (c : Row) (h : Nat) (hm : c.mark=true)
    (hn : unmarked ns) (hg : good h (fs++c::ns)) :
    let xs := fs++c::ns
    let ys := fs++termStep c::ns.map lowStep
    good h ys ∧ count h xs=count h ys+1 ∧ finish h xs=finish h ys ∧
    (1≤c.p ∧ 2≤c.q) ∧ ∀ x ∈ ns, (x.p=0 ∨ 2≤x.p) ∧ 2≤x.q := by
  let H := count h fs
  obtain ⟨hfs,hc,hns⟩ := (goodAppend fs (c::ns) h).mp hg
  obtain ⟨hc',hH,hF⟩ := termPlan H c hm hc
  have hpos : 1≤nextH H c := by omega
  obtain ⟨hn',hcount,hfinish,hp⟩ := lowPlans ns (nextH H c) hpos hn hns
  have he : nextH H c-1=nextH H (termStep c) := by omega
  rw [he] at hn' hcount hfinish
  simp only [countAppend,finishAppend, count,finish]
  refine ⟨(goodAppend fs _ h).mpr ⟨hfs,hc',hn'⟩,hcount,by rw [hF,hfinish],⟨hc.2.1 hm,hc.1⟩,?_⟩
  exact fun x hx => ⟨hp x hx,qGood _ _ hns x hx⟩

theorem splitMarked (xs : List Row) : unmarked xs ∨ ∃ fs c ns, xs=fs++c::ns ∧ c.mark=true ∧ unmarked ns := by
  induction xs with
  | nil => exact Or.inl (by simp [unmarked])
  | cons c cs ih =>
    rcases ih with h|⟨fs,d,ns,he,hm,hn⟩
    · cases hc : c.mark
      · exact Or.inl (by intro x hx; rcases List.mem_cons.mp hx with rfl|hx; exact hc; exact h x hx)
      · exact Or.inr ⟨[],c,cs,rfl,hc,h⟩
    · exact Or.inr ⟨c::fs,d,ns,by simp [he],hm,hn⟩

theorem unmarkedPlan (xs : List Row) (hm : unmarked xs) : count 0 xs=0 ∧ finish 0 xs=xs := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih =>
    have hc := hm c (by simp)
    have hs : unmarked cs := by intro x hx; exact hm x (by simp [hx])
    have h := ih hs
    rcases c with ⟨p,q,e⟩
    simp only at hc
    subst e
    simp [count,nextH,terminals,visits,bit,finish,finishRow,h]

#print axioms splitPlan
end F421DrainPlan
