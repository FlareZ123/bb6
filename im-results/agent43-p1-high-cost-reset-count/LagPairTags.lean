import LagPairSource
namespace BB6.Agent43LagPair
open BB6.Agent45.DelayedCarry
open BB6.Agent43PackedRecover

theorem first_or_last {n P q a k c z : Nat}
    (hw : FixedWalk n P q a k c) (he : Edge n P (q+k) c z) :
    ∃ b, Edge n P q a b := by
  cases hw with
  | nil q a ha => exact ⟨z,by simpa using he⟩
  | cons q a b k c hh tail => exact ⟨b,hh⟩

/-- A genuine fixed-target prefix plus the next edge determines the exact
scaled reverse trail from its midpoint to its original parent. -/
theorem exact_trail (n P r d a c z : Nat) (hd : d<r)
    (hw : FixedWalk n P (2*(r-d)) a (2*d) c)
    (he : Edge n P (2*r) c z) :
    trail n P r (c/2) d=some (a/2) := by
  induction d generalizing a with
  | zero =>
    simp only [Nat.mul_zero] at hw
    cases hw
    rfl
  | succ d ih =>
    let q := r-(d+1)
    have hq : q+1=r-d := by dsimp [q]; omega
    change FixedWalk n P (2*q) a (2*(d+1)) c at hw
    rw [show 2*(d+1)=2*d+1+1 by omega] at hw
    cases hw with
    | cons _ _ b _ _ h1 tail =>
      cases tail with
      | cons _ _ e _ _ h2 tail' =>
        have ht : FixedWalk n P (2*(r-d)) e (2*d) c := by
          simpa [show 2*q+1+1=2*(r-d) by omega] using tail'
        have he' : Edge n P (2*(r-d)+2*d) c z := by
          simpa [show 2*(r-d)+2*d=2*r by omega] using he
        obtain ⟨v,h3⟩ := first_or_last ht he'
        have h3' : Edge n P (2*q+2) e v := by
          simpa [show 2*q+2=2*(r-d) by omega] using h3
        obtain ⟨ha,hc,hu,hp⟩ := pair_parent n P q a b e v h1 h2 h3'
        have htr := ih (by omega) e ht
        simp only [trail,htr]
        change pred q (shift n P q) (e/2)=some (a/2)
        simp [pred,hu,hp]

/-- Concatenate independent arithmetic reverse chunks. -/
theorem trail_add (n P r a d k : Nat) (hd : d+k≤r) :
    trail n P r a (d+k) =
      (trail n P r a d).bind (fun b=>trail n P (r-d) b k) := by
  induction k with
  | zero =>
    cases h : trail n P r a d <;> simp [trail,h]
  | succ k ih =>
    rw [Nat.add_succ,trail,ih (by omega)]
    cases h : trail n P r a d with
    | none => rfl
    | some b =>
      simp only [Option.bind_some,trail]
      have hr : r-(d+(k+1))=r-d-(k+1) := by omega
      rw [hr]

/-- Tagged candidates preserve the midpoint identity through merges.
This allows rejection by small carry computations, not recovery of a long word. -/
def TagCover (n P R r : Nat) (xs : List Nat) (ys : List (Nat × Nat)) :=
  ∀ i∈xs, ∀ b, trail n P R i (R-r)=some b → (i,b)∈ys

theorem tag_start (n P R : Nat) (xs : List Nat) :
    TagCover n P R R xs (xs.map fun x=>(x,x)) := by
  intro i hi b hb
  simp [trail] at hb
  subst b
  exact List.mem_map.mpr ⟨i,hi,rfl⟩

def tagCheck (n P r d : Nat) (xs ys : List (Nat × Nat)) : Bool :=
  xs.all fun p=>match trail n P r p.2 d with
    | none => true
    | some b => ys.contains (p.1,b)

theorem tag_extend (n P R r d : Nat) (xs : List Nat) (ps qs : List (Nat × Nat))
    (hr : r≤R) (hd : d≤r)
    (hc : TagCover n P R r xs ps) (hcheck : tagCheck n P r d ps qs=true) :
    TagCover n P R (r-d) xs qs := by
  intro i hi b hb
  rw [show R-(r-d)=R-r+d by omega,trail_add n P R i (R-r) d (by omega),
    show R-(R-r)=r by omega] at hb
  cases h : trail n P R i (R-r) with
  | none => simp [h] at hb
  | some a =>
    have hm := hc i hi a h
    unfold tagCheck at hcheck
    have hs := List.all_eq_true.mp hcheck (i,a) hm
    simp only [h,Option.bind_some] at hb
    simpa [hb,List.contains_eq_mem] using hs

def survivors (n P R a : Nat) (tags : List (Nat × Nat)) : List Nat :=
  (tags.filter fun p=>p.2==a/2).map fun p=>2*p.1+digit n P (2*R)

theorem tagged_midpoint (n s h B a C c D d R r : Nat) (xs : List Nat)
    (tags : List (Nat × Nat))
    (hclock : n+s+h+3=2*R) (hstart : n+s+3=2*r) (hr : r≤R)
    (hh : h<n)
    (hl : Live n (7*B) (2*n+s+3) R (·∈xs))
    (hc : TagCover n (7*B) R r xs tags)
    (ht : Trace n s B a) (hp : Extend n s B a h C c)
    (hs : Extend n (s+h) C c (n-h) D d) :
    c∈survivors n (7*B) R a tags := by
  have hw := fixed_suffix n s B a h C c (n-h) D d ht hp hs (by omega)
  rw [hclock,show n-h=(n-h-1)+1 by omega] at hw
  obtain ⟨e,he⟩ := fixed_first hw
  have hcpar := (even_half n (7*B) R c e he).1
  have hx : c/2∈xs := by
    apply hl c d
    simpa [show 2*n+s+3-2*R=(n-h-1)+1 by omega] using hw
  have hwpre := fixed_suffix n s B a 0 B a h C c ht Extend.nil (by simpa using hp) (by omega)
  have hwpre' : FixedWalk n (7*B) (2*(R-(R-r))) a (2*(R-r)) c := by
    simpa [show R-(R-r)=r by omega,show 2*(R-r)=h by omega,hstart] using hwpre
  have htrail := exact_trail n (7*B) R (R-r) a c e (by omega) hwpre' he
  have hmem := hc (c/2) hx (a/2) htrail
  unfold survivors
  apply List.mem_map.mpr
  exact ⟨(c/2,a/2),by simp [hmem],hcpar.symm⟩

theorem parent_advance_tagged (n s h B a C c R r : Nat) (xs : List Nat)
    (tags : List (Nat × Nat)) (qs : List Prefix)
    (hclock : n+s+h+3=2*R) (hstart : n+s+3=2*r) (hr : r≤R)
    (hh : h<n)
    (hl : Live n (7*B) (2*n+s+3) R (·∈xs))
    (hcover : TagCover n (7*B) R r xs tags)
    (hout : ∀ p∈recoverList n s h B a (survivors n (7*B) R a tags), p∈qs)
    (ht : Trace n s B a) (hc : C%4=1) (he : Extend n s B a h C c)
    (hsuf : ∃ D d, Extend n (s+h) C c (n-h) D d) :
    (C,c)∈qs := by
  obtain ⟨D,d,hsuf⟩ := hsuf
  exact hout _ (recover_sound n s h B a C c _ ht he (by omega)
    (tagged_midpoint n s h B a C c D d R r xs tags hclock hstart hr hh hl hcover ht he hsuf) hc)

#print axioms exact_trail
#print axioms tag_extend
#print axioms parent_advance_tagged
end BB6.Agent43LagPair
