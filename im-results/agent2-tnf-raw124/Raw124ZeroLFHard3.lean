import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFHard3
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def p3 : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), none,
    some (some ⟨true,true,2⟩), some (some ⟨true,true,0⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,4⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨false,true,1⟩), some (some ⟨true,false,5⟩),
    some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)] :
    List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

private def ones (n : Nat) : List Bool := List.replicate n true
private def zeros (n : Nat) : List Bool := List.replicate n false
private def gap (n : Nat) (x : List Bool) : List Bool := zeros n ++ true::true::x
private def e (n : Nat) (x : List Bool) : List Bool := gap (4*n+2) x
private def o (n : Nat) (x : List Bool) : List Bool := gap (4*n+3) x
private def j (n : Nat) (x : List Bool) : List Bool := gap (4*n+5) x
private def f (l r : List Bool) : HZ := ⟨5,false::l,r⟩
private def rootSec (r : List Bool) : HZ := ⟨5,[],r⟩
private def u (l x : List Bool) : HZ := f l (false::true::x)
private def v (l x : List Bool) : HZ := f l (true::x)

/-- Every even gap has an immediately following odd gap; final gaps are odd. -/
private inductive G : List Bool → Prop where
  | nil : G []
  | odd (n : Nat) {x} : G x → G (o n x)
  | evenOdd (m n : Nat) {x} : G x → G (e m (o n x))
private inductive Odd : List Bool → Prop where
  | mk (n : Nat) {x} : G x → Odd (o n x)
private theorem oddG {x} (h : Odd x) : G x := by
  cases h with | mk n h => exact .odd n h
private theorem evenG (m : Nat) {x} (h : Odd x) : G (e m x) := by
  cases h with | mk n h => exact .evenOdd m n h

/-- An inactive frame has received the two ones deposited by its child. -/
private inductive Inactive : List Bool → Prop where
  | root (n : Nat) : Inactive (ones (4*n+4))
  | single (n : Nat) {l} : Inactive l → Inactive (ones (4*n+4)++false::l)
  | double (n : Nat) {l} : Inactive l → Inactive (ones (4*n+3)++false::false::l)
private inductive Active : List Bool → Prop where
  | root (n : Nat) : Active (ones (4*n+2))
  | single (n : Nat) {l} : Inactive l → Active (ones (4*n+2)++false::l)
  | double (n : Nat) {l} : Inactive l → Active (ones (4*n+1)++false::false::l)
private theorem deactivate {l} (h : Active l) : Inactive (true::true::l) := by
  cases h with
  | root n => exact .root n
  | single n h => exact .single n h
  | double n h => exact .double n h
private theorem activate {l} (h : Inactive l) : Active (true::true::l) := by
  cases h with
  | root n =>
    have he : true::true::ones (4*n+4) = ones (4*(n+1)+2) := by rw [show 4*(n+1)+2=4*n+6 by omega]; rfl
    rw [he]; exact .root (n+1)
  | @single n l h =>
    have he : true::true::(ones (4*n+4)++false::l) = ones (4*(n+1)+2)++false::l := by rw [show 4*(n+1)+2=4*n+6 by omega]; rfl
    rw [he]; exact .single (n+1) h
  | @double n l h =>
    have he : true::true::(ones (4*n+3)++false::false::l) = ones (4*(n+1)+1)++false::false::l := by rw [show 4*(n+1)+1=4*n+5 by omega]; rfl
    rw [he]; exact .double (n+1) h

private inductive Live : HZ → Prop where
  | root (n : Nat) {x} : G x → Live (rootSec (e n x))
  | ready {l x} : Inactive l → G x → Live (f l (e 0 x))
  | back (n : Nat) {l x} : Inactive l → G x → Live (f l (e (n+1) x))
  | extra (n : Nat) {l x} : Inactive l → Odd x → Live (f (false::l) (j n x))
  | scan {l x} : Active l → G x → Live (u l x)
  | scanSingle (n : Nat) {l x} : Inactive l → G x → Live (v (ones (4*n+2)++false::l) x)
  | scanDouble (n : Nat) {l x} : Inactive l → Odd x → Live (v (ones (4*n+1)++false::false::l) x)

private theorem sweep (n : Nat) (l r : List Bool) :
    hrun p3 n ⟨5,ones n++l,r⟩ = some ⟨5,l,zeros n++r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun p3 1 ⟨5,ones (n+1)++l,r⟩ = some ⟨5,ones n++l,false::r⟩ := by rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1)++r = zeros n++false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh

private theorem gapConcat (n m : Nat) (x : List Bool) : zeros n++gap m x = gap (n+m) x := by
  simp only [gap,zeros,← List.append_assoc,List.replicate_append_replicate]

-- Each fixed macro below follows by definitional reduction of the original transition table.
private theorem rootEnter (x : List Bool) : hrun p3 6 (rootSec (e 0 x)) = some (u (ones 2) x) := by rfl
private theorem readyEnter (l x : List Bool) : hrun p3 6 (f l (e 0 x)) = some (u (true::true::l) x) := by rfl
private theorem rootInsert (n : Nat) (x : List Bool) : hrun p3 9 (rootSec (e (n+1) x)) = some (rootSec (e 0 (o n x))) := by
  unfold rootSec e o gap zeros
  rw [show 4*(n+1)+2=(4*n+3)+3 by omega]
  rfl
private theorem insert (l x : List Bool) : hrun p3 9 (f l (false::false::false::x)) = some ⟨5,l,false::false::true::true::x⟩ := by rfl
private theorem insertEven (n : Nat) (l x : List Bool) :
    hrun p3 9 (f l (e (n+1) x)) = some ⟨5,l,e 0 (o n x)⟩ := by
  unfold e o gap zeros
  rw [show 4*(n+1)+2=(4*n+3)+3 by omega]
  rfl
private theorem insertExtra (n : Nat) (l x : List Bool) :
    hrun p3 9 (f (false::l) (j n x)) = some (f l (e 0 (e n x))) := by
  unfold j e gap zeros
  rw [show 4*n+5=(4*n+2)+3 by omega]
  rfl

private theorem uEven (l x : List Bool) : hrun p3 7 (u l (e 0 x)) = some (v (true::false::false::true::true::l) x) := by rfl
private theorem uOdd (l x : List Bool) : hrun p3 9 (u l (o 0 x)) = some (u (true::false::false::true::true::l) x) := by rfl
private theorem uLarge (l x : List Bool) : hrun p3 15 (u l (false::false::false::false::x)) = some (v (true::true::false::true::true::l) x) := by rfl
private theorem uEmpty (l : List Bool) : hrun p3 15 (u l []) = some (v (true::true::false::true::true::l) []) := by rfl
private theorem vEven (l x : List Bool) : hrun p3 6 (v l (e 0 x)) = some (v (ones 4++l) x) := by rfl
private theorem vOdd (l x : List Bool) : hrun p3 8 (v l (o 0 x)) = some (u (ones 4++l) x) := by rfl
private theorem vLarge (l x : List Bool) : hrun p3 13 (v l (false::false::false::false::x)) = some ⟨5,l,gap 4 x⟩ := by rfl
private theorem vEmpty (l : List Bool) : hrun p3 13 (v l []) = some ⟨5,l,gap 4 []⟩ := by rfl

private theorem eShift (n : Nat) (x : List Bool) : e (n+1) x = false::false::false::false::e n x := by
  unfold e gap zeros
  rw [show 4*(n+1)+2=(4*n+2)+4 by omega]
  rfl
private theorem oShift (n : Nat) (x : List Bool) : o (n+1) x = false::false::false::false::o n x := by
  unfold o gap zeros
  rw [show 4*(n+1)+3=(4*n+3)+4 by omega]
  rfl


private theorem backNext {l} (hl : Inactive l) (n : Nat) {x} (hx : G x) :
    ∃ t y, 0<t ∧ Live y ∧ hrun p3 t (f l (e (n+1) x)) = some y := by
  cases hl with
  | root m =>
    have hs := sweep (4*m+4) [] (e 0 (o n x))
    rw [List.append_nil] at hs
    have hh := hjoin (insertEven n (ones (4*m+4)) x) hs
    change hrun p3 _ _ = some ⟨5,[],zeros (4*m+4)++gap 2 (o n x)⟩ at hh
    rw [gapConcat,show 4*m+4+2=4*(m+1)+2 by omega] at hh
    exact ⟨9+(4*m+4),_,by omega,.root (m+1) (.odd n hx),hh⟩
  | @single m l hl =>
    have hh := hjoin (insertEven n (ones (4*m+4)++false::l) x) (sweep (4*m+4) (false::l) (e 0 (o n x)))
    change hrun p3 _ _ = some ⟨5,false::l,zeros (4*m+4)++gap 2 (o n x)⟩ at hh
    rw [gapConcat,show 4*m+4+2=4*(m+1)+2 by omega] at hh
    exact ⟨9+(4*m+4),_,by omega,.back m hl (.odd n hx),hh⟩
  | @double m l hl =>
    have hh := hjoin (insertEven n (ones (4*m+3)++false::false::l) x) (sweep (4*m+3) (false::false::l) (e 0 (o n x)))
    change hrun p3 _ _ = some ⟨5,false::false::l,zeros (4*m+3)++gap 2 (o n x)⟩ at hh
    rw [gapConcat,show 4*m+3+2=4*m+5 by omega] at hh
    exact ⟨9+(4*m+3),_,by omega,.extra m hl (.mk n hx),hh⟩
private theorem singleStop (n : Nat) {l x r} (hl : Inactive l) (hx : G x)
    (h : hrun p3 13 (v (ones (4*n+2)++false::l) r) = some ⟨5,ones (4*n+2)++false::l,gap 4 x⟩) :
    ∃ t y, 0<t ∧ Live y ∧ hrun p3 t (v (ones (4*n+2)++false::l) r) = some y := by
  have hh := hjoin h (sweep (4*n+2) (false::l) (gap 4 x))
  rw [gapConcat,show 4*n+2+4=4*(n+1)+2 by omega] at hh
  exact ⟨13+(4*n+2),_,by omega,.back n hl hx,hh⟩
private theorem doubleStop (n : Nat) {l x r} (hl : Inactive l) (hx : Odd x)
    (h : hrun p3 13 (v (ones (4*n+1)++false::false::l) r) = some ⟨5,ones (4*n+1)++false::false::l,gap 4 x⟩) :
    ∃ t y, 0<t ∧ Live y ∧ hrun p3 t (v (ones (4*n+1)++false::false::l) r) = some y := by
  have hh := hjoin h (sweep (4*n+1) (false::false::l) (gap 4 x))
  rw [gapConcat,show 4*n+1+4=4*n+5 by omega] at hh
  exact ⟨13+(4*n+1),_,by omega,.extra n hl hx,hh⟩
private theorem next {z} (h : Live z) : ∃ t y, 0<t ∧ Live y ∧ hrun p3 t z = some y := by
  cases h with
  | @root n x hx =>
    cases n with
    | zero => exact ⟨6,_,by decide,.scan (.root 0) hx,rootEnter x⟩
    | succ n => exact ⟨9,_,by decide,.root 0 (.odd n hx),rootInsert n x⟩
  | @ready l x hl hx => exact ⟨6,_,by decide,.scan (activate hl) hx,readyEnter l x⟩
  | @back n l x hl hx => exact backNext hl n hx
  | @extra n l x hl hx => exact ⟨9,_,by decide,.ready hl (evenG n hx),insertExtra n l x⟩
  | @scan l x hl hx =>
    cases hx with
    | nil => exact ⟨15,_,by decide,.scanSingle 0 (deactivate hl) .nil,uEmpty l⟩
    | @odd n x hx =>
      cases n with
      | zero => exact ⟨9,_,by decide,.scan (.double 0 (deactivate hl)) hx,uOdd l x⟩
      | succ n =>
        have hh := uLarge l (o n x)
        rw [← oShift] at hh
        exact ⟨15,_,by decide,.scanSingle 0 (deactivate hl) (.odd n hx),hh⟩
    | @evenOdd m n x hx =>
      cases m with
      | zero => exact ⟨7,_,by decide,.scanDouble 0 (deactivate hl) (.mk n hx),uEven l (o n x)⟩
      | succ m =>
        have hh := uLarge l (e m (o n x))
        rw [← eShift] at hh
        exact ⟨15,_,by decide,.scanSingle 0 (deactivate hl) (.evenOdd m n hx),hh⟩
  | @scanSingle n l x hl hx =>
    cases hx with
    | nil => exact singleStop n hl .nil (vEmpty (ones (4*n+2)++false::l))
    | @odd m x hx =>
      cases m with
      | zero =>
        have hh := vOdd (ones (4*n+2)++false::l) x
        have he : ones 4++(ones (4*n+2)++false::l) = ones (4*(n+1)+2)++false::l := by
          rw [show 4*(n+1)+2=4*n+6 by omega]; rfl
        rw [he] at hh
        exact ⟨8,_,by decide,.scan (.single (n+1) hl) hx,hh⟩
      | succ m =>
        have hh := vLarge (ones (4*n+2)++false::l) (o m x)
        rw [← oShift] at hh
        exact singleStop n hl (.odd m hx) hh
    | @evenOdd m k x hx =>
      cases m with
      | zero =>
        have hh := vEven (ones (4*n+2)++false::l) (o k x)
        have he : ones 4++(ones (4*n+2)++false::l) = ones (4*(n+1)+2)++false::l := by
          rw [show 4*(n+1)+2=4*n+6 by omega]; rfl
        rw [he] at hh
        exact ⟨6,_,by decide,.scanSingle (n+1) hl (.odd k hx),hh⟩
      | succ m =>
        have hh := vLarge (ones (4*n+2)++false::l) (e m (o k x))
        rw [← eShift] at hh
        exact singleStop n hl (.evenOdd m k hx) hh
  | @scanDouble n l x hl hx =>
    cases hx with
    | @mk m x hx =>
      cases m with
      | zero =>
        have hh := vOdd (ones (4*n+1)++false::false::l) x
        have he : ones 4++(ones (4*n+1)++false::false::l) = ones (4*(n+1)+1)++false::false::l := by
          rw [show 4*(n+1)+1=4*n+5 by omega]; rfl
        rw [he] at hh
        exact ⟨8,_,by decide,.scan (.double (n+1) hl) hx,hh⟩
      | succ m =>
        have hh := vLarge (ones (4*n+1)++false::false::l) (o m x)
        rw [← oShift] at hh
        exact doubleStop n hl (.mk m hx) hh

private theorem root : hrun p3 9 ⟨0,[],[]⟩ = some (rootSec (e 0 [])) := by rfl
private theorem arbitraryLive (n : Nat) : ∃ t, n≤t ∧ ∃ y, Live y ∧ hrun p3 t ⟨0,[],[]⟩=some y := by
  induction n with
  | zero => exact ⟨9,by decide,_,.root 0 .nil,root⟩
  | succ n ih =>
    obtain ⟨t,ht,y,hy,h⟩ := ih
    obtain ⟨s,z,hs,hz,hh⟩ := next hy
    exact ⟨t+s,by omega,z,hz,hjoin h hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

/-- The fourth hard leaf never queries A1, irrespective of its completion. -/
theorem neverHard3 (m : Machine) (hm : compatible p3 m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,y,hy,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound p3 k _ _ 0 Hk
  have H := zrun_sound p3 m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem coverHard3 (bound : Nat) : Cover (DecidedBelow bound) p3 :=
  .leaf _ (fun m hm => Or.inl (neverHard3 m hm))

#print axioms next
#print axioms neverHard3
#print axioms coverHard3
end BB6.Agent2Raw124ZeroLFHard3
