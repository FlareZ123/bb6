import CarryMacro
namespace BB6CarrySweep
open BB6BlockFAR
open BB6Carry hiding render
abbrev render := BB6Carry.render

structure Ret where
  l : List Bool
  r : Ray

def Ret.render (x : Ret) : Prim := BB6Carry.render .B x.l x.r

/-- In the C phase the right ray starts with 10. Sweep the remaining
nearest-first 10 left blocks, then turn at 01 or at the blank end. -/
def cSweep : List Bool → Ray → Nat × Ret
  | [], r => (3,⟨[false],r⟩)
  | false::l,r => (3,⟨false::false::l,r⟩)
  | true::l,r => let t := cSweep l (bits [true,false] r); (2+t.1,t.2)

theorem cSweep_sound (slow : Bool) (l : List Bool) (r : Ray) :
    let t := cSweep l r
    0 < t.1 ∧ run (machine slow) t.1 (render .C l (bits [true,false] r)) = some t.2.render := by
  induction l generalizing r with
  | nil => exact ⟨by simp [cSweep],Cnil slow r⟩
  | cons a l ih =>
    cases a with
    | false => exact ⟨by simp [cSweep],C01 slow l r⟩
    | true =>
      obtain ⟨hp,hr⟩ := ih (bits [true,false] r)
      change 0 < 2 + (cSweep l (bits [true,false] r)).1 ∧
        run (machine slow) (2 + (cSweep l (bits [true,false] r)).1) _ = _
      refine ⟨by omega,?_⟩
      rw [run_add,C10]
      exact hr

/-- At entry F the right ray starts with zero. Sweep the 01 blocks,
then use C for the contiguous 10 blocks. The blank-end case shifts
alignment by one cell, so the result is again in B at a paired boundary. -/
def fSweep (slow : Bool) : List Bool → Ray → Nat × Ret
  | [],r => (4,⟨[false],r⟩)
  | false::l,r => let t := fSweep slow l (cons true (cons false r)); (2+t.1,t.2)
  | true::l,r => let t := cSweep l (cons false r); ((if slow then 6 else 2)+t.1,t.2)

theorem fSweep_sound (slow : Bool) (l : List Bool) (r : Ray) :
    let t := fSweep slow l r
    0 < t.1 ∧ run (machine slow) t.1 (render .F l (cons false r)) = some t.2.render := by
  induction l generalizing r with
  | nil => exact ⟨by simp [fSweep],Fnil slow r⟩
  | cons a l ih =>
    cases a with
    | false =>
      obtain ⟨hp,hr⟩ := ih (cons true (cons false r))
      change 0 < 2+(fSweep slow l (cons true (cons false r))).1 ∧
        run (machine slow) (2+(fSweep slow l (cons true (cons false r))).1) _ = _
      refine ⟨by omega,?_⟩
      rw [run_add,F01]
      exact hr
    | true =>
      obtain ⟨hp,hr⟩ := cSweep_sound slow l (cons false r)
      change 0 < (if slow then 6 else 2)+(cSweep l (cons false r)).1 ∧
        run (machine slow) ((if slow then 6 else 2)+(cSweep l (cons false r)).1) _ = _
      refine ⟨by cases slow <;> omega,?_⟩
      rw [run_add,F10]
      exact hr

inductive Pair where | A | B | C | D
  deriving DecidableEq, Repr

def Pair.bits : Pair → List Bool
  | .A => [true,false]
  | .B => [false,true]
  | .C => [false,false]
  | .D => [true,true]

def ray : List Pair → Ray
  | [] => blankRay
  | a::r => bits a.bits (ray r)

/-- Finite right words have implicit blank pairs. Every ordinary scan
consumes one A or CA token; D at the scan point is the sole failure. -/
def bSweep (slow : Bool) : List Pair → List Bool → Option (Nat × Ret)
  | [],l => let t := fSweep slow l (bits [false,true] blankRay); some (7+t.1,t.2)
  | .A::r,l => (bSweep slow r (true::l)).map fun t => (2+t.1,t.2)
  | .B::r,l => let t := fSweep slow l (cons false (ray r)); some ((if slow then 7 else 3)+t.1,t.2)
  | .C::[],l => let t := fSweep slow l (bits [false,true] blankRay); some (7+t.1,t.2)
  | .C::.A::r,l => (bSweep slow r (false::false::l)).map fun t => (4+t.1,t.2)
  | .C::.B::r,l => let t := fSweep slow l (bits [false,true,true] (ray r)); some (7+t.1,t.2)
  | .C::.C::r,l => let t := fSweep slow l (bits [false,true,false] (ray r)); some (7+t.1,t.2)
  | .C::.D::r,l => let t := fSweep slow l (bits [true,false,false] (ray r)); some (7+t.1,t.2)
  | .D::_,_ => none

private theorem blank3 : bits [false,false,false] blankRay = blankRay := by
  simp [bits,blank_cons]
private theorem rayCnil : ray [.C] = blankRay := by simp [ray,Pair.bits,bits,blank_cons]

private theorem join (slow : Bool) {n k : Nat} {x y z : Prim}
    (hn : run (machine slow) n x = some y) (hk : run (machine slow) k y = some z) :
    run (machine slow) (n+k) x = some z := by rw [run_add,hn]; exact hk

private theorem twoStep {α : Type} {P : List α → Prop}
    (nil : P []) (singleton : ∀ a, P [a])
    (cons_cons : ∀ a b r, P r → P (b::r) → P (a::b::r)) :
    ∀ w, P w
  | [] => nil
  | [a] => singleton a
  | a::b::r => cons_cons a b r (twoStep nil singleton cons_cons r)
      (twoStep nil singleton cons_cons (b::r))

theorem bSweep_sound (slow : Bool) (w : List Pair) (l : List Bool) (t : Nat × Ret)
    (h : bSweep slow w l = some t) :
    0 < t.1 ∧ run (machine slow) t.1 (render .B l (ray w)) = some t.2.render := by
  induction w using twoStep generalizing l t with
  | nil =>
    simp only [bSweep,Option.some.injEq] at h
    subst t
    have hf := fSweep_sound slow l (bits [false,true] blankRay)
    refine ⟨by omega,?_⟩
    have hb := B000 slow l blankRay
    rw [blank3] at hb
    exact join slow hb hf.2
  | singleton a =>
    cases a with
    | A =>
      simp only [bSweep,Option.map_eq_some_iff] at h
      obtain ⟨u,hu,rfl⟩ := h
      -- one remaining blank-turn macro
      simp only [bSweep,Option.some.injEq] at hu
      subst u
      have hf := fSweep_sound slow (true::l) (bits [false,true] blankRay)
      have hb := B000 slow (true::l) blankRay
      rw [blank3] at hb
      refine ⟨by omega,?_⟩
      exact join slow (B10 slow l blankRay) (join slow hb hf.2)
    | B =>
      simp only [bSweep,Option.some.injEq] at h
      subst t
      have hf := fSweep_sound slow l (cons false blankRay)
      refine ⟨by cases slow <;> simp [ray] <;> omega,?_⟩
      exact join slow (B01 slow l blankRay) hf.2
    | C =>
      simp only [bSweep,Option.some.injEq] at h
      subst t
      have hf := fSweep_sound slow l (bits [false,true] blankRay)
      have hb := B000 slow l blankRay
      rw [blank3] at hb
      refine ⟨by omega,?_⟩
      rw [rayCnil]
      exact join slow hb hf.2
    | D => simp [bSweep] at h
  | cons_cons a b r ih1 ih2 =>
    cases a with
    | A =>
      simp only [bSweep,Option.map_eq_some_iff] at h
      obtain ⟨u,hu,rfl⟩ := h
      obtain ⟨hp,hr⟩ := ih2 (true::l) u hu
      exact ⟨by omega,join slow (B10 slow l (ray (b::r))) hr⟩
    | B =>
      simp only [bSweep,Option.some.injEq] at h
      subst t
      have hf := fSweep_sound slow l (cons false (ray (b::r)))
      exact ⟨by cases slow <;> omega,join slow (B01 slow l (ray (b::r))) hf.2⟩
    | C =>
      cases b with
      | A =>
        simp only [bSweep,Option.map_eq_some_iff] at h
        obtain ⟨u,hu,rfl⟩ := h
        obtain ⟨hp,hr⟩ := ih1 (false::false::l) u hu
        exact ⟨by omega,join slow (B0010 slow l (ray r)) hr⟩
      | B =>
        simp only [bSweep,Option.some.injEq] at h
        subst t
        have hf := fSweep_sound slow l (bits [false,true,true] (ray r))
        exact ⟨by omega,join slow (B000 slow l (cons true (ray r))) hf.2⟩
      | C =>
        simp only [bSweep,Option.some.injEq] at h
        subst t
        have hf := fSweep_sound slow l (bits [false,true,false] (ray r))
        exact ⟨by omega,join slow (B000 slow l (cons false (ray r))) hf.2⟩
      | D =>
        simp only [bSweep,Option.some.injEq] at h
        subst t
        have hf := fSweep_sound slow l (bits [true,false,false] (ray r))
        exact ⟨by omega,join slow (B0011 slow l (ray r)) hf.2⟩
    | D => simp [bSweep] at h

/-- The scan has a complete local failure predicate: D is fatal exactly
when it is the next unconsumed pair. -/
def scanSafe : List Pair → Bool
  | .A::r => scanSafe r
  | .C::.A::r => scanSafe r
  | .D::_ => false
  | _ => true

theorem bSweep_isSome (slow : Bool) (w : List Pair) (l : List Bool) :
    (bSweep slow w l).isSome = scanSafe w := by
  induction w using twoStep generalizing l with
  | nil => rfl
  | singleton a => cases a <;> rfl
  | cons_cons a b r ih1 ih2 =>
    cases a with
    | A => simp [bSweep,scanSafe,ih2]
    | B => rfl
    | C => cases b <;> simp [bSweep,scanSafe,ih1]
    | D => rfl

theorem bSweep_none (slow : Bool) (w : List Pair) (l : List Bool)
    (h : bSweep slow w l = none) :
    ∃ n, run (machine slow) n (render .B l (ray w)) = none := by
  induction w using twoStep generalizing l with
  | nil => simp [bSweep] at h
  | singleton a =>
    cases a with
    | A => simp [bSweep] at h
    | B => simp [bSweep] at h
    | C => simp [bSweep] at h
    | D => exact ⟨2,by cases slow <;> rfl⟩
  | cons_cons a b r ih1 ih2 =>
    cases a with
    | A =>
      have hh : bSweep slow (b::r) (true::l) = none := by simpa [bSweep] using h
      obtain ⟨n,hn⟩ := ih2 (true::l) hh
      refine ⟨2+n,?_⟩
      change run (machine slow) (2+n) (render .B l (bits [true,false] (ray (b::r)))) = none
      rw [run_add,B10]; exact hn
    | B => simp [bSweep] at h
    | C =>
      cases b with
      | A =>
        have hh : bSweep slow r (false::false::l) = none := by simpa [bSweep] using h
        obtain ⟨n,hn⟩ := ih1 (false::false::l) hh
        refine ⟨4+n,?_⟩
        change run (machine slow) (4+n) (render .B l (bits [false,false,true,false] (ray r))) = none
        rw [run_add,B0010]; exact hn
      | B => simp [bSweep] at h
      | C => simp [bSweep] at h
      | D => simp [bSweep] at h
    | D => exact ⟨2,by cases slow <;> rfl⟩

/-- This is a complete return-invariant interface for the two machines.
Every successful macro has strictly positive primitive length, so closure
implies all finite primitive prefixes, not merely infinitely many returns. -/
theorem forever_of_return_closed (slow : Bool) (P : List Bool → List Pair → Prop)
    (h0 : P [true] [])
    (closed : ∀ l w, P l w → ∃ t w', bSweep slow w l = some t ∧
      t.2.r = ray w' ∧ P t.2.l w') :
    ∀ n, ∃ d, run (machine slow) n primBlank = some d := by
  have all : ∀ n l w, P l w → ∃ d,
      run (machine slow) n (render .B l (ray w)) = some d := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro l w hp
      obtain ⟨t,w',ht,hr,hp'⟩ := closed l w hp
      obtain ⟨hpos,hs⟩ := bSweep_sound slow w l t ht
      have hs' : run (machine slow) t.1 (render .B l (ray w)) =
          some (render .B t.2.l (ray w')) := by simpa [Ret.render,hr] using hs
      by_cases hle : t.1 ≤ n
      · obtain ⟨d,hd⟩ := ih (n-t.1) (by omega) t.2.l w' hp'
        refine ⟨d,?_⟩
        rw [show n=t.1+(n-t.1) by omega,run_add,hs']
        exact hd
      · rw [show t.1=n+(t.1-n) by omega,run_add] at hs'
        cases h : run (machine slow) n (render .B l (ray w)) with
        | none => simp [h] at hs'
        | some d => exact ⟨d,rfl⟩
  intro n
  cases n with
  | zero => exact ⟨primBlank,rfl⟩
  | succ n =>
    obtain ⟨d,hd⟩ := all n [true] [] h0
    exact ⟨d,by rw [show n+1=1+n by omega]; exact join slow (start slow) hd⟩

/-- Signed radix-three weights induced by the right-turn rewrites.
The paired first/second bits contribute x and -3*y respectively. -/
def weight : Pair → Int
  | .A => 1
  | .B => -3
  | .C => 0
  | .D => -2

def value : List Pair → Int
  | [] => 0
  | a::r => weight a + 3*value r

theorem turn_B_value (r : List Pair) : value (.C::r) = value (.B::r)+3 := by
  simp [value,weight]; omega

theorem turn_CC_value (r : List Pair) : value (.C::.A::r) = value (.C::.C::r)+3 := by
  simp [value,weight]; omega

theorem turn_CB_value (r : List Pair) : value (.C::.D::r) = value (.C::.B::r)+3 := by
  simp [value,weight]; omega

theorem turn_CD_value (r : List Pair) : value (.B::.C::r) = value (.C::.D::r)+3 := by
  simp [value,weight]; omega

#print axioms cSweep_sound
#print axioms fSweep_sound
#print axioms bSweep_sound
#print axioms bSweep_none
#print axioms forever_of_return_closed
#print axioms turn_CD_value
end BB6CarrySweep
