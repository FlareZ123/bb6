import ReverseSet
namespace BB6.Agent43ReverseSet

/-- A real forward path under a fixed target window. -/
inductive Walk (C y : Nat → Nat) (s a : Nat) : Nat → Nat → Prop
  | nil : Walk C y s a 0 a
  | step (k b x c : Nat) : Walk C y s a k b → x≤1 → b+1<C (s+k) →
      2*c+y (s+k)=b+x*C (s+k) → Walk C y s a (k+1) c

def backBounded (C y : Nat) (cs : List Nat) : List Nat :=
  let lo := cs.filterMap fun c => if 2*c+y<C-1 then some (2*c+y) else none
  let hi := cs.filterMap fun c => if C≤2*c+y ∧ 2*c+y<2*C-1 then some (2*c+y-C) else none
  mergeUnique (lo.length+hi.length) lo hi

theorem backBounded_sound (C y b x c : Nat) (cs : List Nat) (hc : c∈cs)
    (hx : x≤1) (hb : b+1<C) (he : 2*c+y=b+x*C) : b∈backBounded C y cs := by
  unfold backBounded
  apply (mem_mergeUnique _ _ _ _).2
  by_cases h : x=0
  · subst x; simp at he
    left; exact List.mem_filterMap.mpr ⟨c,hc,by simp [he,hb]⟩
  · have h1 : x=1 := by omega
    subst x; simp at he
    right; exact List.mem_filterMap.mpr ⟨c,hc,by simp [show C≤2*c+y by omega,show 2*c+y<2*C-1 by omega,show 2*c+y-C=b by omega]⟩

def rewindBounded (C y : Nat → Nat) (s : Nat) : Nat → List Nat → List Nat
  | 0,cs => cs
  | _+1,[] => []
  | k+1,c::cs => rewindBounded C y s k (backBounded (C (s+k)) (y (s+k)) (c::cs))

theorem rewindBounded_sound {C y : Nat → Nat} {s a k c : Nat} (hw : Walk C y s a k c)
    (cs : List Nat) (hc : c∈cs) : a∈rewindBounded C y s k cs := by
  induction hw generalizing cs with
  | nil => exact hc
  | step k b x c h hx hb he ih =>
    cases cs with
    | nil => simp at hc
    | cons d ds => exact ih _ (backBounded_sound _ _ _ _ _ _ hc hx hb he)

def omitted (bound ends : Nat) : Nat := (2^bound-1) ^^^ (ends % 2^bound)

def reverseCheck (L bound : Nat) (C y : Nat → Nat) (s k start ends : Nat) : Bool :=
  (rewindBounded C y s k (extract 0 (omitted bound ends) L)).all fun a => !(start.testBit a)

theorem reverseCheck_sound {L bound : Nat} {C y : Nat → Nat} {s k start ends a c : Nat}
    (hcheck : reverseCheck L bound C y s k start ends=true)
    (hw : Walk C y s a k c) (ha : start.testBit a=true) (hc : c<bound) (hL : c<2^L) : ends.testBit c=true := by
  by_cases h : ends.testBit c=true
  · exact h
  · have hfalse : ends.testBit c=false := by cases he : ends.testBit c <;> simp_all
    have hbit : (omitted bound ends).testBit c=true := by simp [omitted,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,hc,hfalse]
    have hm : c∈extract 0 (omitted bound ends) L := (extract_iff _ _ _ _).2 ⟨by omega,by omega,by simpa using hbit⟩
    have hstart := rewindBounded_sound hw _ hm
    have hcontra := List.all_eq_true.mp hcheck a hstart
    simp [ha] at hcontra

#print axioms rewindBounded_sound
#print axioms reverseCheck_sound
end BB6.Agent43ReverseSet
