import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1UnarySweep
open BB6Coverage BB6Coverage.Agent31Pump

def bit : List Bool → Nat → Bool
  | l, 0 => l.headD false
  | l, n+1 => bit l.tail n

def PadEq (l r : List Bool) : Prop := ∀ i, bit l i = bit r i

theorem pad_refl (l : List Bool) : PadEq l l := fun _ => rfl

theorem pad_symm {l r : List Bool} (h : PadEq l r) : PadEq r l := fun i => (h i).symm

theorem pad_trans {l r s : List Bool} (h : PadEq l r) (g : PadEq r s) : PadEq l s := fun i => (h i).trans (g i)

theorem pad_tail {l r : List Bool} (h : PadEq l r) : PadEq l.tail r.tail := fun i => h (i+1)

theorem pad_head {l r : List Bool} (h : PadEq l r) : l.headD false = r.headD false := h 0

theorem pad_cons {l r : List Bool} {a b : Bool} (e : a = b) (h : PadEq l r) : PadEq (a::l) (b::r) := by
  intro i; cases i with
  | zero => exact e
  | succ i => exact h i

theorem bit_nil (i : Nat) : bit [] i = false := by induction i with
  | zero => rfl
  | succ i ih => exact ih

theorem pad_false_nil : PadEq [false] [] := by
  intro i; cases i with
  | zero => rfl
  | succ i => exact (bit_nil i).trans (bit_nil (i+1)).symm

theorem pad_append {l r : List Bool} (h : PadEq l r) (p : List Bool) : PadEq (p ++ l) (p ++ r) := by
  induction p with
  | nil => exact h
  | cons a p ih => exact pad_cons rfl ih

theorem pad_zeros (n : Nat) : PadEq (List.replicate n false) [] := by
  induction n with
  | zero => exact pad_refl []
  | succ n ih =>
    rw [List.replicate_succ]
    exact pad_trans (pad_cons rfl ih) pad_false_nil

def ZEq (z z' : Z0) : Prop := z.q = z'.q ∧ PadEq z.l z'.l ∧ PadEq z.r z'.r

theorem zrefl (z : Z0) : ZEq z z := ⟨rfl,pad_refl _,pad_refl _⟩
theorem zsymm {z z' : Z0} (h : ZEq z z') : ZEq z' z := ⟨h.1.symm,pad_symm h.2.1,pad_symm h.2.2⟩
theorem ztrans {x y z : Z0} (h : ZEq x y) (g : ZEq y z) : ZEq x z := ⟨h.1.trans g.1,pad_trans h.2.1 g.2.1,pad_trans h.2.2 g.2.2⟩

theorem move_congr (m : Move) {x y : Z0} (h : ZEq x y) : ZEq (move0 m x) (move0 m y) := by
  unfold move0
  split
  · exact ⟨rfl,pad_cons (pad_head h.2.2) (pad_cons rfl (pad_tail h.2.1)),pad_tail h.2.2⟩
  · exact ⟨rfl,pad_tail h.2.1,pad_cons rfl h.2.2⟩

theorem step_congr (p : PartialMachine) {x y z : Z0} (h : ZEq x y) (hs : step0 p x = some z) : ∃ w, step0 p y = some w ∧ ZEq z w := by
  unfold step0 at hs ⊢
  have e : (y.q,y.l.headD false) = (x.q,x.l.headD false) := by rw [← h.1, ← pad_head h.2.1]
  rw [e]
  cases hm : (p (x.q,x.l.headD false)).bind id with
  | none => rw [hm] at hs; contradiction
  | some m =>
    simp only [hm,Option.map_some,Option.some.injEq] at hs
    subst z
    exact ⟨move0 m y,rfl,move_congr m h⟩

theorem run_congr (p : PartialMachine) (n : Nat) {x y z : Z0} (h : ZEq x y) (hs : run0 p n x = some z) : ∃ w, run0 p n y = some w ∧ ZEq z w := by
  induction n generalizing x y z with
  | zero =>
    simp only [run0.eq_1,Option.some.injEq] at hs
    subst z
    exact ⟨y,rfl,h⟩
  | succ n ih =>
    rw [run0.eq_2] at hs ⊢
    cases he : step0 p x with
    | none => simp [he] at hs
    | some x' =>
      rcases step_congr p h he with ⟨y',hy,hxy⟩
      rw [he] at hs
      change run0 p n x' = some z at hs
      rcases ih hxy hs with ⟨w,hw,hzw⟩
      exact ⟨w,by simpa [hy] using hw,hzw⟩

-- Any invariant with a positive-duration successor proves never halting.
theorem never_of_closed (p : PartialMachine) (I : Z0 → Prop) (hi : I ⟨0,[],[]⟩)
    (closed : ∀ z, I z → ∃ k w, 0 < k ∧ run0 p k z = some w ∧ I w)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have build (n : Nat) : ∃ k z, n ≤ k ∧ run0 p k ⟨0,[],[]⟩ = some z ∧ I z := by
    induction n with
    | zero => exact ⟨0,_,by omega,rfl,hi⟩
    | succ n ih =>
      rcases ih with ⟨t,z,ht,hz,hI⟩
      rcases closed z hI with ⟨k,w,hk,hw,hIw⟩
      exact ⟨t+k,w,by omega,join0 hz hw,hIw⟩
  intro n
  rcases build n with ⟨t,z,ht,hz,_⟩
  have hp := run_project p t start
  rw [show project start = (⟨0,[],[]⟩ : Z0) from rfl, hz] at hp
  cases he : Agent50Zipper.zrun p t start with
  | none => simp [he] at hp
  | some w =>
    have hrun := Agent50Zipper.zrun_sound p m hm t start w he
    rw [start_embed] at hrun
    have hs : n+(t-n)=t := by omega
    rw [← hs,run_append] at hrun
    cases hn : run m n blank with
    | none => simp [hn] at hrun
    | some c => rfl

def AConfig (a : Nat) (c : Bool) (b : Nat) : Z0 :=
  ⟨0,c :: List.replicate a true,List.replicate b true⟩

def Macro (p : PartialMachine) (k : Nat) (a : Nat) (c : Bool) (b A : Nat) (C : Bool) (B : Nat) : Prop :=
  ∃ z, run0 p k (AConfig a c b) = some z ∧ ZEq z (AConfig A C B)

theorem macro_exact (p : PartialMachine) (k a : Nat) (c : Bool) (b A : Nat) (C : Bool) (B : Nat)
    (h : run0 p k (AConfig a c b) = some (AConfig A C B)) : Macro p k a c b A C B :=
  ⟨_,h,zrefl _⟩

theorem macro_blankLeft (p : PartialMachine) (k a : Nat) (c : Bool) (b B : Nat)
    (h : run0 p k (AConfig a c b) = some ⟨0,[],List.replicate B true⟩) : Macro p k a c b 0 false B :=
  ⟨_,h,⟨rfl,pad_symm pad_false_nil,pad_refl _⟩⟩

theorem never_of_macros (p : PartialMachine) (G : Nat → Bool → Nat → Prop)
    (entry : ∃ k z a c b, 0 < k ∧ run0 p k ⟨0,[],[]⟩ = some z ∧ ZEq z (AConfig a c b) ∧ G a c b)
    (closed : ∀ a c b, G a c b → ∃ k A C B, 0 < k ∧ Macro p k a c b A C B ∧ G A C B)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let I : Z0 → Prop := fun z => z = ⟨0,[],[]⟩ ∨ ∃ a c b, ZEq z (AConfig a c b) ∧ G a c b
  apply never_of_closed p I (Or.inl rfl) _ m hm
  intro z hz
  rcases hz with rfl | ⟨a,c,b,hz,hG⟩
  · rcases entry with ⟨k,w,a,c,b,hk,hw,hEq,hG⟩
    exact ⟨k,w,hk,hw,Or.inr ⟨a,c,b,hEq,hG⟩⟩
  · rcases closed a c b hG with ⟨k,A,C,B,hk,hMacro,hGood⟩
    rcases hMacro with ⟨w,hw,hEq⟩
    rcases run_congr p k (zsymm hz) hw with ⟨v,hv,hev⟩
    exact ⟨k,v,hk,hv,Or.inr ⟨A,C,B,ztrans (zsymm hev) hEq,hGood⟩⟩

#print axioms never_of_macros
end BB6Coverage.Agent1UnarySweep
