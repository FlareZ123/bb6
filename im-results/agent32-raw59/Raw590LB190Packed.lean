import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw590LB190
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6.Agent10ZipAudit BB6Coverage.Agent10ZipAudit
open BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent13BlankDelay BB6.Agent8TNFPath

def table : PartialMachine := fun s => match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem one0 (L R : List Bool) :
    run0 table 5 ⟨1,[false]++L,[false]++[true,false,true]++R⟩ =
      some ⟨1,[false]++[true,false,true]++L,[false]++R⟩ := by rfl
theorem one1 (L R : List Bool) :
    run0 table 9 ⟨1,[]++[true,true,false]++L,[]++R⟩ =
      some ⟨1,[]++L,[]++[false,true,true]++R⟩ := by rfl
theorem one2 (L R : List Bool) :
    run0 table 9 ⟨2,[false,true]++[true,true,false]++L,[false]++R⟩ =
      some ⟨2,[false,true]++L,[false]++[false,true,true]++R⟩ := by rfl

/-- Length-bearing packed words; decoding is little-endian. -/
structure W where
  len : Nat
  bits : Nat
  deriving DecidableEq, Repr

def dec : Nat → Nat → List Bool
  | 0,_ => []
  | n+1,x => (x%2 == 1)::dec n (x/2)

def W.decode (w : W) : List Bool := dec w.len w.bits

def W.cat (x y : W) : W := ⟨x.len+y.len,x.bits % 2^x.len + 2^x.len * y.bits⟩

theorem dec_cat (n m x y : Nat) :
    dec (n+m) (x % 2^n + 2^n*y) = dec n x ++ dec m y := by
  induction n generalizing x with
  | zero => simp [dec,Nat.mod_one]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [dec,List.cons_append]
    rw [show 2^(n+1) = 2*2^n by rw [Nat.pow_succ,Nat.mul_comm]]
    have hmod : (x % (2*2^n) + 2*2^n*y)%2 = x%2 := by
      rw [Nat.mul_assoc,Nat.add_mul_mod_self_left,Nat.mod_mul_right_mod]
    have hdiv : (x % (2*2^n) + 2*2^n*y)/2 = x/2 % 2^n + 2^n*y := by
      rw [Nat.mul_assoc,Nat.add_mul_div_left _ _ (by decide),Nat.mod_mul_right_div_self]
    rw [hmod,hdiv,ih]

theorem W.cat_decode (x y : W) : (x.cat y).decode = x.decode ++ y.decode :=
  dec_cat x.len y.len x.bits y.bits

def W.drop (w : W) (n : Nat) : W := ⟨w.len-n,w.bits/2^n⟩
def W.starts (w pre : W) : Bool :=
  decide (pre.len ≤ w.len) && (w.bits % 2^pre.len == pre.bits)

theorem W.starts_sound (w pre : W) (h : w.starts pre = true) :
    w.decode = pre.decode ++ (w.drop pre.len).decode := by
  simp only [W.starts,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  have he : pre.cat (w.drop pre.len) = w := by
    cases w with
    | mk n x =>
      cases pre with
      | mk k y =>
        simp only [W.cat,W.drop] at *
        rw [← h.2,Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by decide)))]
        rw [Nat.mod_add_div]
        congr 1
        omega
  rw [← W.cat_decode,he]

def W.head (w : W) : Bool := w.len != 0 && w.bits % 2 == 1
def W.tail (w : W) : W := ⟨w.len-1,w.bits/2⟩
def W.push (w : W) (b : Bool) : W := ⟨w.len+1,b.toNat+2*w.bits⟩

theorem W.head_decode (w : W) : w.decode.headD false = w.head := by
  cases w with
  | mk n x => cases n <;> simp [W.decode,W.head,dec]

theorem W.tail_decode (w : W) : w.decode.tail = w.tail.decode := by
  cases w with
  | mk n x => cases n <;> rfl

theorem W.push_decode (w : W) (b : Bool) : (w.push b).decode = b::w.decode := by
  cases w with
  | mk n x =>
    cases b <;> simp [W.push,W.decode,dec,Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ (by decide : 0<2)]

def geom (n : Nat) : Nat := (8^n-1)/7
theorem geom_exact (n : Nat) : 8^n = 1+7*geom n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 8^(n+1) = 1+7*(1+8*geom n) := by
      rw [Nat.pow_succ, ih]
      omega
    have hg : geom (n+1) = 1+8*geom n := by
      unfold geom
      rw [he]
      omega
    rw [he,hg]
theorem geom_succ (n : Nat) : geom (n+1) = 1+8*geom n := by
  have h := geom_exact n
  have h' := geom_exact (n+1)
  rw [Nat.pow_succ,h] at h'
  omega

def repeat3 (v n : Nat) : W := ⟨3*n,v*geom n⟩
theorem repeat3_decode (v n : Nat) (hv : v < 8) :
    (repeat3 v n).decode = rep (dec 3 v) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : repeat3 v (n+1) = (W.mk 3 v).cat (repeat3 v n) := by
      simp only [repeat3,W.cat,geom_succ,Nat.mul_add,Nat.mul_one,Nat.mod_eq_of_lt hv]
      congr 1
      · omega
      · rw [← Nat.mul_assoc v 8 (geom n),Nat.mul_comm v 8,Nat.mul_assoc]
    rw [he,W.cat_decode,ih]
    rfl

structure BZ where
  q : Fin 6
  l : W
  r : W
  deriving DecidableEq, Repr

def BZ.decode (z : BZ) : Z0 := ⟨z.q,z.l.decode,z.r.decode⟩
def bstep (p : PartialMachine) (z : BZ) : Option BZ :=
  ((p (z.q,z.l.head)).bind id).map fun mv =>
    if mv.right then ⟨mv.next,(z.l.tail.push mv.write).push z.r.head,z.r.tail⟩
    else ⟨mv.next,z.l.tail,z.r.push mv.write⟩

def brun (p : PartialMachine) : Nat → BZ → Option BZ
  | 0,z => some z
  | n+1,z => (bstep p z).bind (brun p n)

theorem bstep_decode (p : PartialMachine) (z : BZ) :
    (bstep p z).map BZ.decode = step0 p z.decode := by
  unfold bstep step0
  simp only [BZ.decode,W.head_decode]
  cases h : (p (z.q,z.l.head)).bind id with
  | none => rfl
  | some mv =>
    cases hd : mv.right <;> simp [hd,BZ.decode,move0,W.push_decode,W.tail_decode,W.head_decode]
    cases z.r with
    | mk n x => cases n <;> simp [W.head,W.decode,dec]

theorem brun_decode (p : PartialMachine) (n : Nat) (z : BZ) :
    (brun p n z).map BZ.decode = run0 p n z.decode := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [brun,run0,← bstep_decode]
    cases h : bstep p z with
    | none => rfl
    | some t => exact ih t

structure Rule where
  q : Fin 6
  right : Bool
  lp : W
  rp : W
  input : Nat
  output : Nat
  cost : Nat

def Rule.Valid (r : Rule) (p : PartialMachine) : Prop :=
  r.input < 8 ∧ r.output < 8 ∧
  if r.right then
    ∀ L R, run0 p r.cost ⟨r.q,r.lp.decode++L,r.rp.decode++dec 3 r.input++R⟩ =
      some ⟨r.q,r.lp.decode++dec 3 r.output++L,r.rp.decode++R⟩
  else
    ∀ L R, run0 p r.cost ⟨r.q,r.lp.decode++dec 3 r.input++L,r.rp.decode++R⟩ =
      some ⟨r.q,r.lp.decode++L,r.rp.decode++dec 3 r.output++R⟩

def Rule.leftIn (r : Rule) (n : Nat) : W :=
  if r.right then r.lp else r.lp.cat (repeat3 r.input n)
def Rule.rightIn (r : Rule) (n : Nat) : W :=
  if r.right then r.rp.cat (repeat3 r.input n) else r.rp
def Rule.leftOut (r : Rule) (n : Nat) : W :=
  if r.right then r.lp.cat (repeat3 r.output n) else r.lp
def Rule.rightOut (r : Rule) (n : Nat) : W :=
  if r.right then r.rp else r.rp.cat (repeat3 r.output n)

def Rule.apply (r : Rule) (n : Nat) (z : BZ) : Option BZ :=
  if (z.q == r.q) && z.l.starts (r.leftIn n) && z.r.starts (r.rightIn n) then
    some ⟨r.q,(r.leftOut n).cat (z.l.drop (r.leftIn n).len),
      (r.rightOut n).cat (z.r.drop (r.rightIn n).len)⟩
  else none

theorem Rule.apply_sound (r : Rule) (p : PartialMachine) (hv : r.Valid p)
    (n : Nat) (z t : BZ) (h : r.apply n z = some t) :
    run0 p (r.cost*n) z.decode = some t.decode := by
  unfold Rule.apply at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true,beq_iff_eq] at hc
    have hl := W.starts_sound _ _ hc.1.2
    have hr := W.starts_sound _ _ hc.2
    simp only [Option.some.injEq] at h
    subst t
    unfold Rule.Valid at hv
    obtain ⟨hi,ho,hv⟩ := hv
    cases hd : r.right
    · simp only [hd,Bool.false_eq_true,ite_false] at hv
      have H := sweepL p r.q r.lp.decode r.rp.decode (dec 3 r.input)
        (dec 3 r.output) r.cost hv n (z.l.drop (r.leftIn n).len).decode (z.r.drop (r.rightIn n).len).decode
      simp only [Rule.leftIn,Rule.rightIn,Rule.leftOut,Rule.rightOut,hd,
        Bool.false_eq_true,ite_false,W.cat_decode,repeat3_decode _ _ hi,repeat3_decode _ _ ho] at hl hr H ⊢
      unfold BZ.decode
      rw [hc.1.1,hl,hr]
      simp only [Rule.leftOut,Rule.rightOut,hd,Bool.false_eq_true,ite_false,W.cat_decode,
        repeat3_decode _ _ ho]
      exact H
    · simp only [hd,ite_true] at hv
      have H := sweepR p r.q r.lp.decode r.rp.decode (dec 3 r.input)
        (dec 3 r.output) r.cost hv n (z.l.drop (r.leftIn n).len).decode (z.r.drop (r.rightIn n).len).decode
      simp only [Rule.leftIn,Rule.rightIn,Rule.leftOut,Rule.rightOut,hd,
        ite_true,W.cat_decode,repeat3_decode _ _ hi,repeat3_decode _ _ ho] at hl hr H ⊢
      unfold BZ.decode
      rw [hc.1.1,hl,hr]
      simp only [Rule.leftOut,Rule.rightOut,hd,ite_true,W.cat_decode,
        repeat3_decode _ _ ho]
      exact H
  · simp at h

def rule0 : Rule := ⟨1,true,⟨1,0⟩,⟨1,0⟩,5,5,5⟩
def rule1 : Rule := ⟨1,false,⟨0,0⟩,⟨0,0⟩,3,6,9⟩
def rule2 : Rule := ⟨2,false,⟨2,2⟩,⟨1,0⟩,3,6,9⟩
theorem rule0_valid : rule0.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  exact one0
theorem rule1_valid : rule1.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  exact one1
theorem rule2_valid : rule2.Valid table := by
  refine ⟨by decide,by decide,?_⟩
  exact one2

inductive Action where
  | raw (n : Nat)
  | right (n : Nat)
  | leftB (n : Nat)
  | leftC (n : Nat)
  deriving Repr

def Action.cost : Action → Nat
  | .raw n => n
  | .right n => 5*n
  | .leftB n => 9*n
  | .leftC n => 9*n
def Action.apply : Action → BZ → Option BZ
  | .raw n,z => brun table n z
  | .right n,z => rule0.apply n z
  | .leftB n,z => rule1.apply n z
  | .leftC n,z => rule2.apply n z

theorem Action.sound (a : Action) (z t : BZ) (h : a.apply z = some t) :
    run0 table a.cost z.decode = some t.decode := by
  cases a with
  | raw n =>
    have hh := brun_decode table n z
    change brun table n z = some t at h
    rw [h] at hh
    exact hh.symm
  | right n => exact Rule.apply_sound rule0 table rule0_valid n z t h
  | leftB n => exact Rule.apply_sound rule1 table rule1_valid n z t h
  | leftC n => exact Rule.apply_sound rule2 table rule2_valid n z t h

def traceRun : List Action → BZ → Option BZ
  | [], z => some z
  | a::xs,z => (a.apply z).bind (traceRun xs)

def traceCost : List Action → Nat
  | [] => 0
  | a::xs => a.cost + traceCost xs

theorem trace_sound (xs : List Action) (z t : BZ) (h : traceRun xs z = some t) :
    run0 table (traceCost xs) z.decode = some t.decode := by
  induction xs generalizing z with
  | nil =>
    simp [traceRun] at h
    subst t
    rfl
  | cons a xs ih =>
    simp only [traceRun] at h
    cases he : a.apply z with
    | none => simp [he] at h
    | some mid =>
      have hm := a.sound z mid he
      have ht := ih mid (by simpa [he] using h)
      simp only [traceCost,run0_add,hm,Option.bind_some]
      exact ht

#print axioms trace_sound
end BB6.Agent32Raw590LB190
