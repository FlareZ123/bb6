import Raw59PackedQuery

set_option maxHeartbeats 0

namespace BB6.Agent32Raw59PackedQuery
open BB6Coverage BB6Coverage.Agent31Pump

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

def W.repeat (w : W) : Nat → W
  | 0 => ⟨0,0⟩
  | n+1 => w.cat (w.repeat n)

theorem W.repeat_decode (w : W) (n : Nat) :
    (w.repeat n).decode = rep w.decode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [W.repeat,W.cat_decode,ih,rep]

/-- Arbitrary finite block transfer, with a proof over untouched tails. -/
structure Rule where
  q : Fin 6
  right : Bool
  lp : W
  rp : W
  input : W
  output : W
  cost : Nat

def Rule.Valid (r : Rule) (p : BB6Coverage.PartialMachine) : Prop :=
  if r.right then
    ∀ L R, run0 p r.cost ⟨r.q,r.lp.decode++L,r.rp.decode++r.input.decode++R⟩ =
      some ⟨r.q,r.lp.decode++r.output.decode++L,r.rp.decode++R⟩
  else
    ∀ L R, run0 p r.cost ⟨r.q,r.lp.decode++r.input.decode++L,r.rp.decode++R⟩ =
      some ⟨r.q,r.lp.decode++L,r.rp.decode++r.output.decode++R⟩

def Rule.leftIn (r : Rule) (n : Nat) : W :=
  if r.right then r.lp else r.lp.cat (r.input.repeat n)
def Rule.rightIn (r : Rule) (n : Nat) : W :=
  if r.right then r.rp.cat (r.input.repeat n) else r.rp
def Rule.leftOut (r : Rule) (n : Nat) : W :=
  if r.right then r.lp.cat (r.output.repeat n) else r.lp
def Rule.rightOut (r : Rule) (n : Nat) : W :=
  if r.right then r.rp else r.rp.cat (r.output.repeat n)

def Rule.apply (r : Rule) (n : Nat) (z : BZ) : Option BZ :=
  if (z.q == r.q) && z.l.starts (r.leftIn n) && z.r.starts (r.rightIn n) then
    some ⟨r.q,(r.leftOut n).cat (z.l.drop (r.leftIn n).len),
      (r.rightOut n).cat (z.r.drop (r.rightIn n).len)⟩
  else none

theorem Rule.apply_sound (r : Rule) (p : BB6Coverage.PartialMachine) (hv : r.Valid p)
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
    cases hd : r.right
    · simp only [hd,Bool.false_eq_true,ite_false] at hv
      have H := sweepL p r.q r.lp.decode r.rp.decode r.input.decode
        r.output.decode r.cost hv n (z.l.drop (r.leftIn n).len).decode (z.r.drop (r.rightIn n).len).decode
      simp only [Rule.leftIn,Rule.rightIn,Rule.leftOut,Rule.rightOut,hd,
        Bool.false_eq_true,ite_false,W.cat_decode,W.repeat_decode] at hl hr H ⊢
      unfold BZ.decode
      rw [hc.1.1,hl,hr]
      simp only [Rule.leftOut,Rule.rightOut,hd,Bool.false_eq_true,ite_false,W.cat_decode,W.repeat_decode]
      exact H
    · simp only [hd,ite_true] at hv
      have H := sweepR p r.q r.lp.decode r.rp.decode r.input.decode
        r.output.decode r.cost hv n (z.l.drop (r.leftIn n).len).decode (z.r.drop (r.rightIn n).len).decode
      simp only [Rule.leftIn,Rule.rightIn,Rule.leftOut,Rule.rightOut,hd,
        ite_true,W.cat_decode,W.repeat_decode] at hl hr H ⊢
      unfold BZ.decode
      rw [hc.1.1,hl,hr]
      simp only [Rule.leftOut,Rule.rightOut,hd,ite_true,W.cat_decode,W.repeat_decode]
      exact H
  · simp at h

inductive Action (p : BB6Coverage.PartialMachine) where
  | raw (n : Nat)
  | sweep (r : Rule) (valid : r.Valid p) (n : Nat)

def Action.cost {p : BB6Coverage.PartialMachine} : Action p → Nat
  | .raw n => n
  | .sweep r _ n => r.cost*n

def Action.apply {p : BB6Coverage.PartialMachine} : Action p → BZ → Option BZ
  | .raw n,z => brun p n z
  | .sweep r _ n,z => r.apply n z

theorem Action.sound {p : BB6Coverage.PartialMachine} (a : Action p) (z t : BZ)
    (h : a.apply z = some t) : run0 p a.cost z.decode = some t.decode := by
  cases a with
  | raw n =>
    have hh := brun_decode p n z
    change brun p n z = some t at h
    rw [h] at hh
    exact hh.symm
  | sweep r hv n => exact Rule.apply_sound r p hv n z t h

def traceRun {p : BB6Coverage.PartialMachine} : List (Action p) → BZ → Option BZ
  | [], z => some z
  | a::xs,z => (a.apply z).bind (traceRun xs)
def traceCost {p : BB6Coverage.PartialMachine} : List (Action p) → Nat
  | [] => 0
  | a::xs => a.cost + traceCost xs

theorem trace_sound {p : BB6Coverage.PartialMachine} (xs : List (Action p)) (z t : BZ)
    (h : traceRun xs z = some t) : run0 p (traceCost xs) z.decode = some t.decode := by
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

#print axioms Rule.apply_sound
#print axioms trace_sound
end BB6.Agent32Raw59PackedQuery
