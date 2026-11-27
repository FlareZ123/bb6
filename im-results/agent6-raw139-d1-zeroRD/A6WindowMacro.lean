import A6BitTrace
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.A6WindowMacro
open BB6Coverage BB6Coverage.A6BitTrace

/-- A finite window includes its scanned bit on the left. The high tails are arbitrary. -/
structure W where
  q : Fin 6
  l : Nat
  r : Nat
  nl : Nat
  nr : Nat
  deriving DecidableEq, Repr

def ext (w : W) (L R : Nat) : P := ⟨w.q,w.l+2^w.nl*L,w.r+2^w.nr*R⟩

theorem add_pow_mod (a n x : Nat) (h : 0 < n) : (a+2^n*x)%2 = a%2 := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
  rw [show 2^(k+1)*x = 2*(2^k*x) by rw [Nat.pow_succ]; simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]]
  exact Nat.add_mul_mod_self_left _ _ _

theorem add_pow_div (a n x : Nat) (h : 0 < n) : (a+2^n*x)/2 = a/2+2^(n-1)*x := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1,by omega⟩
  rw [show 2^(k+1)*x = 2*(2^k*x) by rw [Nat.pow_succ]; simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]]
  rw [Nat.add_mul_div_left _ _ (by decide : 0<2)]
  simp [Nat.mul_comm]

def wstep (p : PartialMachine) (w : W) : Option W :=
  if w.nl = 0 then none else
  ((p (w.q,hd w.l)).bind id).bind fun mv =>
    if mv.right then
      if w.nr=0 then none else
      some ⟨mv.next,bit (hd w.r)+2*(bit mv.write+2*tl w.l),tl w.r,w.nl+1,w.nr-1⟩
    else some ⟨mv.next,tl w.l,bit mv.write+2*w.r,w.nl-1,w.nr+1⟩

theorem wstep_sound (p : PartialMachine) (w v : W) (h : wstep p w = some v) (L R : Nat) :
    stepP p (ext w L R) = some (ext v L R) := by
  unfold wstep at h
  split at h
  next => simp at h
  next hn =>
    have hl : 0 < w.nl := by omega
    have hread : hd (w.l+2^w.nl*L) = hd w.l := by simp [hd,add_pow_mod _ _ _ hl]
    have htail : tl (w.l+2^w.nl*L) = tl w.l+2^(w.nl-1)*L := by simp [tl,add_pow_div _ _ _ hl]
    cases he : (p (w.q,hd w.l)).bind id with
    | none => simp [he] at h
    | some mv =>
      simp only [he,Option.bind_some] at h
      split at h
      next hm =>
        split at h
        next => simp at h
        next hr =>
          have hrp : 0 < w.nr := by omega
          have hreadR : hd (w.r+2^w.nr*R) = hd w.r := by simp [hd,add_pow_mod _ _ _ hrp]
          have htailR : tl (w.r+2^w.nr*R) = tl w.r+2^(w.nr-1)*R := by simp [tl,add_pow_div _ _ _ hrp]
          have hv := Option.some.inj h
          subst v
          simp only [stepP,ext,hread,he,Option.map_some,hm,if_true,hreadR,htail,htailR,P.mk.injEq,Option.some.injEq,true_and,and_true]
          have hp : 2^(w.nl+1)*L = 4*(2^(w.nl-1)*L) := by
            have e : w.nl+1=(w.nl-1)+2 := by omega
            rw [e,Nat.pow_add]; simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          rw [hp]; omega
      next hm =>
        have hv := Option.some.inj h
        subst v
        simp only [stepP,ext,hread,he,Option.map_some,hm,Bool.false_eq_true,ite_false,htail,P.mk.injEq,Option.some.injEq,true_and]
        rw [Nat.pow_succ]
        simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
        omega

def wrun (p : PartialMachine) : Nat → W → Option W
  | 0,w => some w
  | n+1,w => (wstep p w).bind (wrun p n)

theorem wrun_sound (p : PartialMachine) (n : Nat) (w v : W) (h : wrun p n w = some v) (L R : Nat) :
    runP p n (ext w L R) = some (ext v L R) := by
  induction n generalizing w with
  | zero => have e := Option.some.inj h; subst v; rfl
  | succ n ih =>
    rw [wrun] at h
    cases he : wstep p w with
    | none => simp [he] at h
    | some u =>
      have h' : wrun p n u = some v := by simpa only [he,Option.bind_some] using h
      rw [runP,wstep_sound _ _ _ he L R]
      exact ih u h'

structure Rule (p : PartialMachine) where
  cost : Nat
  before : W
  after : W
  valid : wrun p cost before = some after

def apply (p : PartialMachine) (a : Rule p) (z : P) : Option P :=
  if z.q = a.before.q ∧ z.l % 2^a.before.nl = a.before.l ∧ z.r % 2^a.before.nr = a.before.r then
    some (ext a.after (z.l / 2^a.before.nl) (z.r / 2^a.before.nr))
  else none

theorem apply_sound (p : PartialMachine) (a : Rule p) (z u : P) (h : apply p a z = some u) :
    runP p a.cost z = some u := by
  unfold apply at h
  split at h
  next hh =>
    have h' := Option.some.inj h
    subst u
    have hz : z = ext a.before (z.l / 2^a.before.nl) (z.r / 2^a.before.nr) := by
      cases z with
      | mk q l r =>
        simp only [ext,P.mk.injEq]
        obtain ⟨hq,hl,hr⟩ := hh
        refine ⟨hq,?_,?_⟩
        · rw [← hl]; exact (Nat.mod_add_div _ _).symm
        · rw [← hr]; exact (Nat.mod_add_div _ _).symm
    calc
      runP p a.cost z = runP p a.cost (ext a.before (z.l / 2^a.before.nl) (z.r / 2^a.before.nr)) := congrArg (runP p a.cost) hz
      _ = _ := wrun_sound p a.cost a.before a.after a.valid _ _
  next => simp at h

def eval (p : PartialMachine) : List (Rule p) → P → Option (Nat × P)
  | [],z => some (0,z)
  | a::as,z => match apply p a z with
    | none => none
    | some u => (eval p as u).map fun (n,v) => (a.cost+n,v)

theorem eval_reach (p : PartialMachine) (as : List (Rule p)) (n k : Nat) (z u : P)
    (hz : Reach p n z) (h : eval p as z = some (k,u)) : Reach p (n+k) u := by
  induction as generalizing n k z with
  | nil => simp [eval] at h; obtain ⟨rfl,rfl⟩ := h; simpa using hz
  | cons a as ih =>
    rw [eval] at h
    cases ha : apply p a z with
    | none => simp [ha] at h
    | some v =>
      cases he : eval p as v with
      | none => simp [ha,he] at h
      | some pair =>
        obtain ⟨m,w⟩ := pair
        simp [ha,he] at h
        obtain ⟨rfl,rfl⟩ := h
        have hv := reach_extend hz (apply_sound p a z v ha)
        simpa only [Nat.add_assoc] using ih (n+a.cost) m v hv he

#print axioms wstep_sound
#print axioms wrun_sound
#print axioms apply_sound
#print axioms eval_reach
end BB6Coverage.A6WindowMacro
