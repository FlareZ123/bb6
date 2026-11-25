import CountedBMO5PairScore
import Counted421Coverage

namespace CountedBMO5Pair.Coverage
open CountedBMO5Pair

def stateMap : Q → Counted421.Q
  | .A => .A | .B => .B | .C => .C | .D => .D | .E => .E | .F => .F

def liftCfg (c : Cfg) : Counted421.Cfg := ⟨stateMap c.q,c.l,c.r⟩
def encode (c : Cfg) (h : Int) := Counted421.Coverage.encode (liftCfg c) h
def Rel (a : Option Cfg) (b : Option BB6Coverage.Config) := Counted421.Coverage.Rel (a.map liftCfg) b

/-- #252: 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE. -/
def machine252 : BB6Coverage.Machine := fun (q,b) =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,3⟩
  | 1,false => some ⟨true,false,2⟩
  | 1,true => some ⟨false,true,0⟩
  | 2,false => some ⟨true,true,0⟩
  | 2,true => some ⟨true,false,1⟩
  | 3,false => some ⟨true,false,0⟩
  | 3,true => some ⟨true,false,4⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,false,2⟩
  | 5,false => none
  | 5,true => some ⟨false,true,4⟩
  | _,_ => none

/-- #754: 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE. -/
def machine754 : BB6Coverage.Machine := fun (q,b) =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨true,false,2⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨false,false,3⟩
  | 2,false => some ⟨true,false,0⟩
  | 2,true => some ⟨false,true,1⟩
  | 3,false => some ⟨true,false,1⟩
  | 3,true => some ⟨true,false,4⟩
  | 4,false => some ⟨true,true,5⟩
  | 4,true => some ⟨false,false,0⟩
  | 5,false => none
  | 5,true => some ⟨false,true,4⟩
  | _,_ => none

theorem right_rel (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    Rel (mvR q (if w then 1 else 0) l r) (some (BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,true,Counted421.Coverage.stateIndex (stateMap q)⟩)) := by
  have he : (mvR q (if w then 1 else 0) l r).map liftCfg=Counted421.mvR (stateMap q) (if w then 1 else 0) l r := by rfl
  unfold Rel encode
  rw [he]
  exact Counted421.Coverage.right_rel (stateMap q) (stateMap old) w l r h

theorem left_rel (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    Rel (mvL q (if w then 1 else 0) l r) (some (BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,false,Counted421.Coverage.stateIndex (stateMap q)⟩)) := by
  have he : (mvL q (if w then 1 else 0) l r).map liftCfg=Counted421.mvL (stateMap q) (if w then 1 else 0) l r := by rfl
  unfold Rel encode
  rw [he]
  exact Counted421.Coverage.left_rel (stateMap q) (stateMap old) w l r h

theorem encode_read (c : Cfg) (h : Int) : BB6Coverage.readSlot (encode c h)=(Counted421.Coverage.stateIndex (stateMap c.q),c.r.testBit 0) := Counted421.Coverage.encode_read (liftCfg c) h

theorem step252_rel (c : Cfg) (h : Int) : Rel (step c) (BB6Coverage.rawStep machine252 (encode c h)) := by
  rcases c with ⟨q,l,r⟩
  unfold BB6Coverage.rawStep
  rw [encode_read]
  have he : (r.testBit 0=false ∧ hd r=0) ∨ (r.testBit 0=true ∧ hd r=1) := Counted421.Coverage.bit_zero_cases r
  rcases he with ⟨hb,hh⟩|⟨hb,hh⟩ <;>
    cases q <;> simp only [step,hh,hb,ite_true,show (1:Nat)≠0 by decide,ite_false]
  · exact right_rel .B .A true l r h
  · exact left_rel .C .B true l r h
  · exact right_rel .A .C true l r h
  · exact left_rel .A .D true l r h
  · exact right_rel .F .E true l r h
  · exact True.intro
  · exact left_rel .D .A false l r h
  · exact right_rel .A .B false l r h
  · exact left_rel .B .C true l r h
  · exact left_rel .E .D true l r h
  · exact left_rel .C .E false l r h
  · exact right_rel .E .F false l r h

theorem step754_rel (c : Cfg) (h : Int) : Rel (step754 c) (BB6Coverage.rawStep machine754 (encode c h)) := by
  rcases c with ⟨q,l,r⟩
  unfold BB6Coverage.rawStep
  rw [encode_read]
  have he : (r.testBit 0=false ∧ hd r=0) ∨ (r.testBit 0=true ∧ hd r=1) := Counted421.Coverage.bit_zero_cases r
  rcases he with ⟨hb,hh⟩|⟨hb,hh⟩ <;>
    cases q <;> simp only [step754,hh,hb,ite_true,show (1:Nat)≠0 by decide,ite_false]
  · exact right_rel .B .A true l r h
  · exact right_rel .C .B true l r h
  · exact left_rel .A .C true l r h
  · exact left_rel .B .D true l r h
  · exact right_rel .F .E true l r h
  · exact True.intro
  · exact left_rel .C .A true l r h
  · exact left_rel .D .B false l r h
  · exact right_rel .B .C false l r h
  · exact left_rel .E .D true l r h
  · exact left_rel .A .E false l r h
  · exact right_rel .E .F false l r h

theorem run754_add (a b : Nat) (c : Cfg) : run754 (a+b) c=(run754 a c).bind (run754 b) := by
  induction a generalizing c with
  | zero => simp [run754]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [run754]; cases step754 c <;> simp [ih]

theorem run_rel_generic (m : BB6Coverage.Machine) (st : Cfg → Option Cfg) (rn : Nat → Cfg → Option Cfg)
    (h0 : ∀ c, rn 0 c=some c)
    (hs : ∀ n c, rn (n+1) c=(rn n c).bind st)
    (hstep : ∀ c h, Rel (st c) (BB6Coverage.rawStep m (encode c h)))
    (n : Nat) (c : Cfg) (h : Int) : Rel (rn n c) (BB6Coverage.run m n (encode c h)) := by
  induction n with
  | zero => rw [h0]; exact ⟨h,rfl⟩
  | succ n ih =>
    rw [hs]
    simp only [BB6Coverage.run]
    cases hr : rn n c with
    | none =>
      rw [hr] at ih
      cases hb : BB6Coverage.run m n (encode c h) with
      | none => trivial
      | some d => rw [hb] at ih; exact False.elim ih
    | some d =>
      rw [hr] at ih
      cases hb : BB6Coverage.run m n (encode c h) with
      | none => rw [hb] at ih; exact False.elim ih
      | some e =>
        rw [hb] at ih
        obtain ⟨head,he⟩ : ∃ head, e=encode d head := ih
        simp only [Option.bind_some]
        rw [he]
        exact hstep d head

theorem run252_rel (n : Nat) (c : Cfg) (h : Int) : Rel (run n c) (BB6Coverage.run machine252 n (encode c h)) := by
  apply run_rel_generic machine252 step run (fun _=>rfl) _ step252_rel
  intro k d
  rw [run_add]
  cases run k d <;> simp [run]

theorem run754_rel (n : Nat) (c : Cfg) (h : Int) : Rel (run754 n c) (BB6Coverage.run machine754 n (encode c h)) := by
  apply run_rel_generic machine754 step754 run754 (fun _=>rfl) _ step754_rel
  intro k d
  rw [run754_add]
  cases run754 k d <;> simp [run754]

theorem blank_encode : encode ⟨.A,0,0⟩ 0=BB6Coverage.blank := Counted421.Coverage.blank_encode

theorem rel_status {a : Option Cfg} {b : Option BB6Coverage.Config} (h : Rel a b) : a.isSome=b.isSome := by
  cases a <;> cases b <;> first | rfl | exact False.elim h

theorem status252 (n : Nat) : (run n blank252).isSome=(BB6Coverage.run machine252 n BB6Coverage.blank).isSome := by
  rw [←blank_encode]; exact rel_status (run252_rel n blank252 0)

theorem status754 (n : Nat) : (run754 n ⟨.A,0,0⟩).isSome=(BB6Coverage.run machine754 n BB6Coverage.blank).isSome := by
  rw [←blank_encode]; exact rel_status (run754_rel n ⟨.A,0,0⟩ 0)

theorem haltsAfter_generic (m : BB6Coverage.Machine) (st : Cfg → Option Cfg) (rn : Nat → Cfg → Option Cfg)
    (hs : ∀ n c, rn (n+1) c=(rn n c).bind st)
    (hstatus : ∀ n, (rn n ⟨.A,0,0⟩).isSome=(BB6Coverage.run m n BB6Coverage.blank).isSome) (n : Nat) :
    BB6Coverage.HaltsAfter m n ↔ ∃ d, rn n ⟨.A,0,0⟩=some d ∧ st d=none := by
  unfold BB6Coverage.HaltsAfter
  rw [←hstatus n]
  have h := hstatus (n+1)
  rw [hs] at h
  cases hr : rn n ⟨.A,0,0⟩ with
  | none => simp
  | some d =>
    simp only [hr,Option.bind_some] at h
    have hn : BB6Coverage.run m (n+1) BB6Coverage.blank=none ↔ st d=none := by
      cases hs : st d <;> cases hb : BB6Coverage.run m (n+1) BB6Coverage.blank <;> simp [hs,hb] at h ⊢
    rw [hn]
    simp

theorem exact252_coverage (n : Nat) : BB6Coverage.HaltsAfter machine252 n ↔ Exact blank252 (n+1) none := by
  have hh := haltsAfter_generic machine252 step run (by intro k c; rw [run_add]; cases run k c <;> simp [run]) status252 n
  rw [hh]
  constructor
  · rintro ⟨d,hr,hs⟩; exact ⟨n,d,rfl,hr,hs⟩
  · rintro ⟨k,d,hk,hr,hs⟩
    have : k=n := by omega
    subst k
    exact ⟨d,hr,hs⟩

theorem exact754_coverage (n : Nat) : BB6Coverage.HaltsAfter machine754 n ↔ Exact754 (n+1) := by
  rw [haltsAfter_generic machine754 step754 run754 (by intro k c; rw [run754_add]; cases run754 k c <;> simp [run754]) status754 n]
  constructor
  · rintro ⟨d,hr,hs⟩; exact ⟨n,d,rfl,hr,hs⟩
  · rintro ⟨k,d,hk,hr,hs⟩
    have : k=n := by omega
    subst k
    exact ⟨d,hr,hs⟩

theorem halts252_iff (n : Nat) : BB6Coverage.HaltsAfter machine252 n ↔ ∃ i, Cap.rootOf (Cap.halt i)=1 ∧ n+1=W i+3 :=
  (exact252_coverage n).trans (exact252_iff (n+1))

theorem halts754_iff (n : Nat) : BB6Coverage.HaltsAfter machine754 n ↔ ∃ i, Cap.rootOf (Cap.halt i)=3 ∧ n+1=W i+18 :=
  (exact754_coverage n).trans (exact754_literal_iff (n+1))

theorem first_failure (m : BB6Coverage.Machine) (t : Nat) (h : BB6Coverage.run m t BB6Coverage.blank=none) :
    ∃ n, BB6Coverage.HaltsAfter m n := by
  induction t with
  | zero => contradiction
  | succ t ih =>
    cases hprev : BB6Coverage.run m t BB6Coverage.blank with
    | none => exact ih hprev
    | some d => exact ⟨t,⟨by simp [hprev],h⟩⟩

theorem not_never (m : BB6Coverage.Machine) (h : ¬ BB6Coverage.NeverHalts m) : ∃ n, BB6Coverage.HaltsAfter m n := by
  classical
  unfold BB6Coverage.NeverHalts at h
  obtain ⟨t,ht⟩ := Classical.not_forall.mp h
  apply first_failure m t
  cases hh : BB6Coverage.run m t BB6Coverage.blank <;> simp_all

theorem decidedBelow_generic (m : BB6Coverage.Machine) (root offset bound : Nat) (ho : 0<offset)
    (h : ∀ n, BB6Coverage.HaltsAfter m n ↔ ∃ i, Cap.rootOf (Cap.halt i)=root ∧ n+1=W i+offset) :
    BB6Coverage.DecidedBelow bound m ↔ ∀ i, Cap.rootOf (Cap.halt i)=root → W i+offset≤bound := by
  constructor
  · intro hd i hi
    let n := W i+offset-1
    have he : n+1=W i+offset := by dsimp [n]; omega
    have hh : BB6Coverage.HaltsAfter m n := (h n).mpr ⟨i,hi,he⟩
    rcases hd with hn|⟨k,hk,hk'⟩
    · have hs := hn (n+1); rw [hh.2] at hs; contradiction
    · have hnk := BB6Coverage.halting_time_unique m n k hh hk'
      omega
  · intro ht
    classical
    by_cases hn : BB6Coverage.NeverHalts m
    · exact Or.inl hn
    · obtain ⟨n,hh⟩ := not_never m hn
      obtain ⟨i,hi,he⟩ := (h n).mp hh
      exact Or.inr ⟨n,by rw [he]; exact ht i hi,hh⟩

theorem decidedBelow252_iff (bound : Nat) : BB6Coverage.DecidedBelow bound machine252 ↔ ∀ i, Cap.rootOf (Cap.halt i)=1 → W i+3≤bound :=
  decidedBelow_generic machine252 1 3 bound (by decide) halts252_iff

theorem decidedBelow754_iff (bound : Nat) : BB6Coverage.DecidedBelow bound machine754 ↔ ∀ i, Cap.rootOf (Cap.halt i)=3 → W i+18≤bound :=
  decidedBelow_generic machine754 3 18 bound (by decide) halts754_iff

#print axioms run252_rel
#print axioms run754_rel
#print axioms decidedBelow252_iff
#print axioms decidedBelow754_iff
end CountedBMO5Pair.Coverage
