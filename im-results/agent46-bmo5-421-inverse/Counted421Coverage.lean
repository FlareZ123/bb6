import Counted421BandBound
import Frontier

namespace Counted421.Coverage

open Counted421

def stateIndex : Q → Fin 6
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

/-- Literal normalized holdout #421: 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE. -/
def machine : BB6Coverage.Machine := fun (q,b) =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true  => some ⟨true,true,4⟩
  | 1,false => some ⟨true,false,2⟩
  | 1,true  => some ⟨false,true,0⟩
  | 2,false => some ⟨true,true,3⟩
  | 2,true  => some ⟨false,false,1⟩
  | 3,false => some ⟨true,false,1⟩
  | 3,true  => some ⟨true,true,2⟩
  | 4,false => some ⟨true,false,5⟩
  | 4,true  => some ⟨false,true,3⟩
  | 5,false => none
  | 5,true  => some ⟨false,false,4⟩
  | _,_ => none

def push (w : Bool) (n : Nat) := if w then b1 n else b0 n

theorem push_zero (w : Bool) (n : Nat) : (push w n).testBit 0=w := by
  cases w <;> simp [push,Nat.testBit_zero,b0,b1]

theorem push_succ (w : Bool) (n i : Nat) : (push w n).testBit (i+1)=n.testBit i := by
  rw [Nat.testBit_succ]
  change (tl (push w n)).testBit i=n.testBit i
  cases w <;> simp [push]

def symbol (l r : Nat) : Int → Bool
  | .ofNat n => r.testBit n
  | .negSucc n => l.testBit n

def rightCfg (q : Q) (w : Bool) (l r : Nat) : Cfg := ⟨q,push w l,tl r⟩
def leftCfg (q : Q) (w : Bool) (l r : Nat) : Cfg := ⟨q,tl l,push (l.testBit 0) (push w (tl r))⟩

theorem right_symbol (w : Bool) (l r : Nat) (k : Int) :
    symbol (push w l) (tl r) k = if k = -1 then w else symbol l r (k+1) := by
  cases k with
  | ofNat n =>
    have h : (Int.ofNat n : Int)≠ -1 := by simp only [Int.ofNat_eq_natCast]; omega
    have hs : (Int.ofNat n : Int)+1=Int.ofNat (n+1) := by simp only [Int.ofNat_eq_natCast,Int.natCast_add]; omega
    rw [ite_eq_right h,hs]
    exact Nat.testBit_div_two r n
  | negSucc n =>
    cases n with
    | zero => simpa [symbol] using push_zero w l
    | succ n =>
      have h : (Int.negSucc (n+1) : Int)≠ -1 := by omega
      have hs : (Int.negSucc (n+1) : Int)+1=Int.negSucc n := by omega
      rw [ite_eq_right h,hs]
      exact push_succ w l n

theorem left_symbol (w : Bool) (l r : Nat) (k : Int) :
    symbol (tl l) (push (l.testBit 0) (push w (tl r))) k = if k = 1 then w else symbol l r (k-1) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => change (push (l.testBit 0) (push w (tl r))).testBit 0=l.testBit 0; exact push_zero _ _
    | succ n =>
      cases n with
      | zero => change (push (l.testBit 0) (push w (tl r))).testBit 1=w; rw [push_succ,push_zero]
      | succ n =>
        have h : (Int.ofNat (n+2) : Int)≠ 1 := by simp only [Int.ofNat_eq_natCast,Int.natCast_add]; omega
        have hs : (Int.ofNat (n+2) : Int)-1=Int.ofNat (n+1) := by simp only [Int.ofNat_eq_natCast,Int.natCast_add]; omega
        rw [ite_eq_right h,hs]
        change (push (l.testBit 0) (push w (tl r))).testBit (n+1+1)=r.testBit (n+1)
        rw [push_succ,push_succ]
        exact Nat.testBit_div_two r n
  | negSucc n =>
    have h : (Int.negSucc n : Int)≠1 := by omega
    have hs : (Int.negSucc n : Int)-1=Int.negSucc (n+1) := by omega
    rw [ite_eq_right h,hs]
    exact Nat.testBit_div_two l n

def encode (c : Cfg) (h : Int) : BB6Coverage.Config :=
  ⟨stateIndex c.q,h,fun x=>symbol c.l c.r (x-h)⟩

theorem encode_read (c : Cfg) (h : Int) : BB6Coverage.readSlot (encode c h)=(stateIndex c.q,c.r.testBit 0) := by
  simp [encode,BB6Coverage.readSlot,symbol]

theorem apply_right (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,true,stateIndex q⟩ = encode (rightCfg q w l r) (h+1) := by
  unfold BB6Coverage.applyMove encode rightCfg
  simp only [ite_true]
  congr 1
  funext x
  rw [right_symbol]
  have he : x-(h+1)=-1 ↔ x=h := by omega
  simp only [he,show x-(h+1)+1=x-h by omega]

theorem apply_left (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,false,stateIndex q⟩ = encode (leftCfg q w l r) (h-1) := by
  unfold BB6Coverage.applyMove encode leftCfg
  simp only [Bool.false_eq_true,ite_false]
  rw [show h+(-1)=h-1 by omega]
  congr 1
  funext x
  rw [left_symbol]
  have he : x-(h-1)=1 ↔ x=h := by omega
  simp only [he,show x-(h-1)-1=x-h by omega]

theorem bit_zero_cases (n : Nat) : (n.testBit 0=false ∧ hd n=0) ∨ (n.testBit 0=true ∧ hd n=1) := by
  have h : hd n<2 := Nat.mod_lt _ (by decide)
  by_cases h0 : hd n=0
  · left; refine ⟨?_,h0⟩; unfold hd at h0; simp [Nat.testBit_zero,h0]
  · right; have h1 : hd n=1 := by omega
    exact ⟨by unfold hd at h1; simp [Nat.testBit_zero,h1],h1⟩

theorem mvR_bool (q : Q) (w : Bool) (l r : Nat) : mvR q (if w then 1 else 0) l r=some (rightCfg q w l r) := by
  cases w <;> rfl

theorem mvL_bool (q : Q) (w : Bool) (l r : Nat) : mvL q (if w then 1 else 0) l r=some (leftCfg q w l r) := by
  rcases bit_zero_cases l with ⟨hb,hh⟩|⟨hb,hh⟩ <;> cases w <;> simp [mvL,leftCfg,push,hb,hh]

def Rel : Option Cfg → Option BB6Coverage.Config → Prop
  | none,none => True
  | some c,some d => ∃ h, d=encode c h
  | _,_ => False

theorem right_rel (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    Rel (mvR q (if w then 1 else 0) l r) (some (BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,true,stateIndex q⟩)) := by
  rw [mvR_bool]
  exact ⟨h+1,apply_right q old w l r h⟩

theorem left_rel (q old : Q) (w : Bool) (l r : Nat) (h : Int) :
    Rel (mvL q (if w then 1 else 0) l r) (some (BB6Coverage.applyMove (encode ⟨old,l,r⟩ h) ⟨w,false,stateIndex q⟩)) := by
  rw [mvL_bool]
  exact ⟨h-1,apply_left q old w l r h⟩

theorem step_rel (c : Cfg) (h : Int) : Rel (step c) (BB6Coverage.rawStep machine (encode c h)) := by
  rcases c with ⟨q,l,r⟩
  unfold BB6Coverage.rawStep
  rw [encode_read]
  rcases bit_zero_cases r with ⟨hb,hh⟩|⟨hb,hh⟩ <;>
    cases q <;> simp only [step,hh,hb,ite_true,show (1:Nat)≠0 by decide,ite_false]
  · exact right_rel .B .A true l r h
  · exact left_rel .C .B true l r h
  · exact right_rel .D .C true l r h
  · exact left_rel .B .D true l r h
  · exact left_rel .F .E true l r h
  · exact True.intro
  · exact right_rel .E .A true l r h
  · exact right_rel .A .B false l r h
  · exact left_rel .B .C false l r h
  · exact right_rel .C .D true l r h
  · exact right_rel .D .E false l r h
  · exact left_rel .E .F false l r h

/-- All attempted instructions, including a halt, commute with the tape encoding. -/
theorem run_rel (n : Nat) (c : Cfg) (h : Int) : Rel (Counted421.run n c) (BB6Coverage.run machine n (encode c h)) := by
  induction n with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    rw [show n+1=n+1 by rfl,run_add]
    simp only [BB6Coverage.run]
    cases hrel : Counted421.run n c with
    | none =>
      rw [hrel] at ih
      cases habs : BB6Coverage.run machine n (encode c h) with
      | none => trivial
      | some d => rw [habs] at ih; exact False.elim ih
    | some d =>
      rw [hrel] at ih
      cases habs : BB6Coverage.run machine n (encode c h) with
      | none => rw [habs] at ih; exact False.elim ih
      | some e =>
        rw [habs] at ih
        obtain ⟨head,he⟩ := ih
        simp only [Option.bind_some]
        rw [he]
        simpa [Counted421.run] using step_rel d head

theorem blank_encode : encode ⟨.A,0,0⟩ 0=BB6Coverage.blank := by
  unfold encode BB6Coverage.blank stateIndex
  congr 1
  funext x
  simp only [Int.sub_zero]
  cases x <;> simp [symbol]

theorem blank_run_rel (n : Nat) : Rel (Counted421.run n ⟨.A,0,0⟩) (BB6Coverage.run machine n BB6Coverage.blank) := by
  rw [←blank_encode]
  exact run_rel n _ _

theorem rel_status {a : Option Cfg} {b : Option BB6Coverage.Config} (h : Rel a b) : a.isSome=b.isSome := by
  cases a <;> cases b <;> first | rfl | exact False.elim h

theorem status_iff (n : Nat) : (Counted421.run n ⟨.A,0,0⟩).isSome=(BB6Coverage.run machine n BB6Coverage.blank).isSome :=
  rel_status (blank_run_rel n)

theorem exact_iff_haltsAfter (n : Nat) : Exact ⟨.A,0,0⟩ (n+1) none ↔ BB6Coverage.HaltsAfter machine n := by
  unfold BB6Coverage.HaltsAfter
  rw [←status_iff n]
  have h := status_iff (n+1)
  cases ha : Counted421.run n ⟨.A,0,0⟩ with
  | none =>
    constructor
    · intro he
      obtain ⟨k,d,hk,hr,_⟩ := he
      have hk' : k=n := by omega
      subst k
      rw [ha] at hr
      contradiction
    · intro h; simp at h
  | some d =>
    have hn : Counted421.run (n+1) ⟨.A,0,0⟩=step d := by rw [run_add,ha]; simp [Counted421.run]
    rw [hn] at h
    have hnone : BB6Coverage.run machine (n+1) BB6Coverage.blank=none ↔ step d=none := by
      cases hs : step d <;> cases habs : BB6Coverage.run machine (n+1) BB6Coverage.blank <;> simp [hs,habs] at h ⊢
    rw [hnone]
    constructor
    · intro he
      obtain ⟨k,e,hk,hr,hs⟩ := he
      have hk' : k=n := by omega
      subst k
      rw [ha] at hr
      have heq := Option.some.inj hr
      subst e
      exact ⟨rfl,hs⟩
    · intro h
      exact ⟨n,d,rfl,ha,h.2⟩

theorem haltsAfter_iff_terminal (n : Nat) : BB6Coverage.HaltsAfter machine n ↔
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n+1=8+arrivalCost (Cap.halt i)+score (Cap.halt i) := by
  rw [←exact_iff_haltsAfter,exact_blank_iff]

theorem coverage_halt_bound (n : Nat) (h : BB6Coverage.HaltsAfter machine n) :
    ∃ i, Cap.rootOf (Cap.halt i)=2 ∧ n+1≤8+800*(i+5)*4^i :=
  halt_score_bound_sharp (n+1) ((exact_iff_haltsAfter n).mpr h)

/-- Any failed finite run has a first halting query. -/
theorem first_failure (t : Nat) (h : BB6Coverage.run machine t BB6Coverage.blank=none) :
    ∃ n, BB6Coverage.HaltsAfter machine n := by
  induction t with
  | zero => contradiction
  | succ t ih =>
    cases hprev : BB6Coverage.run machine t BB6Coverage.blank with
    | none => exact ih hprev
    | some d => exact ⟨t,⟨by simp [hprev],h⟩⟩

theorem exists_haltsAfter_of_not_never (h : ¬ BB6Coverage.NeverHalts machine) :
    ∃ n, BB6Coverage.HaltsAfter machine n := by
  classical
  unfold BB6Coverage.NeverHalts at h
  obtain ⟨t,ht⟩ := Classical.not_forall.mp h
  apply first_failure t
  cases hh : BB6Coverage.run machine t BB6Coverage.blank <;> simp_all

def terminalScore (i : Nat) := 8+arrivalCost (Cap.halt i)+score (Cap.halt i)

theorem terminal_haltsAfter {i : Nat} (hi : Cap.rootOf (Cap.halt i)=2) :
    BB6Coverage.HaltsAfter machine (terminalScore i-1) := by
  apply (exact_iff_haltsAfter _).mp
  have he : terminalScore i-1+1=terminalScore i := by unfold terminalScore; omega
  rw [he,exact_blank_iff]
  exact ⟨i,hi,rfl⟩

theorem never_iff_terminal_exclusion : BB6Coverage.NeverHalts machine ↔ ∀ i, Cap.rootOf (Cap.halt i)≠2 := by
  constructor
  · intro hn i hi
    have hh := terminal_haltsAfter hi
    have hs := hn (terminalScore i-1+1)
    rw [hh.2] at hs
    contradiction
  · intro ht
    classical
    by_cases h : BB6Coverage.NeverHalts machine
    · exact h
    · obtain ⟨n,hn⟩ := exists_haltsAfter_of_not_never h
      obtain ⟨i,hi,_⟩ := (haltsAfter_iff_terminal n).mp hn
      exact False.elim (ht i hi)

/-- Necessary and sufficient root-specific upper-bound obligation for #421. -/
theorem decidedBelow_iff_terminal_score (bound : Nat) :
    BB6Coverage.DecidedBelow bound machine ↔ ∀ i, Cap.rootOf (Cap.halt i)=2 → terminalScore i≤bound := by
  constructor
  · intro hd i hi
    have hh := terminal_haltsAfter hi
    rcases hd with hn|⟨n,hb,hh'⟩
    · have hs := hn (terminalScore i-1+1)
      rw [hh.2] at hs
      contradiction
    · have h1 := (exact_iff_haltsAfter _).mpr hh
      have h2 := (exact_iff_haltsAfter _).mpr hh'
      have he := exact_unique h1 h2
      have hpos : 0<terminalScore i := by unfold terminalScore; omega
      omega
  · intro ht
    classical
    by_cases h : BB6Coverage.NeverHalts machine
    · exact Or.inl h
    · obtain ⟨n,hn⟩ := exists_haltsAfter_of_not_never h
      obtain ⟨i,hi,he⟩ := (haltsAfter_iff_terminal n).mp hn
      exact Or.inr ⟨n,by rw [he]; exact ht i hi,hn⟩

/-- A simple sufficient bounded-terminal theorem for the actual coverage leaf. -/
theorem decidedBelow_of_terminal_bound (bound : Nat)
    (ht : ∀ i, Cap.rootOf (Cap.halt i)=2 → 8+800*(i+5)*4^i≤bound) :
    BB6Coverage.DecidedBelow bound machine := by
  apply (decidedBelow_iff_terminal_score bound).mpr
  intro i hi
  -- Apply the potential bound to the given terminal i.
  have he : Cap.halt i=Cap.lo i+(Cap.c i+1) := by unfold Cap.halt; omega
  have hp := arrival_potential ((Cap.root_iff_reach _).mp hi) i (Cap.c i+1) he (by omega)
  have hb := potential_end i (Cap.c i+1) (by omega)
  rw [←he] at hb
  have hf := bandPrefix_bound i
  unfold terminalScore
  have hb' := ht i hi
  omega

#print axioms run_rel
#print axioms haltsAfter_iff_terminal
#print axioms coverage_halt_bound
#print axioms never_iff_terminal_exclusion
#print axioms decidedBelow_iff_terminal_score
#print axioms decidedBelow_of_terminal_bound
end Counted421.Coverage
