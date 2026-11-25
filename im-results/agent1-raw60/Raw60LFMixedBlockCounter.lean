import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFMixedBlockCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨v,false,if v then 4 else 5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev C := Q 2
abbrev D := Q 3
abbrev Z (n : Nat) := List.replicate n false
abbrev B : List Bool := [true,true,true,true,false]
abbrev H : List Bool := [false,true,true,true,false]
abbrev J : List Bool := [true,true,false,false]
abbrev V : List Bool := [true,true,false,true,false]
abbrev I : List Bool := [true,true,true,false]
abbrev E : List Bool := [true,true,true,true,true]
abbrev P : List Bool := [false,false,true,true,true,true]
abbrev pad : List Bool := [false,false]

def rep (w : List Bool) : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => w++rep w n R

theorem repEnd (w : List Bool) (n : Nat) (R : List Bool) : rep w n (w++R)=rep w (n+1) R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih]

def enc : List Bool → List Bool
  | [] => E
  | b::bs => (if b then B else H)++enc bs

def W (n : Nat) (s : List Bool) := U (2*n+3)++false::(B++enc s)

theorem encFalse (k : Nat) (s : List Bool) : enc (List.replicate k false++s)=rep H k (enc s) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih]; rfl

theorem zmerge (a b : Nat) (R : List Bool) : Z a++(Z b++R)=Z (a+b)++R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem cSweep (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) n (C (true::L) (U n++R)) = some (C (true::(Z n++L)) R) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (C (true::L) (U (n+1)++R)) = some (C (true::false::L) (U n++R)) := by cases v <;> rfl
    have H := join0 h (ih (false::L))
    have he : Z n++false::L=Z (n+1)++L := by
      change Z n++(Z 1++L)=_
      rw [zmerge]
    rw [he,Nat.add_comm 1 n] at H
    exact H


theorem unpackLoop (v : Bool) (k : Nat) (L R : List Bool) : Reach (table v) (F (false::rep B k L) (I++R)) (F (false::L) (I++rep H k R)) := by
  induction k generalizing R with
  | zero => exact ⟨0,by rfl⟩
  | succ k ih =>
    have h1 : run0 (table v) 5 (F (false::rep B (k+1) L) (I++R)) = some (F (false::rep B k L) (I++(H++R))) := by cases v <;> rfl
    have h2 := ih (H++R)
    rw [repEnd H k R] at h2
    exact reachTrans ⟨5,h1⟩ h2

theorem finish (v : Bool) (k : Nat) (L : List Bool) (s : List Bool) : Reach (table v) (F (false::rep B k (J++L)) (I++enc s)) (F L (W 0 (List.replicate k false++s))) := by
  obtain ⟨a,ha⟩ := unpackLoop v k (J++L) (enc s)
  have hb : run0 (table v) 17 (F (false::(J++L)) (I++rep H k (enc s))) = some (F L (I++(B++rep H k (enc s)))) := by cases v <;> rfl
  have he : W 0 (List.replicate k false++s) = I++(B++rep H k (enc s)) := by simp only [W,encFalse]; rfl
  rw [he]
  exact reachTrans ⟨a,ha⟩ ⟨17,hb⟩

def packCost (v : Bool) := if v then 21 else 19

theorem process (v : Bool) (s : List Bool) (k : Nat) (L : List Bool) : ∃ s', Reach (table v) (F (Z 3++rep B k (J++L)) (true::false::enc s)) (F L (W 0 s')) := by
  induction s generalizing k with
  | nil =>
    have h : run0 (table v) 53 (F (Z 3++rep B k (J++L)) (true::false::enc [])) = some (F (false::rep B (k+1) (J++L)) (I++enc [])) := by cases v <;> rfl
    exact ⟨_,reachTrans ⟨53,h⟩ (finish v (k+1) L [])⟩
  | cons b s ih =>
    cases b with
    | false =>
      have h : run0 (table v) 14 (F (Z 3++rep B k (J++L)) (true::false::enc (false::s))) = some (F (false::rep B k (J++L)) (I++enc (true::s))) := by cases v <;> rfl
      exact ⟨_,reachTrans ⟨14,h⟩ (finish v k L (true::s))⟩
    | true =>
      have h : run0 (table v) (packCost v) (F (Z 3++rep B k (J++L)) (true::false::enc (true::s))) = some (F (Z 3++rep B (k+1) (J++L)) (true::false::enc s)) := by cases v <;> rfl
      obtain ⟨s',hs⟩ := ih (k+1)
      exact ⟨s',reachTrans ⟨packCost v,h⟩ hs⟩

def startCost (v : Bool) := if v then 11 else 9

theorem clear (v : Bool) (n : Nat) (s : List Bool) (L : List Bool) : ∃ s' t, 2≤t ∧ run0 (table v) t (F (pad++L) (W n s)) = some (F (Z (2*n)++true::true::L) (W 0 s')) := by
  have h1 : run0 (table v) 3 (F (pad++L) (W n s)) = some (C (true::true::true::L) (U (2*n+2)++false::(B++enc s))) := by cases v <;> rfl
  have h2 := cSweep v (2*n+2) (true::true::L) (false::(B++enc s))
  have h3 : run0 (table v) 7 (C (true::(Z (2*n+2)++true::true::L)) (false::(B++enc s))) = some (F (Z (2*n+4)++true::true::L) (V++enc s)) := by cases v <;> rfl
  have h4 : run0 (table v) (startCost v) (F (Z (2*n+4)++true::true::L) (V++enc s)) = some (F (Z 3++(J++(Z (2*n)++true::true::L))) (true::false::enc s)) := by cases v <;> rfl
  obtain ⟨s',a,ha⟩ := process v s 0 (Z (2*n)++true::true::L)
  exact ⟨s',_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) ha⟩

def Inc (v : Bool) (n : Nat) : Prop := ∀ s L, ∃ s' t, 2≤t ∧ run0 (table v) t (F (pad++L) (W n s)) = some (F L (W (n+1) s'))

theorem chain (v : Bool) (d j : Nat) (s : List Bool) (L : List Bool) (h : ∀ i, j≤i → i<j+d → Inc v i) :
    ∃ s', Reach (table v) (F (Z (2*d)++L) (W j s)) (F L (W (j+d) s')) := by
  induction d generalizing j s with
  | zero => exact ⟨s,0,by rfl⟩
  | succ d ih =>
    obtain ⟨s',t,_,ht⟩ := h j (by omega) (by omega) s (Z (2*d)++L)
    obtain ⟨s'',h2⟩ := ih (j+1) s' (fun i hi hi' => h i (by omega) (by omega))
    rw [show j+1+d=j+(d+1) by omega] at h2
    exact ⟨s'',reachTrans ⟨t,ht⟩ h2⟩

theorem inc (v : Bool) (n : Nat) : Inc v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s L
    obtain ⟨s',a,apos,h1⟩ := clear v n s L
    obtain ⟨s'',b,h2⟩ := chain v n 0 s' (true::true::L) (fun i _ hi => ih i (by omega))
    rw [Nat.zero_add] at h2
    have h3 : run0 (table v) 2 (F (true::true::L) (W n s'')) = some (F L (W (n+1) s'')) := by cases v <;> rfl
    exact ⟨s'',_,by omega,join0 (join0 h1 h2) h3⟩

theorem firstEq (v : Bool) (R : List Bool) : run0 (table v) 2 (F [] R)=run0 (table v) 2 (F pad R) := by cases v <;> cases R <;> rfl

theorem transfer (v : Bool) (R : List Bool) (t : Nat) (h : 2≤t) (c : Z0)
    (hr : run0 (table v) t (F pad R)=some c) : run0 (table v) t (F [] R)=some c := by
  have ht : t=2+(t-2) := by omega
  rw [ht,run0_add,firstEq,←run0_add,←ht]
  exact hr

theorem advance (v : Bool) (n : Nat) (s : List Bool) : ∃ s' t, 0<t ∧ run0 (table v) t (F [] (W n s)) = some (F [] (W (n+1) s')) := by
  obtain ⟨s',t,hpos,h⟩ := inc v n s []
  exact ⟨s',t,by omega,transfer v _ _ hpos _ h⟩
noncomputable def nextS (v : Bool) (n : Nat) (s : List Bool) := Classical.choose (advance v n s)
noncomputable def size (v : Bool) : Nat → List Bool
  | 0 => []
  | n+1 => nextS v (n+3) (size v n)
noncomputable def family (v : Bool) (n : Nat) := F [] (W (n+3) (size v n))
theorem entry (v : Bool) : run0 (table v) 179 ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem growth_exists (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  have h := Classical.choose_spec (advance v (n+3) (size v n))
  have he : n+3+1=n+1+3 := by omega
  change ∃ t, 0<t ∧ run0 (table v) t (F [] (W (n+3) (size v n))) = some (F [] (W (n+1+3) (size v (n+1))))
  rw [←he]
  exact h
noncomputable def cost (v : Bool) (n : Nat) : Nat := Classical.choose (growth_exists v n)
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) 179 (cost v) (entry v) (fun n => (Classical.choose_spec (growth_exists v n)).1)
    (fun n => (Classical.choose_spec (growth_exists v n)).2) m hm
#print axioms never

namespace V986
def table := BB6.Agent1Raw60LFMixedBlockCounter.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LFMixedBlockCounter.never false m hm
end V986
namespace V989
def table := BB6.Agent1Raw60LFMixedBlockCounter.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent1Raw60LFMixedBlockCounter.never true m hm
end V989
end BB6.Agent1Raw60LFMixedBlockCounter
