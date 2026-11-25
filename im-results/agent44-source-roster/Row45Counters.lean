import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Row45
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Arbitrarily long live zipper prefixes imply nonhalting of every compatible completion. -/
theorem never_of_live (p : PartialMachine)
    (live : ∀ n, ∃ t z, n ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := live n
  have hz : (zrun p t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project p t BB6Coverage.Agent31Pump.start).trans hr
  cases h : zrun p t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z' =>
    have H := zrun_sound p m hm t BB6Coverage.Agent31Pump.start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

namespace Counter3
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, true, 3⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => if v then some (some ⟨false, false, 4⟩) else some (some ⟨false, false, 5⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => if v then some (some ⟨false, true, 5⟩) else some (some ⟨false, true, 4⟩)
  | 3, false => some (some ⟨true, false, 0⟩)
  | 3, true => some (some ⟨false, false, 3⟩)
  | 4, false => if v then some (some ⟨true, false, 1⟩) else some (some ⟨false, true, 2⟩)
  | 4, true => if v then some (some ⟨true, true, 4⟩) else none
  | 5, false => if v then some (some ⟨false, true, 2⟩) else some (some ⟨true, false, 1⟩)
  | 5, true => if v then none else some (some ⟨true, true, 5⟩)
  | _, _ => none

def enc : List Bool → List Bool
  | [] => [true]
  | b::w => b::false::enc w

def sectionCfg (w : List Bool) : Z0 := ⟨0, [false,false,false,false] ++ enc w, [false,false]⟩
def rr (k : Nat) : List Bool := true :: (rep [false,true] k ++ [false,true,false,false,false])

theorem enc_prefix (k : Nat) (w : List Bool) :
    enc (List.replicate k false ++ w) = rep [false,false] k ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, enc, rep, ih, List.nil_append]

theorem enter (v : Bool) (w : List Bool) :
    run0 (table v) 16 (sectionCfg w) = some ⟨1,enc w,rr 0⟩ := by cases v <;> rfl

theorem carryStep (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 2 ⟨1,true::false::L,rr k⟩ = some ⟨1,L,rr (k+1)⟩ := by cases v <;> rfl

theorem carryEnd (v : Bool) (k : Nat) :
    run0 (table v) 2 ⟨1,[true],rr k⟩ = some ⟨1,[],rr (k+1)⟩ := by cases v <;> rfl

theorem clearStep (v : Bool) (L R : List Bool) :
    run0 (table v) 2 ⟨2,true::L,[false,true]++R⟩ = some ⟨2,true::false::false::L,R⟩ := by cases v <;> rfl

theorem clearEnd (v : Bool) (L : List Bool) :
    run0 (table v) 5 ⟨2,true::L,[false,true,false,false,false]⟩ = some ⟨0,[false,false,false,false]++L,[false,false]⟩ := by cases v <;> rfl

theorem clear (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) (2*k+5) ⟨2,true::L,rep [false,true] k ++ [false,true,false,false,false]⟩ =
      some ⟨0,[false,false,false,false] ++ rep [false,false] k ++ L,[false,false]⟩ := by
  induction k generalizing L with
  | zero => exact clearEnd v L
  | succ k ih =>
    have h := join0 (clearStep v L (rep [false,true] k ++ [false,true,false,false,false])) (ih (false::false::L))
    rw [show 2 + (2*k+5) = 2*(k+1)+5 by omega] at h
    have hword : rep [false,false] k ++ ([false,false] ++ L) = [false,false] ++ (rep [false,false] k ++ L) := by
      rw [← List.append_assoc, rep_snoc, List.append_assoc]
    change run0 (table v) _ ⟨2,true::L,rep [false,true] (k+1) ++ [false,true,false,false,false]⟩ = some ⟨0,[false,false,false,false] ++ (rep [false,false] k ++ ([false,false] ++ L)),[false,false]⟩ at h
    rw [hword] at h
    exact h

theorem exitDigit (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 1 ⟨1,false::L,rr k⟩ = some ⟨2,true::true::L,rep [false,true] k ++ [false,true,false,false,false]⟩ := by cases v <;> rfl

theorem exitBlank (v : Bool) (k : Nat) :
    run0 (table v) 1 ⟨1,[],rr k⟩ = some ⟨2,[true,true],rep [false,true] k ++ [false,true,false,false,false]⟩ := by cases v <;> rfl

theorem finish (v : Bool) (k : Nat) (w : List Bool) :
    ∃ t w', 0 < t ∧ run0 (table v) t ⟨1,enc w,rr k⟩ = some (sectionCfg w') := by
  induction w generalizing k with
  | nil =>
    have h := join0 (join0 (carryEnd v k) (exitBlank v (k+1))) (clear v (k+1) [true])
    refine ⟨2+1+(2*(k+1)+5),List.replicate (k+1) false,by omega,?_⟩
    have hw := enc_prefix (k+1) []
    simp only [List.append_nil,enc] at hw
    simpa only [sectionCfg,hw,enc,List.append_assoc,List.nil_append] using h
  | cons b w ih =>
    cases b with
    | false =>
      have h := join0 (exitDigit v k (false::enc w)) (clear v k (true::false::enc w))
      refine ⟨1+(2*k+5),List.replicate k false ++ true::w,by omega,?_⟩
      simpa only [sectionCfg,enc_prefix,enc,List.append_assoc,List.nil_append] using h
    | true =>
      obtain ⟨t,w',ht,h⟩ := ih (k+1)
      exact ⟨_,w',by omega,join0 (carryStep v k (enc w)) h⟩

theorem next (v : Bool) (w : List Bool) :
    ∃ t w', 0 < t ∧ run0 (table v) t (sectionCfg w) = some (sectionCfg w') := by
  obtain ⟨t,w',ht,h⟩ := finish v 0 w
  exact ⟨_,w',by omega,join0 (enter v w) h⟩

theorem entry (v : Bool) : run0 (table v) 22 ⟨0,[],[]⟩ = some (sectionCfg []) := by cases v <;> rfl

theorem livePrefixes (v : Bool) (n : Nat) :
    ∃ t w, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sectionCfg w) := by
  induction n with
  | zero => exact ⟨22,[],by omega,entry v⟩
  | succ n ih =>
    obtain ⟨t,w,ht,hr⟩ := ih
    obtain ⟨c,w',hc,hs⟩ := next v w
    exact ⟨t+c,w',by omega,join0 hr hs⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply never_of_live (table v) (m := m) (hm := hm)
  intro n
  obtain ⟨t,w,ht,hr⟩ := livePrefixes v n
  exact ⟨t,sectionCfg w,ht,hr⟩

#print axioms never
end Counter3
namespace Counter5
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, true, 3⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => if v then some (some ⟨false, true, 4⟩) else some (some ⟨false, true, 5⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 2⟩)
  | 3, false => some (some ⟨true, false, 0⟩)
  | 3, true => some (some ⟨false, false, 3⟩)
  | 4, false => if v then some (some ⟨true, false, 4⟩) else some (some ⟨true, false, 1⟩)
  | 4, true => if v then some (some ⟨true, false, 5⟩) else none
  | 5, false => if v then some (some ⟨true, false, 1⟩) else some (some ⟨true, false, 5⟩)
  | 5, true => if v then none else some (some ⟨true, false, 4⟩)
  | _, _ => none

def enc : List Bool → List Bool
  | [] => [true]
  | b::w => b::enc w

def sectionCfg (w : List Bool) : Z0 := ⟨0, [false,false,false,false] ++ enc w, [false,false]⟩
def rr (k : Nat) : List Bool := true :: (rep [true] k ++ [true,true,true,false,false])

theorem enc_prefix (k : Nat) (w : List Bool) :
    enc (List.replicate k false ++ w) = rep [false] k ++ enc w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, enc, rep, ih, List.nil_append]

theorem enter (v : Bool) (w : List Bool) :
    run0 (table v) 16 (sectionCfg w) = some ⟨1,enc w,rr 0⟩ := by cases v <;> rfl

theorem carryStep (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 3 ⟨1,true::L,rr k⟩ = some ⟨1,L,rr (k+1)⟩ := by cases v <;> rfl

theorem carryEnd (v : Bool) (k : Nat) :
    run0 (table v) 3 ⟨1,[true],rr k⟩ = some ⟨1,[],rr (k+1)⟩ := by cases v <;> rfl

theorem clearStep (v : Bool) (L R : List Bool) :
    run0 (table v) 1 ⟨2,true::L,[true]++R⟩ = some ⟨2,true::false::L,R⟩ := by cases v <;> rfl

theorem clearEnd (v : Bool) (L : List Bool) :
    run0 (table v) 5 ⟨2,true::L,[true,true,true,false,false]⟩ = some ⟨0,[false,false,false,false]++L,[false,false]⟩ := by cases v <;> rfl

theorem clear (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) (1*k+5) ⟨2,true::L,rep [true] k ++ [true,true,true,false,false]⟩ =
      some ⟨0,[false,false,false,false] ++ rep [false] k ++ L,[false,false]⟩ := by
  induction k generalizing L with
  | zero => exact clearEnd v L
  | succ k ih =>
    have h := join0 (clearStep v L (rep [true] k ++ [true,true,true,false,false])) (ih (false::L))
    rw [show 1 + (1*k+5) = 1*(k+1)+5 by omega] at h
    have hword : rep [false] k ++ ([false] ++ L) = [false] ++ (rep [false] k ++ L) := by
      rw [← List.append_assoc, rep_snoc, List.append_assoc]
    change run0 (table v) _ ⟨2,true::L,rep [true] (k+1) ++ [true,true,true,false,false]⟩ = some ⟨0,[false,false,false,false] ++ (rep [false] k ++ ([false] ++ L)),[false,false]⟩ at h
    rw [hword] at h
    exact h

theorem exitDigit (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 1 ⟨1,false::L,rr k⟩ = some ⟨2,true::true::L,rep [true] k ++ [true,true,true,false,false]⟩ := by cases v <;> rfl

theorem exitBlank (v : Bool) (k : Nat) :
    run0 (table v) 1 ⟨1,[],rr k⟩ = some ⟨2,[true,true],rep [true] k ++ [true,true,true,false,false]⟩ := by cases v <;> rfl

theorem finish (v : Bool) (k : Nat) (w : List Bool) :
    ∃ t w', 0 < t ∧ run0 (table v) t ⟨1,enc w,rr k⟩ = some (sectionCfg w') := by
  induction w generalizing k with
  | nil =>
    have h := join0 (join0 (carryEnd v k) (exitBlank v (k+1))) (clear v (k+1) [true])
    refine ⟨3+1+(1*(k+1)+5),List.replicate (k+1) false,by omega,?_⟩
    have hw := enc_prefix (k+1) []
    simp only [List.append_nil,enc] at hw
    simpa only [sectionCfg,hw,enc,List.append_assoc,List.nil_append] using h
  | cons b w ih =>
    cases b with
    | false =>
      have h := join0 (exitDigit v k (enc w)) (clear v k (true::enc w))
      refine ⟨1+(1*k+5),List.replicate k false ++ true::w,by omega,?_⟩
      simpa only [sectionCfg,enc_prefix,enc,List.append_assoc,List.nil_append] using h
    | true =>
      obtain ⟨t,w',ht,h⟩ := ih (k+1)
      exact ⟨_,w',by omega,join0 (carryStep v k (enc w)) h⟩

theorem next (v : Bool) (w : List Bool) :
    ∃ t w', 0 < t ∧ run0 (table v) t (sectionCfg w) = some (sectionCfg w') := by
  obtain ⟨t,w',ht,h⟩ := finish v 0 w
  exact ⟨_,w',by omega,join0 (enter v w) h⟩

theorem entry (v : Bool) : run0 (table v) 22 ⟨0,[],[]⟩ = some (sectionCfg []) := by cases v <;> rfl

theorem livePrefixes (v : Bool) (n : Nat) :
    ∃ t w, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sectionCfg w) := by
  induction n with
  | zero => exact ⟨22,[],by omega,entry v⟩
  | succ n ih =>
    obtain ⟨t,w,ht,hr⟩ := ih
    obtain ⟨c,w',hc,hs⟩ := next v w
    exact ⟨t+c,w',by omega,join0 hr hs⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply never_of_live (table v) (m := m) (hm := hm)
  intro n
  obtain ⟨t,w,ht,hr⟩ := livePrefixes v n
  exact ⟨t,sectionCfg w,ht,hr⟩

#print axioms never
end Counter5
namespace Counter6
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 0, true => some (some ⟨true, true, 3⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => if v then some (some ⟨false, true, 4⟩) else some (some ⟨false, true, 5⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | 2, true => some (some ⟨false, true, 2⟩)
  | 3, false => some (some ⟨true, false, 0⟩)
  | 3, true => some (some ⟨false, false, 3⟩)
  | 4, false => if v then some (some ⟨true, false, 4⟩) else some (some ⟨true, false, 2⟩)
  | 4, true => if v then some (some ⟨true, false, 5⟩) else none
  | 5, false => if v then some (some ⟨true, false, 2⟩) else some (some ⟨true, false, 5⟩)
  | 5, true => if v then none else some (some ⟨true, false, 4⟩)
  | _, _ => none

def tailEnc : List Bool → List Bool
  | [] => []
  | b::w => false::false::false::b::true::tailEnc w

def scanEnc : List Bool → List Bool
  | [] => []
  | b::w => b::true::tailEnc w

def refillR (k : Nat) : List Bool := rep [false,true,true,true,true] k ++ [false,false]
def scanR (k : Nat) : List Bool := [true,true,true,true] ++ refillR k

def sectionCfg (b : Bool) (w : List Bool) (k : Nat) : Z0 :=
    ⟨0,[false,false,false,false] ++ scanEnc (b::w),refillR k⟩

theorem enter (v b : Bool) (w : List Bool) :
    run0 (table v) 16 (sectionCfg b w 0) = some ⟨2,scanEnc (b::w),scanR 0⟩ := by cases v <;> rfl

theorem borrow (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 13 ⟨2,false::true::false::false::false::L,scanR k⟩ =
      some ⟨2,L,scanR (k+1)⟩ := by cases v <;> rfl

theorem borrowLast (v : Bool) (k : Nat) :
    run0 (table v) 13 ⟨2,[false,true],scanR k⟩ = some ⟨2,[],scanR (k+1)⟩ := by cases v <;> rfl

theorem stop (v : Bool) (k : Nat) (w : List Bool) :
    run0 (table v) 6 ⟨2,scanEnc (true::w),scanR k⟩ = some (sectionCfg false w k) := by
  cases k <;> cases v <;> rfl

theorem underflow (v : Bool) (k : Nat) :
    run0 (table v) 8 ⟨2,[],scanR k⟩ = some (sectionCfg true [] k) := by
  cases k <;> cases v <;> rfl

theorem refillStep (v b : Bool) (w : List Bool) (k : Nat) :
    run0 (table v) 7 (sectionCfg b w (k+1)) = some (sectionCfg true (b::w) k) := by
  cases k <;> cases v <;> rfl

theorem refill (v : Bool) (k : Nat) (b : Bool) (w : List Bool) :
    ∃ b' w', run0 (table v) (7*k) (sectionCfg b w k) = some (sectionCfg b' w' 0) := by
  induction k generalizing b w with
  | zero => exact ⟨b,w,rfl⟩
  | succ k ih =>
    obtain ⟨b',w',h⟩ := ih true (b::w)
    refine ⟨b',w',?_⟩
    rw [show 7*(k+1)=7+7*k by omega]
    exact join0 (refillStep v b w k) h

theorem finish (v : Bool) (k : Nat) (w : List Bool) :
    ∃ t b' w', 0 < t ∧ run0 (table v) t ⟨2,scanEnc w,scanR k⟩ = some (sectionCfg b' w' 0) := by
  induction w generalizing k with
  | nil =>
    obtain ⟨b',w',h⟩ := refill v k true []
    exact ⟨8+7*k,b',w',by omega,join0 (underflow v k) h⟩
  | cons b w ih =>
    cases b with
    | true =>
      obtain ⟨b',w',h⟩ := refill v k false w
      exact ⟨6+7*k,b',w',by omega,join0 (stop v k w) h⟩
    | false =>
      obtain ⟨t,b',w',ht,h⟩ := ih (k+1)
      cases w with
      | nil => exact ⟨13+t,b',w',by omega,join0 (borrowLast v k) h⟩
      | cons b w =>
        exact ⟨13+t,b',w',by omega,join0 (borrow v k (scanEnc (b::w))) h⟩

theorem next (v b : Bool) (w : List Bool) :
    ∃ t b' w', 0 < t ∧ run0 (table v) t (sectionCfg b w 0) = some (sectionCfg b' w' 0) := by
  obtain ⟨t,b',w',ht,h⟩ := finish v 0 (b::w)
  exact ⟨16+t,b',w',by omega,join0 (enter v b w) h⟩

theorem entry (v : Bool) : run0 (table v) 24 ⟨0,[],[]⟩ = some (sectionCfg true [] 0) := by cases v <;> rfl

theorem livePrefixes (v : Bool) (n : Nat) :
    ∃ t b w, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sectionCfg b w 0) := by
  induction n with
  | zero => exact ⟨24,true,[],by omega,entry v⟩
  | succ n ih =>
    obtain ⟨t,b,w,ht,hr⟩ := ih
    obtain ⟨c,b',w',hc,hs⟩ := next v b w
    exact ⟨t+c,b',w',by omega,join0 hr hs⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply never_of_live (table v) (m := m) (hm := hm)
  intro n
  obtain ⟨t,b,w,ht,hr⟩ := livePrefixes v n
  exact ⟨t,sectionCfg b w 0,ht,hr⟩

#print axioms never
end Counter6

end BB6.Agent44Row45
