import Box33PrefixMacro

namespace BB6.Agent13.Box33D17V23Carry
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_succ rep_add cfg ones)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

inductive Variant where | m18 | m22 | m23 deriving DecidableEq

def step (v : Variant) (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .A false c)
  | .B,false => some (left .C true c)
  | .B,true => some (if v = .m22 then left .E false c else right .A false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => none
  | .E,false => some (left .F true c)
  | .E,true => some (right .E false c)
  | .F,false => some (right (if v = .m18 then .B else .A) true c)
  | .F,true => some (left .C false c)

abbrev run (v : Variant) := BB6.Agent13.Box33PrefixMacro.run (step v)
theorem run_add (v : Variant) (m n : Nat) (c : C9Pair.Config) :
    run v (m+n) c = (run v m c).bind (run v n) :=
  BB6.Agent13.Box33PrefixMacro.run_add (step v) m n c
abbrev A := word [false,true]
abbrev B := word [false,true,true]
abbrev C := word [false,false,true]
abbrev D := word [false,false,true,true]
abbrev E := word [false,false,false,true]
abbrev F := word [false,false,false,false,true]
abbrev G := word [false,false,false,false,false,true]
abbrev H := word [false,false,false,false,false,false,true]
abbrev ap := rep [false,true]
abbrev rp := rep [true,true,false,false]
abbrev r1 := word [true,false,false]
abbrev r2 := word [true,true,false,false]
abbrev r3 := word [true,true,true,false,false]
abbrev r4 := word [true,true,true,true,false,false]
abbrev r5 := word [true,true,true,true,true,false,false]
abbrev inc := push true
abbrev zeros := rep [false]
def phase (l r : Stream) := cfg .A l (word [false,false] r)
def Reach (v : Variant) (l r l' r' : Stream) : Prop :=
  ∃ t, run v t (phase l r) = some (phase l' r')
def Pos (v : Variant) (l r l' r' : Stream) : Prop :=
  ∃ t, 0<t ∧ run v t (phase l r) = some (phase l' r')
theorem Pos.reach {v l r l' r'} (h : Pos v l r l' r') : Reach v l r l' r' := by
  obtain ⟨t,_,h⟩ := h; exact ⟨t,h⟩
theorem Reach.refl (v) (l r : Stream) : Reach v l r l r := ⟨0,rfl⟩
theorem Reach.trans {v l r l' r' l'' r''}
    (h : Reach v l r l' r') (h' : Reach v l' r' l'' r'') : Reach v l r l'' r'' := by
  obtain ⟨n,hn⟩ := h; obtain ⟨m,hm⟩ := h'
  exact ⟨n+m,by rw [run_add,hn,Option.bind_some,hm]⟩
theorem Pos.trans {v l r l' r' l'' r''}
    (h : Pos v l r l' r') (h' : Reach v l' r' l'' r'') : Pos v l r l'' r'' := by
  obtain ⟨n,hp,hn⟩ := h; obtain ⟨m,hm⟩ := h'
  exact ⟨n+m,by omega,by rw [run_add,hn,Option.bind_some,hm]⟩

theorem raw0 (v) (l r : Stream) : Pos v (word [false,false,false] l) r (A l) (inc r) := by
  refine ⟨7,by decide,?_⟩
  cases v <;> simp [phase,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rawCA (v) (l r : Stream) : Pos v (C (A l)) r (push false l) (r1 (inc r)) := by
  refine ⟨8,by decide,?_⟩
  cases v <;> simp [phase,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rawCB (v) (l r : Stream) : Pos v (C (B l)) r (A l) (r1 (inc r)) := by
  refine ⟨8,by decide,?_⟩
  cases v <;> simp [phase,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rawD (v) (l r : Stream) : Pos v (D (A l)) r (A l) (r1 (inc r)) := by
  refine ⟨12,by decide,?_⟩
  cases v <;> simp [phase,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

-- The shared right-transfer prefix and the variable-length A1 sweep.
theorem pushEnter (v) (l r : Stream) :
    run v (if v=.m22 then 14 else 10) (phase (A l) (push true r)) =
      some (cfg .A (A (A l)) (push true r)) := by
  cases v <;> simp [phase,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aOne (v) (l r : Stream) : run v 1 (cfg .A l (push true r)) = some (cfg .A (push false l) r) := by
  simp [cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]
theorem aSweep (v) (n : Nat) (l r : Stream) :
    run v n (cfg .A l (ones n r)) = some (cfg .A (zeros n l) r) := by
  induction n generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ n ih =>
    rw [run_add,show ones (n+1) r = ones n (push true r) from rep_add [true] n 1 r,ih,Option.bind_some]
    exact aOne v (zeros n l) r

def Ready (l : Stream) : Prop := ∃ u, l=A u
theorem readyA (l : Stream) : Ready (A l) := ⟨l,rfl⟩
theorem readyB (l : Stream) : Ready (B l) := ⟨push true l,rfl⟩
theorem readyAP (k : Nat) (l : Stream) : Ready (ap (k+1) l) := ⟨ap k l,rfl⟩
theorem pushRun (v) (n : Nat) (l r : Stream) (h : Ready l) :
    Pos v l (ones (n+1) (word [false,false] r)) (zeros (n+2) (push true l)) r := by
  obtain ⟨u,rfl⟩ := h
  refine ⟨(if v=.m22 then 14 else 10)+(n+1),by split <;> omega,?_⟩
  rw [run_add]
  change ((run v (if v=.m22 then 14 else 10) (phase (A u) (push true (ones n (word [false,false] r))))).bind (run v (n+1))) = _
  rw [pushEnter,Option.bind_some]
  change run v (n+1) (cfg .A (A (A u)) (ones (n+1) (word [false,false] r))) = _
  rw [aSweep]
  have he : zeros (n+1) (A (A u)) = zeros (n+2) (push true (A u)) := by
    change zeros (n+1) (zeros 1 (push true (A u))) = _
    exact (rep_add [false] (n+1) 1 (push true (A u))).symm
  rw [he]
  rfl

theorem push1 (v) (l r : Stream) (h : Ready l) : Pos v l (r1 r) (C l) r := by
  exact pushRun v 0 l r h

theorem emit2 (v) (l r : Stream) (h : Ready l) : Reach v l (r2 r) (B l) (inc r) :=
  (pushRun v 1 l r h).reach.trans (raw0 v (push true l) r).reach

theorem emit3 (v) (l r : Stream) (h : Ready l) : Reach v l (r3 r) (A (A l)) (inc r) :=
  (pushRun v 2 l r h).reach.trans (raw0 v (A l) r).reach

theorem emit4 (v) (l r : Stream) (h : Ready l) : Reach v l (r4 r) (A (C l)) (inc r) :=
  (pushRun v 3 l r h).reach.trans (raw0 v (C l) r).reach

theorem emit5 (v) (l r : Stream) (h : Ready l) : Reach v l (r5 r) (A (E l)) (inc r) :=
  (pushRun v 4 l r h).reach.trans (raw0 v (E l) r).reach

theorem pop2 (v) (l r : Stream) (h : Ready l) : Reach v l (r2 r) (E l) r :=
  (pushRun v 1 l r h).reach

theorem pop3 (v) (l r : Stream) (h : Ready l) : Reach v l (r3 r) (F l) r :=
  (pushRun v 2 l r h).reach

theorem sweep (v) (k : Nat) (l r : Stream) :
    Pos v (C (ap (2*k+1) l)) r (push false l) (r1 (rp k (inc r))) := by
  induction k generalizing r with
  | zero => exact rawCA v l r
  | succ k ih =>
    have h := rawCA v (ap (2*k+2) l) r
    have h' := ih (r1 (inc r))
    change Pos v (C (ap (2*k+1) l)) (r1 (inc r)) (push false l) (r1 (rp k (r2 (inc r)))) at h'
    have he := h.trans h'.reach
    rw [show 2*(k+1)+1=(2*k+2)+1 by omega]
    change Pos v (C (A (ap (2*k+2) l))) r (push false l) (r1 (rp (k+1) (inc r)))
    rw [show rp (k+1) (inc r) = rp k (r2 (inc r)) from rep_add _ _ _ _]
    exact he

-- Drain a stack of 2-runs, with a carried increment on its leading run.
theorem drain3 (v) (k : Nat) (l r : Stream) (h : Ready l) :
    Reach v l (r3 (rp k r)) (ap (2*k) l) (r3 r) := by
  induction k generalizing l with
  | zero => exact Reach.refl v l (r3 r)
  | succ k ih =>
    have h0 := emit3 v l (rp (k+1) r) h
    change Reach v l (r3 (rp (k+1) r)) (A (A l)) (r3 (rp k r)) at h0
    have he := h0.trans (ih (A (A l)) (readyA _))
    rw [show 2*(k+1)=2*k+2 by omega]
    change Reach v l (r3 (rp (k+1) r)) (rep [false,true] (2*k+2) l) (r3 r)
    rw [rep_add]
    exact he

theorem drainCarry (v) (k : Nat) (l r : Stream) (h : Ready l) :
    Reach v l (inc (rp k r)) (ap (2*k) l) (inc r) := by
  induction k generalizing l with
  | zero => exact Reach.refl v l (inc r)
  | succ k ih =>
    have h0 := emit3 v l (rp k r) h
    have he := h0.trans (ih (A (A l)) (readyA _))
    rw [show 2*(k+1)=2*k+2 by omega]
    change Reach v l (r3 (rp k r)) (rep [false,true] (2*k+2) l) (inc r)
    rw [rep_add]
    exact he

-- Recursive tail grammar, with binary increment on its constructors.
inductive Tail where
  | nil
  | even (k : Nat) (w : Tail)
  | odd (k : Nat) (w : Tail)
mutual
  def W : Tail → Stream
    | .nil => z
    | .even k w => E (ap (2*k+1) (W w))
    | .odd k w => C (ap (2*k) (B (X w)))
  def X : Tail → Stream
    | .nil => A z
    | .even k w => ap (2*k+3) (W w)
    | .odd k w => B (ap (2*k) (B (X w)))
end

def next : Tail → Tail
  | .nil => .odd 0 .nil
  | .even k w => .odd (k+1) w
  | .odd k w => .even k (next w)

theorem readyX (w : Tail) : Ready (X w) := by
  cases w with
  | nil => exact readyA _
  | even k w => exact readyAP (2*k+2) _
  | odd k w => exact readyB _

theorem turnW (v) (w : Tail) (r : Stream) : Reach v (push false (W w)) r (X w) (inc r) := by
  cases w with
  | nil => simpa [W,X,word] using (raw0 v z r).reach
  | even k w => exact (raw0 v (A (ap (2*k+1) (W w))) r).reach
  | odd k w => exact (raw0 v (push true (ap (2*k) (B (X w)))) r).reach

-- The fundamental carry theorem; the suffix r is arbitrary, not a sampled tape.
theorem carry (v) (w : Tail) (r : Stream) :
    Reach v (X w) (r1 (r2 r)) (A (W (next w))) (inc r) := by
  induction w generalizing r with
  | nil =>
    exact (push1 v (A z) (r2 r) (readyA _)).reach.trans
      ((rawCA v z (r2 r)).reach.trans
        ((turnW v .nil (r1 (r3 r))).trans
          ((emit2 v (A z) (r3 r) (readyA _)).trans (emit4 v (B (A z)) r (readyB _)))))
  | even k w ih =>
    -- X = A^(2k+3) W; sweep all A pairs, turn, emit B and 2k+2 A blocks.
    have h0 := (push1 v (X (.even k w)) (r2 r) (readyX _)).reach
    have h1 := (sweep v (k+1) (W w) (r2 r)).reach
    change Reach v (C (X (.even k w))) (r2 r) (push false (W w)) (r1 (rp (k+1) (r3 r))) at h1
    have h2 := turnW v w (r1 (rp (k+1) (r3 r)))
    change Reach v (push false (W w)) (r1 (rp (k+1) (r3 r))) (X w) (r2 (rp (k+1) (r3 r))) at h2
    have h3 := emit2 v (X w) (rp (k+1) (r3 r)) (readyX _)
    change Reach v (X w) (r2 (rp (k+1) (r3 r))) (B (X w)) (r3 (rp k (r3 r))) at h3
    have h4 := drain3 v k (B (X w)) (r3 r) (readyB _)
    have h5 := emit3 v (ap (2*k) (B (X w))) (r3 r) (by
      cases k with
      | zero => exact readyB _
      | succ k => exact readyAP (2*k+1) _)
    change Reach v (ap (2*k) (B (X w))) (r3 (r3 r)) (A (A (ap (2*k) (B (X w))))) (r4 r) at h5
    have h6 := emit4 v (ap (2*(k+1)) (B (X w))) r (readyAP (2*k+1) _)
    change Reach v (A (A (ap (2*k) (B (X w))))) (r4 r) (A (W (next (.even k w)))) (inc r) at h6
    exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))
  | odd k w ih =>
    have h0 := (push1 v (X (.odd k w)) (r2 r) (readyX _)).reach
    have h1 := (rawCB v (ap (2*k) (B (X w))) (r2 r)).reach
    change Reach v (C (X (.odd k w))) (r2 r) (ap (2*k+1) (B (X w))) (r1 (r3 r)) at h1
    have hr : Ready (ap (2*k+1) (B (X w))) := readyAP _ _
    have h2 := (push1 v _ (r3 r) hr).reach
    have h3 := (sweep v k (B (X w)) (r3 r)).reach
    change Reach v (C (ap (2*k+1) (B (X w)))) (r3 r) (D (X w)) (r1 (rp k (r4 r))) at h3
    obtain ⟨u,hu⟩ := readyX w
    have h4 : Reach v (D (X w)) (r1 (rp k (r4 r))) (X w) (r1 (rp (k+1) (r4 r))) := by
      rw [hu]
      exact (rawD v u _).reach
    have h5 := ih (rp k (r4 r))
    have h6 : Reach v (A (W (next w))) (inc (rp k (r4 r))) (ap (2*k+1) (W (next w))) (r5 r) := by
      have he := drainCarry v k (A (W (next w))) (r4 r) (readyA _)
      change Reach v (A (W (next w))) (inc (rp k (r4 r))) (rep [false,true] (2*k+1) (W (next w))) (r5 r)
      rw [rep_add]
      exact he
    have h7 := emit5 v (ap (2*k+1) (W (next w))) r (readyAP _ _)
    change Reach v (ap (2*k+1) (W (next w))) (r5 r) (A (W (next (.odd k w)))) (inc r) at h7
    exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))

def root (k : Nat) (w : Tail) : Stream := C (ap (2*k+1) (W w))

theorem firstPhase (v) (k : Nat) (w : Tail) :
    Pos v (root k w) z (E (ap (2*k) (B (X w)))) z := by
  have h0 := sweep v k (W w) z
  have h1 := turnW v w (r1 (rp k (inc z)))
  change Reach v (push false (W w)) (r1 (rp k (inc z))) (X w) (r2 (rp k (inc z))) at h1
  have h2 := emit2 v (X w) (rp k (inc z)) (readyX _)
  have h3 := drainCarry v k (B (X w)) (inc z) (readyB _)
  have h4 := pop2 v (ap (2*k) (B (X w))) z (by
    cases k with
    | zero => exact readyB _
    | succ k => exact readyAP (2*k+1) _)
  have hz : inc (inc z) = r2 z := by simp [word]
  rw [hz] at h3
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem secondPhase (v) (l : Stream) : Reach v (E l) z (C (B l)) z := by
  have h := (raw0 v (push true l) z).reach
  have h' := (push1 v (B l) z (readyB _)).reach
  have hz : inc z = r1 z := by simp [word]
  rw [hz] at h
  exact h.trans h'

theorem thirdPhase (v) (k : Nat) (w : Tail) :
    Reach v (C (B (ap (2*k) (B (X w))))) z (F (ap (2*k+1) (W (next w)))) z := by
  have h0 := (rawCB v (ap (2*k) (B (X w))) z).reach
  have h1 := (push1 v (ap (2*k+1) (B (X w))) (inc z) (readyAP _ _)).reach
  have h2 := (sweep v k (B (X w)) (inc z)).reach
  have hz : inc (inc z) = r2 z := by simp [word]
  rw [hz] at h2
  have hrp : rp k (r2 z) = rp (k+1) z := (rep_add [true,true,false,false] k 1 z).symm
  rw [hrp] at h2
  obtain ⟨u,hu⟩ := readyX w
  have h3 : Reach v (D (X w)) (r1 (rp (k+1) z)) (X w) (r1 (rp (k+2) z)) := by
    rw [hu]
    exact (rawD v u _).reach
  have h4 := carry v w (rp (k+1) z)
  have h5 := drain3 v k (A (W (next w))) z (readyA _)
  have h6 := pop3 v (ap (2*k+1) (W (next w))) z (readyAP _ _)
  have he : ap (2*k+1) (W (next w)) = ap (2*k) (A (W (next w))) := rep_add _ _ _ _
  rw [←he] at h5
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))

theorem fourthPhase (v) (k : Nat) (w : Tail) : Reach v (F (ap (2*k+1) (W w))) z (root (k+1) w) z := by
  have h0 := (raw0 v (A (ap (2*k+1) (W w))) z).reach
  have h1 := (push1 v (ap (2*(k+1)+1) (W w)) z (readyAP _ _)).reach
  have hz : inc z = r1 z := by simp [word]
  rw [hz] at h0
  have he : ap (2*(k+1)+1) (W w) = A (A (ap (2*k+1) (W w))) := by
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega]
    rfl
  rw [he] at h1
  exact h0.trans h1

theorem epoch (v) (k : Nat) (w : Tail) : Pos v (root k w) z (root (k+1) (next w)) z :=
  (firstPhase v k w).trans ((secondPhase v _).trans ((thirdPhase v k w).trans (fourthPhase v k (next w))))

theorem init (v) : Pos v z z (root 0 .nil) z := by
  have h := (raw0 v z z)
  have h' := (push1 v (A z) z (readyA _)).reach
  have hz : inc z = r1 z := by simp [word]
  rw [hz] at h
  simpa [root,W,ap,rep,word] using h.trans h'

theorem neverRoot (v) (n k : Nat) (w : Tail) : run v n (phase (root k w) z) ≠ none := by
  induction n using Nat.strongRecOn generalizing k w with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,he⟩ := epoch v k w
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih (n-t) (by omega) (k+1) (next w) h

theorem neverBlank (v) (n : Nat) : run v n (phase z z) ≠ none := by
  intro h
  obtain ⟨t,ht,he⟩ := init v
  by_cases hn : n≤t
  · rw [←show n+(t-n)=t by omega,run_add,h] at he
    contradiction
  · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
    exact neverRoot v (n-t) 0 .nil h

open BB6Coverage
open Box17 (index decode)
def codes : Variant → List (Fin 25)
  | .m18 => [8,2,11,2,1,13,17,0,23,18,8,9]
  | .m22 => [8,2,11,17,1,13,17,0,23,18,4,9]
  | .m23 => [8,2,11,2,1,13,17,0,23,18,4,9]
def table (v : Variant) : Machine := fun s => decode ((codes v).getD (index s).val 0)
theorem project_step (v : Variant) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map BB6.Agent13.Box33PrefixMacro.project = step v (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases v <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never (v : Variant) : NeverHalts (table v) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table v) (step v) (project_step v)
  intro n
  exact neverBlank v n
def partialTable (v : Variant) : PartialMachine := fun s => some (table v s)
theorem compatible_never (v : Variant) (m : Machine) (hm : compatible (partialTable v) m) : NeverHalts m := by
  have he : m = table v := funext fun s => hm s _ rfl
  rw [he]
  exact never v

#print axioms carry
#print axioms epoch
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V23Carry
