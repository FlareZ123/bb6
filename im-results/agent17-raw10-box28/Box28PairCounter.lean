import Box33BinaryCounter
namespace BB6.Agent17.Box28PairCounter
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)

def step (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .E true c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true | .C,true => some (left .D false c)
  | .D,false => some (right .A false c)
  | .D,true => some (left .F true c)
  | .E,false => some (right .A true c)
  | .E,true => none
  | .F,false => some (right .A false c)
  | .F,true => some (left .F false c)

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [run]
    cases step c <;> simp [ih]

def pair (a b : Bool) (s : Stream) : Stream := push a (push b s)
def root (k : Nat) (s : Stream) : Config := ⟨.A,ones (2*k),s 0,pop s⟩
def fSweep (n : Nat) (r : Stream) : Config := ⟨.F,ones n,true,r⟩

theorem root01_zero (s : Stream) : run 6 (root 0 (pair false true s)) = some (root 1 s) := by
  simp [run,step,root,pair,ones,rep,right,left]

theorem root01_enter (k : Nat) (s : Stream) :
    run 3 (root (k+1) (pair false true s)) = some (fSweep (2*k+1) (pair true false s)) := by
  simp only [root,show 2*(k+1)=2*k+2 by omega]; rfl

theorem root10 (k : Nat) (s : Stream) : run 2 (root k (pair true false s)) = some (root (k+1) s) := by
  simp only [root,show 2*(k+1)=2*k+2 by omega]; rfl

theorem root00_zero (s : Stream) : run 4 (root 0 (pair false false s)) = some (root 0 (pair false true s)) := by
  simp [run,step,root,pair,ones,rep,right,left]

theorem root00_enter (k : Nat) (s : Stream) :
    run 4 (root (k+1) (pair false false s)) = some (fSweep (2*k) (push true (pair false true s))) := by
  simp only [root,show 2*(k+1)=2*k+2 by omega]; rfl

theorem f_step (n : Nat) (r : Stream) : run 1 (fSweep (n+1) r) = some (fSweep n (push false r)) := by rfl

theorem rep_push (n : Nat) (r : Stream) : rep false n (push false r) = rep false (n+1) r := by rw [rep_add]; rfl

theorem f_sweep (n : Nat) (r : Stream) : run n (fSweep n r) = some (fSweep 0 (rep false n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add,show 1+n=n+1 by omega,f_step,Option.bind_some,ih,rep_push]

theorem f_end (r : Stream) : run 2 (fSweep 0 r) = some (root 0 (push false r)) := by
  simp [run,step,fSweep,root,right,left,ones,rep]

theorem root00_sweep (k : Nat) (s : Stream) :
    run (4+2*k+2) (root (k+1) (pair false false s)) =
      some (root 0 (rep false (2*k) (pair false true (pair false true s)))) := by
  rw [run_add,run_add,root00_enter,Option.bind_some,f_sweep,Option.bind_some,f_end]
  rw [←show rep false (2*k+1) (push true (pair false true s)) = push false (rep false (2*k) (push true (pair false true s))) from rfl, ←rep_push]
  rfl

theorem root01_sweep (k : Nat) (s : Stream) :
    run (3+(2*k+1)+2) (root (k+1) (pair false true s)) =
      some (root 0 (rep false (2*k+2) (pair true false s))) := by
  rw [run_add,run_add,root01_enter,Option.bind_some,f_sweep,Option.bind_some,f_end]
  rfl

-- The aligned two-bit digit 11 is forbidden, regardless of the tape length.
def Good (s : Stream) : Prop := ∀ i, s (2*i) = false ∨ s (2*i+1) = false

theorem pair_good (a b : Bool) (s : Stream) : Good (pair a b s) ↔ (a=false ∨ b=false) ∧ Good s := by
  constructor
  · intro h
    refine ⟨h 0,?_⟩
    intro i
    have hh := h (i+1)
    simpa only [show 2*(i+1)=2*i+2 by omega,show 2*(i+1)+1=(2*i+1)+2 by omega,pair,push] using hh
  · rintro ⟨h0,h⟩ i
    cases i with
    | zero => exact h0
    | succ i =>
      simpa only [show 2*(i+1)=2*i+2 by omega,show 2*(i+1)+1=(2*i+1)+2 by omega,pair,push] using h i

theorem pad_good (k : Nat) (s : Stream) (h : Good s) : Good (rep false (2*k) s) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,rep_add]
    exact (pair_good false false _).2 ⟨Or.inl rfl,ih⟩

theorem split (s : Stream) : s = pair (s 0) (s 1) (pop (pop s)) := by
  funext i; cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem progress (k : Nat) (s : Stream) (h : Good s) :
    ∃ n k' s', 0<n ∧ run n (root k s) = some (root k' s') ∧ Good s' := by
  obtain ⟨h0,ht⟩ := (pair_good (s 0) (s 1) (pop (pop s))).1 (by rw [←split]; exact h)
  have hs := split s
  generalize hA : s 0 = a at h0 hs
  generalize hB : s 1 = b at h0 hs
  let t := pop (pop s)
  change s=pair a b t at hs
  change Good t at ht
  cases a <;> cases b
  · cases k with
    | zero => exact ⟨4,0,pair false true t,by decide,by rw [hs,root00_zero],(pair_good false true t).2 ⟨Or.inl rfl,ht⟩⟩
    | succ k =>
      refine ⟨4+2*k+2,0,rep false (2*k) (pair false true (pair false true t)),by omega,?_,?_⟩
      · rw [hs,root00_sweep]
      · exact pad_good k _ ((pair_good false true _).2 ⟨Or.inl rfl,(pair_good false true _).2 ⟨Or.inl rfl,ht⟩⟩)
  · cases k with
    | zero => exact ⟨6,1,t,by decide,by rw [hs,root01_zero],ht⟩
    | succ k =>
      refine ⟨3+(2*k+1)+2,0,rep false (2*k+2) (pair true false t),by omega,?_,?_⟩
      · rw [hs,root01_sweep]
      · rw [show 2*k+2=2*(k+1) by omega]
        exact pad_good (k+1) _ ((pair_good true false _).2 ⟨Or.inr rfl,ht⟩)
  · exact ⟨2,k+1,t,by decide,by rw [hs,root10],ht⟩
  · simp at h0

theorem never_root (n k : Nat) (s : Stream) (hg : Good s) : run n (root k s) ≠ none := by
  induction n using Nat.strongRecOn generalizing k s with
  | ind n ih =>
    intro h
    obtain ⟨j,k',s',hj,hs,hg'⟩ := progress k s hg
    by_cases hn : n ≤ j
    · have e : j=n+(j-n) := by omega
      rw [e,run_add,h] at hs; contradiction
    · have e : n=j+(n-j) := by omega
      rw [e,run_add,hs] at h
      exact ih _ (by omega) k' s' hg' h

theorem never_blank (n : Nat) : run n ⟨.A,zeros,false,zeros⟩ ≠ none :=
    never_root n 0 zeros (fun _ => Or.inl rfl)
#print axioms never_blank
end BB6.Agent17.Box28PairCounter
