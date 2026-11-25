import PhaseClosure
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace BB6.Agent3Raw120OneRAParity
open BB6Coverage BB6Coverage.Agent31Pump

/-- Leaf 437, only C1 unassigned. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true

theorem onesJoin (a b : Nat) (L : List Bool) : O a++(O b++L)=O (a+b)++L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

theorem onesSnoc (n : Nat) (L : List Bool) : O n++true::L=O (n+1)++L := by
  exact onesJoin n 1 L

theorem onesFront (n : Nat) (L : List Bool) : O n++true::L=true::(O n++L) := by
  rw [onesSnoc]
  rfl

/-- All internal runs are odd; the terminal (furthest-left) run may be arbitrary. -/
inductive Stack where
  | nil
  | bottom (k : Nat)
  | odd (a : Nat) (tail : Stack)
  deriving Repr

def stack : Stack → List Bool
  | .nil => []
  | .bottom k => false::O (k+1)
  | .odd a xs => false::(O (2*a+1)++stack xs)

theorem stackHead (xs : Stack) : (stack xs).headD false=false := by cases xs <;> rfl

/-- Right runs have the same odd-internal condition; terminal length can be zero. -/
inductive Right where
  | last (n : Nat)
  | odd (a : Nat) (tail : Right)
  deriving Repr

def word : Right → List Bool
  | .last n => O n
  | .odd a r => O (2*a+1)++false::word r

def prependPairs : Nat → Right → Right
  | 0,r => r
  | n+1,r => prependPairs n (.odd 0 r)

/-- The sole exception is the fresh left boundary's first scanned run.
    It may be even or zero; all subsequent internal runs remain odd. -/
inductive Good : Z0 → Prop where
  | normal (xs : Stack) (r : Right) : Good ⟨0,stack xs,word r⟩
  | rootScan (m : Nat) (r : Right) : Good ⟨0,[],true::false::(O m++false::word r)⟩

-- Left-return phase. Every local equation has arbitrary uninspected tails.
theorem pairStep (L R : List Bool) :
    run0 table 2 ⟨0,true::true::L,R⟩ = some ⟨0,L,true::false::R⟩ := by rfl

theorem pairSweep (a : Nat) (L : List Bool) (r : Right) :
    run0 table (2*a) ⟨0,O (2*a)++L,word r⟩ =
      some ⟨0,L,word (prependPairs a r)⟩ := by
  induction a generalizing r with
  | zero => rfl
  | succ a ih =>
    have H := join0 (pairStep (O (2*a)++L) (word r)) (ih (.odd 0 r))
    rw [show 2*(a+1)=2*a+2 by omega,show 2*a+2=2+2*a by omega]
    rw [show 2+2*a=2*a+1+1 by omega]
    simpa only [List.replicate_succ,List.cons_append,prependPairs,show 2+(2*a)=2*a+1+1 by omega] using H

theorem oddToE (L R : List Bool) (h : L.headD false=false) :
    run0 table 2 ⟨0,true::L,R⟩ = some ⟨4,L.tail,true::false::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

theorem eSweep (n : Nat) (L R : List Bool) :
    run0 table n ⟨4,O n++L,R⟩ = some ⟨4,L,O n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 ⟨4,true::(O n++L),R⟩ = some ⟨4,O n++L,true::R⟩ := by rfl
    have H := join0 h (ih (true::R))
    rw [show 1+n=n+1 by omega,onesFront] at H
    exact H

theorem exitE (L R : List Bool) (h : L.headD false=false) :
    run0 table 3 ⟨4,L,true::R⟩ = some ⟨0,L.tail,true::false::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

theorem eReturn (n : Nat) (L R : List Bool) (h : L.headD false=false) :
    run0 table (n+3) ⟨4,O n++L,true::R⟩ =
      some ⟨0,L.tail,true::false::(O n++R)⟩ := by
  have h1 := eSweep n L (true::R)
  rw [onesFront] at h1
  exact join0 h1 (exitE L (O n++R) h)

/-- A leftward return can start with an arbitrary top run. It then removes
    two normal stack frames per recursive call. Zero cost is allowed only
    for this auxiliary lemma; every complete phase below has positive cost. -/
theorem retA (xs : Stack) (k : Nat) (r : Right) :
    ∃ time d, run0 table time ⟨0,O k++stack xs,word r⟩=some d ∧ Good d := by
  let a := k/2
  have hk : k=2*a ∨ k=2*a+1 := by dsimp [a]; omega
  rcases hk with hk|hk
  · rw [hk]
    exact ⟨2*a,_,pairSweep a (stack xs) r,Good.normal xs (prependPairs a r)⟩
  · have h1 := pairSweep a (true::stack xs) r
    rw [onesSnoc,← hk] at h1
    have h2 := oddToE (stack xs) (word (prependPairs a r)) (stackHead xs)
    have H := join0 h1 h2
    cases xs with
    | nil =>
      have h3 := eReturn 0 [] (false::word (prependPairs a r)) (by rfl)
      exact ⟨_,_,join0 H h3,Good.rootScan 0 (prependPairs a r)⟩
    | bottom b =>
      have h3 := eReturn (b+1) [] (false::word (prependPairs a r)) (by rfl)
      have h3' : run0 table (b+1+3) ⟨4,O (b+1),true::false::word (prependPairs a r)⟩ =
          some ⟨0,[],true::false::(O (b+1)++false::word (prependPairs a r))⟩ := by
        simpa only [List.append_nil,List.tail_nil] using h3
      exact ⟨_,_,join0 H h3',Good.rootScan (b+1) (prependPairs a r)⟩
    | odd b ys =>
      have h3 := eReturn (2*b+1) (stack ys) (false::word (prependPairs a r)) (stackHead ys)
      have H' := join0 H h3
      let r' := Right.odd 0 (.odd b (prependPairs a r))
      cases ys with
      | nil => exact ⟨_,_,H',Good.normal .nil r'⟩
      | bottom c =>
        obtain ⟨t,d,ht,hd⟩ := retA .nil (c+1) r'
        have ht' : run0 table t ⟨0,O (c+1),word r'⟩=some d := by
          simpa only [stack,List.append_nil] using ht
        exact ⟨_,d,join0 H' ht',hd⟩
      | odd c zs =>
        obtain ⟨t,d,ht,hd⟩ := retA zs (2*c+1) r'
        exact ⟨_,d,join0 H' ht,hd⟩
termination_by sizeOf xs
decreasing_by all_goals simp_wf; omega

theorem retTail (xs : Stack) (r : Right) :
    ∃ time d, run0 table time ⟨0,(stack xs).tail,word r⟩=some d ∧ Good d := by
  cases xs with
  | nil => exact ⟨0,_,rfl,Good.normal .nil r⟩
  | bottom k =>
    simpa only [stack,List.tail_cons,List.append_nil] using retA .nil (k+1) r
  | odd a xs => exact retA xs (2*a+1) r

-- Right scan: move an entire run, then push a new singleton frame.
theorem consume (L R : List Bool) (h : L.headD false=false) :
    run0 table 5 ⟨0,L,true::false::true::R⟩ =
      some ⟨0,false::true::L.tail,true::false::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

def suffix : Option (List Bool) → List Bool
  | none => []
  | some R => false::R

theorem pushLocal (L : List Bool) (R : Option (List Bool)) (h : L.headD false=false) :
    run0 table 3 ⟨0,L,true::false::suffix R⟩ =
      some ⟨0,false::true::false::true::L.tail,R.getD []⟩ := by
  cases L with
  | nil => cases R <;> rfl
  | cons b L => cases b <;> cases R <;> simp_all <;> rfl

theorem pushOne (L : List Bool) (h : L.headD false=false) :
    run0 table 3 ⟨0,L,[true]⟩ = some ⟨0,false::true::false::true::L.tail,[]⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

theorem scanPush (m : Nat) (L : List Bool) (R : Option (List Bool)) (h : L.headD false=false) :
    run0 table (5*m+3) ⟨0,L,true::false::(O m++suffix R)⟩ =
      some ⟨0,false::true::false::(O (m+1)++L.tail),R.getD []⟩ := by
  induction m generalizing L with
  | zero => exact pushLocal L R h
  | succ m ih =>
    have h1 := consume L (O m++suffix R) h
    have h2 := ih (false::true::L.tail) (by rfl)
    have H := join0 h1 h2
    rw [show 5*(m+1)+3=5+(5*m+3) by omega]
    simp only [List.tail_cons,onesSnoc] at H
    exact H

-- The terminal extension never reads C1: both right cells are implicit blanks.
theorem extendRaw (L : List Bool) (h : L.headD false=false) :
    run0 table 9 ⟨0,L,[]⟩ = some ⟨4,L.tail,O 4⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

theorem extendNormal (xs : Stack) :
    ∃ time d, 0<time ∧ run0 table time ⟨0,stack xs,[]⟩=some d ∧ Good d := by
  have h1 := extendRaw (stack xs) (stackHead xs)
  cases xs with
  | nil =>
    have h2 := eReturn 0 [] (O 3) (by rfl)
    exact ⟨12,_,by omega,join0 h1 h2,Good.normal .nil (.odd 0 (.last 3))⟩
  | bottom k =>
    have h2 := eReturn (k+1) [] (O 3) (by rfl)
    rw [List.append_nil,List.replicate_append_replicate] at h2
    exact ⟨9+(k+1+3),_,by omega,join0 h1 h2,Good.normal .nil (.odd 0 (.last (k+1+3)))⟩
  | odd a ys =>
    have h2 := eReturn (2*a+1) (stack ys) (O 3) (stackHead ys)
    rw [show O 3=O 3++[] by simp,onesJoin] at h2
    simp only [List.append_nil] at h2
    obtain ⟨t,d,ht,hd⟩ := retTail ys (.odd 0 (.last (2*a+1+3)))
    exact ⟨9+(2*a+1+3)+t,d,by omega,join0 (join0 h1 h2) ht,hd⟩

/-- The right terminal scan may temporarily make the second left run even.
    Process this exceptional run immediately during the left return. -/
theorem extendSecond (j : Nat) (xs : Stack) :
    ∃ time d, 0<time ∧ run0 table time ⟨0,false::true::false::(O j++stack xs),[]⟩=some d ∧ Good d := by
  have h1 := extendRaw (false::true::false::(O j++stack xs)) (by rfl)
  have h2 := eReturn 1 (false::(O j++stack xs)) (O 3) (by rfl)
  obtain ⟨t,d,ht,hd⟩ := retA xs j (.odd 0 (.last 4))
  exact ⟨9+4+t,d,by omega,join0 (join0 h1 h2) ht,hd⟩

theorem afterPush (m : Nat) (xs : Stack) :
    ∃ time d, 0<time ∧ run0 table time
      ⟨0,false::true::false::(O (m+1)++(stack xs).tail),[]⟩=some d ∧ Good d := by
  cases xs with
  | nil => simpa only [stack,List.tail_nil,List.append_nil] using extendSecond (m+1) .nil
  | bottom k =>
    have h := extendSecond (m+1+(k+1)) .nil
    simpa only [stack,List.tail_cons,List.append_nil,← List.replicate_append_replicate] using h
  | odd a ys =>
    rw [stack,List.tail_cons,onesJoin]
    exact extendSecond (m+1+(2*a+1)) ys

theorem terminalScan (m : Nat) (xs : Stack) :
    ∃ time d, 0<time ∧ run0 table time
      ⟨0,stack xs,true::false::O m⟩=some d ∧ Good d := by
  have h1 := scanPush m (stack xs) none (stackHead xs)
  obtain ⟨t,d,ht,hr,hd⟩ := afterPush m xs
  have H := join0 h1 hr
  exact ⟨5*m+3+t,d,by omega,by simpa only [suffix,List.append_nil] using H,hd⟩

theorem terminalOne (xs : Stack) :
    ∃ time d, 0<time ∧ run0 table time ⟨0,stack xs,[true]⟩=some d ∧ Good d := by
  have h1 := pushOne (stack xs) (stackHead xs)
  obtain ⟨t,d,ht,hr,hd⟩ := afterPush 0 xs
  exact ⟨3+t,d,by omega,join0 h1 hr,hd⟩

-- Long right run: start the left-return phase after consuming two ones.
theorem bounceRaw (L R : List Bool) (h : L.headD false=false) :
    run0 table 7 ⟨0,L,true::true::R⟩ = some ⟨5,L.tail,false::true::false::R⟩ := by
  cases L with
  | nil => rfl
  | cons b L => cases b <;> simp_all <;> rfl

theorem fOne (L R : List Bool) :
    run0 table 1 ⟨5,true::L,false::true::false::R⟩ =
      some ⟨0,L,true::false::true::false::R⟩ := by rfl

theorem fRoot (R : List Bool) :
    run0 table 4 ⟨5,[],false::true::false::R⟩ =
      some ⟨0,[],true::false::false::true::false::R⟩ := by rfl

theorem longBounce (xs : Stack) (r : Right) :
    ∃ time d, 0<time ∧ run0 table time ⟨0,stack xs,true::true::word r⟩=some d ∧ Good d := by
  have h1 := bounceRaw (stack xs) (word r) (stackHead xs)
  cases xs with
  | nil => exact ⟨11,_,by omega,join0 h1 (fRoot (word r)),Good.rootScan 0 (.odd 0 r)⟩
  | bottom k =>
    have h2 := fOne (O k) (word r)
    obtain ⟨t,d,ht,hd⟩ := retA .nil k (.odd 0 (.odd 0 r))
    have ht' : run0 table t ⟨0,O k,word (.odd 0 (.odd 0 r))⟩=some d := by
      simpa only [stack,List.append_nil] using ht
    exact ⟨7+1+t,d,by omega,join0 (join0 h1 h2) ht',hd⟩
  | odd a ys =>
    have h2 := fOne (O (2*a)++stack ys) (word r)
    obtain ⟨t,d,ht,hd⟩ := retA ys (2*a) (.odd 0 (.odd 0 r))
    exact ⟨7+1+t,d,by omega,join0 (join0 h1 h2) ht,hd⟩

theorem internalScan (b : Nat) (xs : Stack) (r : Right) :
    ∃ time d, 0<time ∧ run0 table time
      ⟨0,stack xs,true::false::(O (2*b+1)++false::word r)⟩=some d ∧ Good d := by
  have H := scanPush (2*b+1) (stack xs) (some (word r)) (stackHead xs)
  cases xs with
  | nil =>
    simp only [stack,List.tail_nil,List.append_nil,suffix,Option.getD_some] at H
    exact ⟨_,_,by omega,H,Good.normal (.odd 0 (.bottom (2*b+1))) r⟩
  | bottom k =>
    simp only [stack,List.tail_cons,suffix,Option.getD_some] at H
    rw [List.replicate_append_replicate] at H
    exact ⟨_,_,by omega,H,Good.normal (.odd 0 (.bottom (2*b+1+1+k))) r⟩
  | odd a ys =>
    simp only [stack,List.tail_cons,suffix,Option.getD_some] at H
    rw [onesJoin,show 2*b+1+1+(2*a+1)=2*(a+b+1)+1 by omega] at H
    exact ⟨_,_,by omega,H,Good.normal (.odd 0 (.odd (a+b+1) ys)) r⟩

theorem advance (c : Z0) (hc : Good c) :
    ∃ time d, 0<time ∧ run0 table time c=some d ∧ Good d := by
  cases hc with
  | rootScan m r =>
    have H := scanPush m [] (some (word r)) (by rfl)
    simp only [List.tail_nil,List.append_nil,suffix,Option.getD_some] at H
    exact ⟨5*m+3,_,by omega,H,Good.normal (.odd 0 (.bottom m)) r⟩
  | normal xs r =>
    cases r with
    | last n =>
      cases n with
      | zero => exact extendNormal xs
      | succ n =>
        cases n with
        | zero => exact terminalOne xs
        | succ n => exact longBounce xs (.last n)
    | odd a r =>
      cases a with
      | zero =>
        cases r with
        | last n => exact terminalScan n xs
        | odd b r => exact internalScan b xs r
      | succ a =>
        have H := longBounce xs (.odd a r)
        simp only [word] at H ⊢
        rw [show 2*(a+1)+1=2*a+1+1+1 by omega]
        simpa only [List.replicate_succ,List.cons_append] using H

theorem initial : Good ⟨0,[],[]⟩ := Good.normal .nil (.last 0)
def seed : {z // Good z} := ⟨⟨0,[],[]⟩,initial⟩
noncomputable def family (n : Nat) : Z0 := (phaseOrbit table Good advance seed n).val
noncomputable def cost (n : Nat) : Nat := phaseTime table Good advance (phaseOrbit table Good advance seed n)
theorem entry : run0 table 0 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem positive (n : Nat) : 0 < cost n := phaseTime_pos table Good advance (phaseOrbit table Good advance seed n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := phaseOrbit_step table Good advance seed n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 0 cost entry positive growth m hm
#print axioms advance
#print axioms growth
#print axioms never
end BB6.Agent3Raw120OneRAParity
