import Box33BinaryCounter
namespace BB6.Agent17.Box28CarryFamily
open C9Pair
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option linter.constructorNameAsVariable false
inductive Entry where | c | d | e deriving DecidableEq, Repr

/-- The two entry gates are arbitrary: the aligned recurrent languages never
    read B1 or E0, even when they contain unboundedly many digits. -/
abbrev Gate := Config → Option Config

def stepCore (two : Bool) (b e : Gate) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right (if two then .F else .E) true c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true => b c
  | .C,true => some (left .D false c)
  | .D,false => some (right .E false c)
  | .D,true => some (left .D true c)
  | .E,false => e c
  | .E,true => some (right .F true c)
  | .F,false => some (right .A true c)
  | .F,true => some (right .C true c)

def runCore (two : Bool) (b e : Gate) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (stepCore two b e c).bind (runCore two b e n)

theorem runCore_add (two : Bool) (b e : Gate) (m n : Nat) (c : Config) :
    runCore two b e (m+n) c = (runCore two b e m c).bind (runCore two b e n) := by
  induction m generalizing c with
  | zero => simp [runCore]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [runCore]
    cases stepCore two b e c <;> simp [ih]

def Eroot (n : Nat) (s : Stream) : Config := ⟨.E,ones n,s 0,pop s⟩
def Froot (n : Nat) (s : Stream) : Config := ⟨.F,ones n,s 0,pop s⟩
def Droot (n : Nat) (s : Stream) : Config := ⟨.D,ones n,true,s⟩
def pair (a b : Bool) (s : Stream) := push a (push b s)
def triple (a b c : Bool) (s : Stream) := push a (pair b c s)

theorem rep_push (n : Nat) (r : Stream) : rep true n (push true r) = rep true (n+1) r := by rw [rep_add]; rfl

theorem rewind (two : Bool) (b e : Gate) (n : Nat) (r : Stream) :
    runCore two b e (n+2) (Droot n r) = some (Eroot 0 (rep true (n+1) r)) := by
  induction n generalizing r with
  | zero => simp [runCore,stepCore,Droot,Eroot,ones,rep,left,right]
  | succ n ih =>
    rw [show n+1+2=1+(n+2) by omega,runCore_add]
    change (some (Droot n (push true r))).bind _ = _
    rw [Option.bind_some,ih,rep_push]

inductive Word3 : Stream → Prop where
  | endWord : Word3 (ones 1)
  | d111 {s} : Word3 s → Word3 (triple true true true s)
  | d110 {s} : Word3 s → Word3 (triple true true false s)
  | d101 {s} : Word3 s → Word3 (triple true false true s)

theorem prefix3 (k : Nat) (s : Stream) (h : Word3 s) : Word3 (rep true (3*k) s) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 3*(k+1)=3+3*k by omega,rep_add]
    exact Word3.d111 ih

theorem carry3 (b e : Gate) (n : Nat) (s : Stream) :
    runCore false b e 3 (Eroot n (triple true false true s)) = some (Eroot (n+3) s) := by rfl

theorem enter111 (b e : Gate) (n : Nat) (s : Stream) :
    runCore false b e 3 (Eroot n (triple true true true s)) = some (Droot (n+1) (push false s)) := by rfl

theorem enter110 (b e : Gate) (n : Nat) (s : Stream) :
    runCore false b e 4 (Eroot n (triple true true false s)) = some (Droot n (pair false true s)) := by rfl

theorem enterEnd3 (b e : Gate) (n : Nat) :
    runCore false b e 5 (Eroot n (ones 1)) = some (Droot (n+1) (push false (ones 1))) := by rfl

theorem progress3 (b e : Gate) (k : Nat) (s : Stream) (h : Word3 s) :
    ∃ j k' s', 0<j ∧ runCore false b e j (Eroot (3*k) s) = some (Eroot (3*k') s') ∧ Word3 s' := by
  cases h with
  | endWord =>
    refine ⟨5+(3*k+1+2),0,rep true (3*k) (triple true true false (ones 1)),by omega,?_,prefix3 k _ (.d110 .endWord)⟩
    rw [runCore_add,enterEnd3,Option.bind_some,rewind,show 3*k+1+1=3*k+2 by omega,rep_add]
    rfl
  | d111 ht =>
    refine ⟨3+(3*k+1+2),0,rep true (3*k) (triple true true false _),by omega,?_,prefix3 k _ (.d110 ht)⟩
    rw [runCore_add,enter111,Option.bind_some,rewind,show 3*k+1+1=3*k+2 by omega,rep_add]
    rfl
  | d110 ht =>
    refine ⟨4+(3*k+2),0,rep true (3*k) (triple true false true _),by omega,?_,prefix3 k _ (.d101 ht)⟩
    rw [runCore_add,enter110,Option.bind_some,rewind,rep_add]
    rfl
  | d101 ht => exact ⟨3,k+1,_,by decide,by rw [show 3*(k+1)=3*k+3 by omega,carry3],ht⟩

inductive Word2 : Stream → Prop where
  | endWord : Word2 zeros
  | d11 {s} : Word2 s → Word2 (pair true true s)
  | d10 {s} : Word2 s → Word2 (pair true false s)
  | d01 {s} : Word2 s → Word2 (pair false true s)

theorem prefix2 (k : Nat) (s : Stream) (h : Word2 s) : Word2 (rep true (2*k) s) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,rep_add]
    exact Word2.d11 ih

theorem E_to_F (b e : Gate) (s : Stream) : runCore true b e 1 (Eroot 0 (push true s)) = some (Froot 1 s) := by rfl

theorem carry2 (b e : Gate) (n : Nat) (s : Stream) :
    runCore true b e 2 (Froot n (pair false true s)) = some (Froot (n+2) s) := by rfl

theorem enter11 (b e : Gate) (n : Nat) (s : Stream) :
    runCore true b e 2 (Froot n (pair true true s)) = some (Droot n (push false s)) := by rfl

theorem enter10 (b e : Gate) (n : Nat) (s : Stream) :
    runCore true b e 3 (Froot (n+1) (pair true false s)) = some (Droot n (pair false true s)) := by rfl

theorem enterEnd2 (b e : Gate) (n : Nat) :
    runCore true b e 4 (Froot n zeros) = some (Droot n (push false (ones 1))) := by rfl

theorem rewind2 (b e : Gate) (n : Nat) (r : Stream) :
    runCore true b e (n+2+1) (Droot n r) = some (Froot 1 (rep true n r)) := by
  rw [runCore_add,rewind,Option.bind_some]
  exact E_to_F b e _

theorem progress2 (b e : Gate) (k : Nat) (s : Stream) (h : Word2 s) :
    ∃ j k' s', 0<j ∧ runCore true b e j (Froot (2*k+1) s) = some (Froot (2*k'+1) s') ∧ Word2 s' := by
  cases h with
  | endWord =>
    refine ⟨4+(2*k+1+2+1),0,rep true (2*k) (pair true false (pair true false zeros)),by omega,?_,prefix2 k _ (.d10 (.d10 .endWord))⟩
    rw [runCore_add,enterEnd2,Option.bind_some,rewind2,rep_add]
    simp [pair,ones,rep,zero_push]
  | d11 ht =>
    refine ⟨2+(2*k+1+2+1),0,rep true (2*k) (pair true false _),by omega,?_,prefix2 k _ (.d10 ht)⟩
    rw [runCore_add,enter11,Option.bind_some,rewind2,rep_add]
    rfl
  | d10 ht =>
    refine ⟨3+(2*k+2+1),0,rep true (2*k) (pair false true _),by omega,?_,prefix2 k _ (.d01 ht)⟩
    rw [runCore_add,enter10,Option.bind_some,rewind2]
  | d01 ht => exact ⟨2,k+1,_,by decide,by rw [show 2*(k+1)+1=2*k+1+2 by omega,carry2],ht⟩

theorem never3 (b e : Gate) (n k : Nat) (s : Stream) (h : Word3 s) : runCore false b e n (Eroot (3*k) s) ≠ none := by
  induction n using Nat.strongRecOn generalizing k s with
  | ind n ih =>
    intro hn
    obtain ⟨j,k',s',hj,hs,hg⟩ := progress3 b e k s h
    by_cases hnj : n≤j
    · rw [show j=n+(j-n) by omega,runCore_add,hn] at hs; contradiction
    · rw [show n=j+(n-j) by omega,runCore_add,hs] at hn
      exact ih _ (by omega) k' s' hg hn

theorem never2 (b e : Gate) (n k : Nat) (s : Stream) (h : Word2 s) : runCore true b e n (Froot (2*k+1) s) ≠ none := by
  induction n using Nat.strongRecOn generalizing k s with
  | ind n ih =>
    intro hn
    obtain ⟨j,k',s',hj,hs,hg⟩ := progress2 b e k s h
    by_cases hnj : n≤j
    · rw [show j=n+(j-n) by omega,runCore_add,hn] at hs; contradiction
    · rw [show n=j+(n-j) by omega,runCore_add,hs] at hn
      exact ih _ (by omega) k' s' hg hn


def localBlank : Config := ⟨.A,zeros,false,zeros⟩

theorem runCore_one (two : Bool) (b e : Gate) (c : Config) :
    runCore two b e 1 c = stepCore two b e c := by
  cases h : stepCore two b e c <;> simp [runCore,h]

theorem never_from3 (b e : Gate) (j : Nat) (s : Stream)
    (hs : runCore false b e j localBlank = some (Eroot 0 s))
    (hw : Word3 s) (n : Nat) : runCore false b e n localBlank ≠ none := by
  intro hn
  by_cases h : n≤j
  · rw [show j=n+(j-n) by omega,runCore_add,hn] at hs; contradiction
  · rw [show n=j+(n-j) by omega,runCore_add,hs,Option.bind_some] at hn
    exact never3 b e _ 0 s hw hn

theorem never_from2 (b e : Gate) (j : Nat) (s : Stream)
    (hs : runCore true b e j localBlank = some (Froot 1 s))
    (hw : Word2 s) (n : Nat) : runCore true b e n localBlank ≠ none := by
  intro hn
  by_cases h : n≤j
  · rw [show j=n+(j-n) by omega,runCore_add,hn] at hs; contradiction
  · rw [show n=j+(n-j) by omega,runCore_add,hs,Option.bind_some] at hn
    exact never2 b e _ 0 s hw hn

-- Backwards-compatible entry-specific API for the previous six cylinders.
def entryAction (e : Entry) (c : Config) : Option Config := some (match e with
  | .c => right .C true c
  | .d => right .D false c
  | .e => right .E false c)
def step (two : Bool) (e : Entry) := stepCore two (fun _ => none) (entryAction e)
def run (two : Bool) (e : Entry) := runCore two (fun _ => none) (entryAction e)
theorem run_add (two : Bool) (e : Entry) (m n : Nat) (c : Config) :
    run two e (m+n) c = (run two e m c).bind (run two e n) :=
  runCore_add two _ _ m n c

theorem initial (two : Bool) (e : Entry) :
    ∃ n, run two e n ⟨.A,zeros,false,zeros⟩ = some (Eroot 0 (ones 1)) := by
  cases e with
  | c => exact ⟨8,by cases two <;> simp [run,runCore,stepCore,entryAction,Eroot,ones,rep,left,right]⟩
  | d => exact ⟨7,by cases two <;> simp [run,runCore,stepCore,entryAction,Eroot,ones,rep,left,right]⟩
  | e => exact ⟨5,by cases two <;> simp [run,runCore,stepCore,entryAction,Eroot,ones,rep,left,right]⟩


theorem never_blank (two : Bool) (e : Entry) (n : Nat) : run two e n ⟨.A,zeros,false,zeros⟩ ≠ none := by
  cases two
  · obtain ⟨j,hj⟩ := initial false e
    exact never_from3 (fun _ => none) (entryAction e) j (ones 1) hj .endWord n
  · obtain ⟨j,hj⟩ := initial true e
    have hnext : runCore true (fun _ => none) (entryAction e) (j+1) localBlank = some (Froot 1 zeros) := by
      rw [runCore_add]
      change run true e j ⟨.A,zeros,false,zeros⟩ >>= runCore true (fun _ => none) (entryAction e) 1 = _
      rw [hj]
      rfl
    exact never_from2 (fun _ => none) (entryAction e) (j+1) zeros hnext .endWord n

#print axioms never3
#print axioms never2
#print axioms never_blank
end BB6.Agent17.Box28CarryFamily
