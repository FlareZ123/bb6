import Box28CarryRectangle

namespace BB6.Agent17.Box28SweepFill
open C9Pair
open BB6.Agent17.Box28CarryFamily (Gate Froot Eroot Droot pair localBlank)
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

/-- F1 is a rightward sweep rather than the old carry's transition to C.
    Both entry gates remain arbitrary. -/
def stepCore (b e : Gate) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true => b c
  | .C,true => some (left .D false c)
  | .D,false => some (right .E false c)
  | .D,true => some (left .D true c)
  | .E,false => e c
  | .E,true => some (right .F true c)
  | .F,false => some (right .A true c)
  | .F,true => some (right .F true c)

def runCore (b e : Gate) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (stepCore b e c).bind (runCore b e n)

theorem runCore_add (b e : Gate) (m n : Nat) (c : Config) :
    runCore b e (m+n) c = (runCore b e m c).bind (runCore b e n) := by
  induction m generalizing c with
  | zero => simp [runCore]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [runCore]
    cases stepCore b e c <;> simp [ih]

theorem runCore_one (b e : Gate) (c : Config) :
    runCore b e 1 c = stepCore b e c := by
  cases h : stepCore b e c <;> simp [runCore,h]

/-- Finite words with no double zero before the final one. -/
inductive Word : Stream → Prop where
  | endWord : Word zeros
  | one {s} : Word s → Word (push true s)
  | gap {s} : Word s → Word (pair false true s)

theorem prefix_word (n : Nat) (s : Stream) (hs : Word s) : Word (rep true n s) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact Word.one ih

theorem consume_one (b e : Gate) (n : Nat) (s : Stream) :
    runCore b e 1 (Froot n (push true s)) = some (Froot (n+1) s) := by rfl

theorem consume_gap (b e : Gate) (n : Nat) (s : Stream) :
    runCore b e 2 (Froot n (pair false true s)) = some (Froot (n+2) s) := by rfl

theorem rewind (b e : Gate) (n : Nat) (r : Stream) :
    runCore b e (n+2) (Droot n r) = some (Eroot 0 (rep true (n+1) r)) := by
  induction n generalizing r with
  | zero => simp [runCore,stepCore,Droot,Eroot,ones,rep,left,right]
  | succ n ih =>
    rw [show n+1+2=1+(n+2) by omega,runCore_add]
    change (some (Droot n (push true r))).bind _ = _
    rw [Option.bind_some,ih,BB6.Agent17.Box28CarryFamily.rep_push]

theorem turn (b e : Gate) (n : Nat) :
    runCore b e 4 (Froot n zeros) = some (Droot n (pair false true zeros)) := by rfl

theorem fill (b e : Gate) (n : Nat) :
    runCore b e (n+7) (Froot n zeros) =
      some (Froot 1 (rep true n (pair false true zeros))) := by
  rw [show n+7=4+(n+2)+1 by omega,runCore_add,runCore_add,turn,Option.bind_some,
    rewind,Option.bind_some]
  rfl

theorem progress (b e : Gate) (n : Nat) (s : Stream) (hs : Word s) :
    ∃ t n' s', 0<t ∧ runCore b e t (Froot n s) = some (Froot n' s') ∧ Word s' := by
  cases hs with
  | endWord => exact ⟨n+7,1,_,by omega,fill b e n,prefix_word n _ (.gap .endWord)⟩
  | one hw => exact ⟨1,n+1,_,by decide,consume_one b e n _,hw⟩
  | gap hw => exact ⟨2,n+2,_,by decide,consume_gap b e n _,hw⟩

theorem never (b e : Gate) (t n : Nat) (s : Stream) (hs : Word s) :
    runCore b e t (Froot n s) ≠ none := by
  induction t using Nat.strongRecOn generalizing n s with
  | ind t ih =>
    intro ht
    obtain ⟨u,n',s',hu,hr,hw⟩ := progress b e n s hs
    by_cases h : t ≤ u
    · rw [show u=t+(u-t) by omega,runCore_add,ht] at hr; contradiction
    · rw [show t=u+(t-u) by omega,runCore_add,hr,Option.bind_some] at ht
      exact ih _ (by omega) n' s' hw ht

theorem never_from (b e : Gate) (j n : Nat) (s : Stream)
    (h : runCore b e j localBlank = some (Froot n s))
    (hs : Word s) (t : Nat) : runCore b e t localBlank ≠ none := by
  intro ht
  by_cases hj : t ≤ j
  · rw [show j=t+(j-t) by omega,runCore_add,ht] at h; contradiction
  · rw [show t=j+(t-j) by omega,runCore_add,h,Option.bind_some] at ht
    exact never b e _ n s hs ht

#print axioms never
#print axioms never_from
end BB6.Agent17.Box28SweepFill
