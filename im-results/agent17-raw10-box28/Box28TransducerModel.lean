import Box28Transducer

namespace BB6.Agent17.Box28TransducerModel
open C9Pair
open BB6.Agent17.Box28Transducer
open BB6.Agent17.Box28CarryFamily (Gate pair localBlank)
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def state (s : S) : Q := if s=0 then .A else if s=1 then .E else .F
def stepCore (p : Params) (b : Gate) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right (state (dst p.o.a)) (wr p.o.a) c)
  | .B,false | .C,false => some (left .C true c)
  | .B,true => b c
  | .C,true => some (left .D false c)
  | .D,false => some (right .E false c)
  | .D,true => some (left .D true c)
  | .E,false => some (right (state (dst p.ze)) (wr p.ze) c)
  | .E,true => some (right (state (dst p.o.e)) (wr p.o.e) c)
  | .F,false => some (right (state (dst p.zf)) (wr p.zf) c)
  | .F,true => some (right (state (dst p.o.f)) (wr p.o.f) c)

def runCore (p : Params) (b : Gate) : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (stepCore p b c).bind (runCore p b n)

theorem runCore_add (p : Params) (b : Gate) (m n : Nat) (c : Config) :
    runCore p b (m+n) c = (runCore p b m c).bind (runCore p b n) := by
  induction m generalizing c with
  | zero => simp [runCore]
  | succ m ih =>
    rw [Nat.succ_add]; simp only [runCore]
    cases stepCore p b c <;> simp [ih]

theorem runCore_one (p : Params) (b : Gate) (c : Config) :
    runCore p b 1 c = stepCore p b c := by
  cases h : stepCore p b c <;> simp [runCore,h]

def atScan (s : S) (l r : Stream) : Config := ⟨state s,l,r 0,pop r⟩
def atLeft (q : Q) (l r : Stream) : Config := ⟨q,pop l,l 0,r⟩
def ray (n : Nat) (l : Stream) : Stream := rep true n (push false l)
def tail : Stream := pair false true zeros
def root (n : Nat) (l : Stream) : Config := atScan 1 (push false l) (rep true n tail)
def newTail (c : Code) (n : Nat) (l : Stream) : Stream :=
  if wr c then l else ray n l

theorem push_ray (c : Code) (n : Nat) (l : Stream) :
    push (wr c) (ray n l) = ray (inc c n) (newTail c n l) := by
  cases h : wr c <;> simp [ray,inc,newTail,h,rep]

theorem step_one (p : Params) (b : Gate) (s : S) (l r : Stream) :
    stepCore p b (atScan s l (push true r)) =
      some (atScan (dst (one p.o s)) (push (wr (one p.o s)) l) r) := by
  have hs := (show ∀ s : S, s=0 ∨ s=1 ∨ s=2 by decide) s
  rcases hs with h|h|h <;> subst s <;> rfl

theorem step_zero (p : Params) (b : Gate) (s : S) (l r : Stream) (hs : s≠0) :
    stepCore p b (atScan s l (push false r)) =
      some (atScan (dst (zero p s)) (push (wr (zero p s)) l) r) := by
  have h := (show ∀ s : S, s≠0 → s=1 ∨ s=2 by decide) s hs
  rcases h with h|h <;> subst s <;> rfl

theorem zero_blank_step (p : Params) (b : Gate) (s : S) (l : Stream) (hs : s≠0) :
    runCore p b 1 (atScan s l zeros) =
      some (atScan (dst (zero p s)) (push (wr (zero p s)) l) zeros) := by
  rw [runCore_one]
  have h := step_zero p b s l zeros hs
  rw [zero_push] at h
  exact h

theorem scan_prefix (p : Params) (b : Gate) (n : Nat) (s : S) (r : Nat) (l u : Stream) :
    ∃ l', runCore p b n (atScan s (ray r l) (rep true n u)) =
      some (atScan (scan p.o n s r).1 (ray (scan p.o n s r).2 l') u) := by
  induction n generalizing s r l with
  | zero => exact ⟨l,rfl⟩
  | succ n ih =>
    obtain ⟨l',hl⟩ := ih (dst (one p.o s)) (inc (one p.o s) r) (newTail (one p.o s) r l)
    refine ⟨l',?_⟩
    rw [runCore,rep,step_one,Option.bind_some,push_ray]
    exact hl

theorem consume_gap (p : Params) (b : Gate) (s : S) (r : Nat) (l : Stream) (hs : s≠0) :
    ∃ l', runCore p b 2 (atScan s (ray r l) tail) =
      some (atScan (postState p s) (ray (countList (startCodes p s) r) l') zeros) := by
  let c := zero p s
  let d := one p.o (dst c)
  refine ⟨newTail d (inc c r) (newTail c r l),?_⟩
  change runCore p b 2 (atScan s (ray r l) (push false (push true zeros))) = _
  rw [runCore,step_zero p b s _ _ hs,Option.bind_some,push_ray,runCore_one,step_one,push_ray]
  rfl

inductive ZeroPath (p : Params) : S → List Code → Prop where
  | done : ZeroPath p 0 []
  | more {s cs} : s≠0 → ZeroPath p (dst (zero p s)) cs →
      ZeroPath p s (zero p s::cs)

theorem zero_path (p : Params) (s : S) (cs : List Code) (h : zeroCodes p s=some cs) :
    ZeroPath p s cs := by
  unfold zeroCodes at h
  dsimp only at h
  split at h
  · rename_i hs
    subst s; cases h; exact .done
  · rename_i hs
    split at h
    · rename_i h1
      cases h
      apply ZeroPath.more hs
      rw [h1]; exact .done
    · rename_i h1
      split at h
      · rename_i h2
        cases h
        apply ZeroPath.more hs
        apply ZeroPath.more h1
        rw [h2]; exact .done
      · contradiction

theorem run_zero_path (p : Params) (b : Gate) (s : S) (cs : List Code)
    (h : ZeroPath p s cs) (r : Nat) (l : Stream) :
    ∃ l', runCore p b cs.length (atScan s (ray r l) zeros) =
      some (atScan 0 (ray (countList cs r) l') zeros) := by
  induction h generalizing r l with
  | done => exact ⟨l,rfl⟩
  | @more s cs hs hp ih =>
    obtain ⟨l',hl⟩ := ih (inc (zero p s) r) (newTail (zero p s) r l)
    refine ⟨l',?_⟩
    rw [List.length_cons,show cs.length+1=1+cs.length by omega,runCore_add,
      zero_blank_step p b s _ hs,Option.bind_some,push_ray]
    exact hl

theorem drift_check : ∀ ze zf : Code, ∀ s : S,
    let p : Params := ⟨⟨0,0,0⟩,ze,zf⟩
    zeroCodes p s=none → s≠0 ∧ zeroCodes p (dst (zero p s))=none := by decide

theorem drift_closed (p : Params) (s : S) (h : zeroCodes p s=none) :
    s≠0 ∧ zeroCodes p (dst (zero p s))=none := by
  rcases p with ⟨o,ze,zf⟩
  exact drift_check ze zf s h

theorem drift (p : Params) (b : Gate) (t : Nat) (s : S) (l : Stream) (h : zeroCodes p s=none) :
    runCore p b t (atScan s l zeros) ≠ none := by
  induction t generalizing s l with
  | zero => simp [runCore]
  | succ t ih =>
    have hc := drift_closed p s h
    rw [show t+1=1+t by omega,runCore_add,zero_blank_step p b s l hc.1,Option.bind_some]
    exact ih _ _ hc.2

theorem rewind (p : Params) (b : Gate) (r : Nat) (l u : Stream) :
    runCore p b (r+1) (atLeft .D (ray r l) u) =
      some (atScan 1 (push false l) (rep true r u)) := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    rw [show r+1+1=1+(r+1) by omega,runCore_add]
    change (some (atLeft .D (ray r l) (push true u))).bind _ = _
    rw [Option.bind_some,ih,BB6.Agent17.Box28CarryFamily.rep_push] <;> rfl

theorem turn (p : Params) (b : Gate) (r : Nat) (l : Stream) :
    runCore p b 3 (atScan 0 (ray r l) zeros) = some (atLeft .D (ray r l) tail) := by rfl

theorem turn_back (p : Params) (b : Gate) (r : Nat) (l : Stream) :
    runCore p b (r+4) (atScan 0 (ray r l) zeros) = some (root r l) := by
  rw [show r+4=3+(r+1) by omega,runCore_add,turn,Option.bind_some,rewind] <;> rfl

theorem scan_then_gap (p : Params) (b : Gate) (n : Nat) (l : Stream)
    (hs : (scan p.o n 1 0).1≠0) :
    ∃ l', runCore p b (n+2) (root n l) =
      some (atScan (postState p (scan p.o n 1 0).1)
        (ray (countList (startCodes p (scan p.o n 1 0).1) (scan p.o n 1 0).2) l') zeros) := by
  obtain ⟨l1,h1⟩ := scan_prefix p b n 1 0 l tail
  obtain ⟨l2,h2⟩ := consume_gap p b _ _ l1 hs
  exact ⟨l2,by rw [runCore_add,show root n l=atScan 1 (ray 0 l) (rep true n tail) by rfl,h1,Option.bind_some,h2]⟩

/-- A returning macro preserves an arbitrary left tape beyond the most
    recent zero; the exact new unary length is its trailing write count. -/
theorem round (p : Params) (b : Gate) (n : Nat) (l : Stream) (cs : List Code)
    (hs : (scan p.o n 1 0).1≠0)
    (hc : tailCodes p (scan p.o n 1 0).1=some cs) :
    let m := countList cs (scan p.o n 1 0).2
    ∃ l', runCore p b (n+cs.length+m+4) (root n l) = some (root m l') := by
  let h := scan p.o n 1 0
  change h.1≠0 at hs
  change tailCodes p h.1=some cs at hc
  obtain ⟨l2,h2⟩ := scan_then_gap p b n l hs
  change runCore p b (n+2) (root n l) =
    some (atScan (postState p h.1) (ray (countList (startCodes p h.1) h.2) l2) zeros) at h2
  cases hz : zeroCodes p (postState p h.1) with
  | none => simp [tailCodes,hz] at hc
  | some zs =>
    have he : cs=startCodes p h.1++zs := by simpa [tailCodes,hz,eq_comm] using hc
    subst cs
    let r := countList (startCodes p h.1) h.2
    let m := countList zs r
    obtain ⟨l3,h3⟩ := run_zero_path p b _ zs (zero_path p _ zs hz) r l2
    change ∃ l', runCore p b (n+(startCodes p h.1++zs).length+m+4) (root n l) = some (root m l')
    refine ⟨l3,?_⟩
    rw [show n+(startCodes p h.1++zs).length+m+4=(n+2)+zs.length+(m+4) by simp [startCodes]; omega,
      runCore_add,runCore_add,h2,Option.bind_some,h3,Option.bind_some,turn_back]

theorem next_sound (p : Params) (b : Gate) (n m : Nat) (l : Stream)
    (h : concreteStep p n=.next m) :
    ∃ t l', 0<t ∧ runCore p b t (root n l) = some (root m l') := by
  unfold concreteStep at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hs
    cases hc : tailCodes p (scan p.o n 1 0).1 with
    | none => simp [hc] at h
    | some cs =>
      simp [hc] at h
      subst m
      obtain ⟨l',hl⟩ := round p b n l cs hs hc
      exact ⟨_,l',by omega,hl⟩

theorem drift_sound (p : Params) (b : Gate) (n : Nat) (l : Stream)
    (h : concreteStep p n=.drift) (t : Nat) : runCore p b t (root n l) ≠ none := by
  unfold concreteStep at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hs
    cases hc : tailCodes p (scan p.o n 1 0).1 with
    | some cs => simp [hc] at h
    | none =>
      have hz : zeroCodes p (postState p (scan p.o n 1 0).1)=none := by
        cases hq : zeroCodes p (postState p (scan p.o n 1 0).1) <;> simp [tailCodes,hq] at hc ⊢
      obtain ⟨l',hr⟩ := scan_then_gap p b n l hs
      intro ht
      by_cases hle : t≤n+2
      · rw [show n+2=t+(n+2-t) by omega,runCore_add,ht] at hr; contradiction
      · rw [show t=(n+2)+(t-(n+2)) by omega,runCore_add,hr,Option.bind_some] at ht
        exact drift p b _ _ _ hz ht

theorem never_root (p : Params) (b : Gate) (hc : safeCert p=true)
    (t n : Nat) (l : Stream) (hn : classOf n ∈ bank p) :
    runCore p b t (root n l) ≠ none := by
  induction t using Nat.strongRecOn generalizing n l with
  | ind t ih =>
    have hclosed := safe_member p hc _ hn
    unfold closedAt at hclosed
    rw [← step_class p n] at hclosed
    cases hs : concreteStep p n with
    | halt => simp [abstractStep,hs] at hclosed
    | drift => exact drift_sound p b n l hs t
    | next m =>
      have hm : classOf m ∈ bank p := by simpa [abstractStep,hs] using hclosed
      obtain ⟨u,l',hu,hr⟩ := next_sound p b n m l hs
      intro ht
      by_cases hle : t≤u
      · rw [show u=t+(u-t) by omega,runCore_add,ht] at hr; contradiction
      · rw [show t=u+(t-u) by omega,runCore_add,hr,Option.bind_some] at ht
        exact ih _ (by omega) m l' hm ht

theorem init (p : Params) (b : Gate) :
    runCore p b 4 localBlank = some (root 0 zeros) := by
  simp [runCore,stepCore,localBlank,root,atScan,state,tail,pair,rep,left,right]

theorem never_blank (p : Params) (b : Gate) (hc : safeCert p=true) (t : Nat) :
    runCore p b t localBlank ≠ none := by
  intro ht
  have hi := init p b
  by_cases hle : t≤4
  · rw [show 4=t+(4-t) by omega,runCore_add,ht] at hi; contradiction
  · rw [show t=4+(t-4) by omega,runCore_add,hi,Option.bind_some] at ht
    exact never_root p b hc _ 0 zeros (by simpa [classOf] using bank_zero p) ht

#print axioms round
#print axioms never_blank
end BB6.Agent17.Box28TransducerModel
