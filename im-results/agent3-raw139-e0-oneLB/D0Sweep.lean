import PackedAudit

/- Arbitrary-tail block sweep proof for the D0 leaf. -/
namespace BB6.Agent3OneLBD0
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay

abbrev Word := List Bool
abbrev z := false
abbrev o := true

def codes (slow : Bool) : List Nat :=
  [7,23,11,13,14,21,24,16,6,11,3,0]
def parent (slow : Bool) : PartialMachine := fromCodes (codes slow)

-- Headless finite zipper, with implicit zeros at either end.  Left includes
-- the scanned bit, exactly as in the original packed zipper.
structure S where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq

def enc (s : S) : P := ⟨s.q,pack s.l,pack s.r⟩

def mvS (mv : Move) (s : S) : S :=
  if mv.right then
    ⟨mv.next,s.r.headD false::mv.write::s.l.tail,s.r.tail⟩
  else
    ⟨mv.next,s.l.tail,mv.write::s.r⟩

def stepS (slow : Bool) (s : S) : Option S :=
  ((parent slow (s.q,s.l.headD false)).bind id).map (fun mv => mvS mv s)

def runS (slow : Bool) : Nat → S → Option S
  | 0,s => some s
  | n+1,s => (stepS slow s).bind (runS slow n)

theorem enc_mv (mv : Move) (s : S) :
    enc (mvS mv s) = moveP mv (enc s) := by
  cases h : mv.right <;> simp [enc,mvS,moveP,h,pack,pack_head,pack_tail]

theorem enc_read (s : S) : readP (enc s) = (s.q,s.l.headD false) := by
  unfold readP enc
  rw [pack_head]
  cases s.l.headD false <;> rfl

theorem enc_step (slow : Bool) (s : S) :
    (stepS slow s).map enc = stepP (parent slow) (enc s) := by
  unfold stepS stepP
  rw [enc_read]
  cases h : (parent slow (s.q,s.l.headD false)).bind id with
  | none => rfl
  | some mv => simp [enc_mv]

theorem enc_run (slow : Bool) (n : Nat) (s : S) :
    (runS slow n s).map enc = runP (parent slow) n (enc s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [runS,runP,← enc_step]
    cases h : stepS slow s with
    | none => rfl
    | some t => exact ih t

theorem runS_add (slow : Bool) (n k : Nat) (s : S) :
    runS slow (n+k) s = (runS slow n s).bind (runS slow k) := by
  induction n generalizing s with
  | zero => simp [runS]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [runS]
    cases stepS slow s with
    | none => rfl
    | some t => exact ih t

theorem joinS {slow : Bool} {n k : Nat} {a b c : S}
    (h : runS slow n a = some b) (g : runS slow k b = some c) :
    runS slow (n+k) a = some c := by
  rw [runS_add,h]; exact g


def rep (x : Word) : Nat → Word → Word
  | 0,w => w
  | n+1,w => x ++ rep x n w

theorem rep_last (x : Word) (n : Nat) (w : Word) :
    rep x n (x++w) = x++rep x n w := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih]

structure Macro where
  q : Fin 6
  left : Bool
  period : Nat
  u : Word
  v : Word
  x : Word
  y : Word

def beginS (m : Macro) (n : Nat) (a b : Word) : S :=
  if m.left then ⟨m.q,m.u++rep m.x n a,m.v++b⟩
  else ⟨m.q,m.u++a,m.v++rep m.x n b⟩

def endS (m : Macro) (n : Nat) (a b : Word) : S :=
  if m.left then ⟨m.q,m.u++a,m.v++rep m.y n b⟩
  else ⟨m.q,m.u++rep m.y n a,m.v++b⟩

def Valid (m : Macro) : Prop :=
  ∀ a b, runS false m.period (beginS m 1 a b) = some (endS m 1 a b)

theorem repeat_sound (m : Macro) (h : Valid m) (n : Nat) (a b : Word) :
    runS false (m.period*n) (beginS m n a b) = some (endS m n a b) := by
  induction n generalizing a b with
  | zero =>
    cases hm : m.left <;> simp [beginS,endS,rep,hm,runS]
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (m.period*n)]
    cases hm : m.left
    · have h1 := h a (rep m.x n b)
      have h2 := ih (m.y++a) b
      simp only [beginS,endS,hm,if_false,rep,List.append_nil] at h1 h2
      simp only [beginS,endS,hm,if_false,rep]
      rw [← rep_last]
      exact joinS h1 h2
    · have h1 := h (rep m.x n a) b
      have h2 := ih a (m.y++b)
      simp only [beginS,endS,hm,if_true,rep,List.append_nil] at h1 h2
      simp only [beginS,endS,hm,if_true,rep]
      rw [← rep_last]
      exact joinS h1 h2

def pre (u : Word) (x : Nat) : Nat := pack u + 2^u.length*x

theorem pack_append (u w : Word) : pack (u++w) = pre u (pack w) := by
  induction u with
  | nil => simp [pack,pre]
  | cons b u ih =>
    simp only [List.cons_append,pack,ih,pre,List.length_cons,Nat.pow_succ,Nat.mul_add,Nat.add_assoc]
    ac_rfl

def blockIter (A c : Nat) : Nat → Nat → Nat
  | 0,w => w
  | n+1,w => c + A*blockIter A c n w

theorem pack_rep (x : Word) (n : Nat) (w : Word) :
    pack (rep x n w) = blockIter (2^x.length) (pack x) n (pack w) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,pack_append,pre,ih,blockIter]

def repNum (x : Word) (n a : Nat) : Nat := blockIter (2^x.length) (pack x) n a

def beginP (m : Macro) (n a b : Nat) : P :=
  if m.left then ⟨m.q,pre m.u (repNum m.x n a),pre m.v b⟩
  else ⟨m.q,pre m.u a,pre m.v (repNum m.x n b)⟩

def endP (m : Macro) (n a b : Nat) : P :=
  if m.left then ⟨m.q,pre m.u a,pre m.v (repNum m.y n b)⟩
  else ⟨m.q,pre m.u (repNum m.y n a),pre m.v b⟩

theorem enc_begin (m : Macro) (n : Nat) (a b : Word) :
    enc (beginS m n a b) = beginP m n (pack a) (pack b) := by
  cases hm : m.left <;> simp [beginS,beginP,enc,hm,pack_append,pack_rep,repNum]

theorem enc_end (m : Macro) (n : Nat) (a b : Word) :
    enc (endS m n a b) = endP m n (pack a) (pack b) := by
  cases hm : m.left <;> simp [endS,endP,enc,hm,pack_append,pack_rep,repNum]

def incWord : Word → Word
  | [] => [true]
  | false::w => true::w
  | true::w => false::incWord w

theorem pack_incWord (w : Word) : pack (incWord w) = pack w + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [incWord,pack,Bool.toNat,ih] <;> omega

theorem pack_surj (n : Nat) : ∃ w : Word, pack w = n := by
  induction n with
  | zero => exact ⟨[],rfl⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨incWord w,by rw [pack_incWord,hw]⟩

theorem packed_repeat (m : Macro) (h : Valid m) (n a b : Nat) :
    runP (parent false) (m.period*n) (beginP m n a b) = some (endP m n a b) := by
  obtain ⟨w,hw⟩ := pack_surj a
  obtain ⟨r,hr⟩ := pack_surj b
  rw [← hw,← hr,← enc_begin,← enc_end,← enc_run,repeat_sound m h]
  rfl

structure Rule where
  data : Macro
  proof : Valid data

inductive Cmd where
  | prim (n : Nat)
  | macro (i n a b : Nat)

def applyCmd (rules : Array Rule) (z : P) : Cmd → Option (Nat × P)
  | .prim n => (runP (parent false) n z).map (fun y => (n,y))
  | .macro i n a b => do
    let rule ← rules[i]?
    if z = beginP rule.data n a b then
      some (rule.data.period*n,endP rule.data n a b)
    else none

theorem apply_sound (rules : Array Rule) (z : P) (cmd : Cmd) (n : Nat) (y : P)
    (h : applyCmd rules z cmd = some (n,y)) :
    runP (parent false) n z = some y := by
  cases cmd with
  | prim k =>
    simp only [applyCmd] at h
    cases he : runP (parent false) k z with
    | none => simp [he] at h
    | some p =>
      simp [he] at h
      obtain ⟨hk,hp⟩ := h
      subst n; subst y; exact he
  | macro i k a b =>
    simp only [applyCmd] at h
    cases he : rules[i]? with
    | none => simp [he] at h
    | some r =>
      simp only [he,Option.bind_some] at h
      split at h
      · rename_i hz
        simp at h
        obtain ⟨hk,hy⟩ := h
        subst n; subst y; subst z
        exact packed_repeat r.data r.proof k a b
      · simp at h

def replay (rules : Array Rule) : List Cmd → P → Option (Nat × P)
  | [],z => some (0,z)
  | c::cs,z => do
    let (n,y) ← applyCmd rules z c
    let (k,w) ← replay rules cs y
    some (n+k,w)

theorem replay_sound (rules : Array Rule) (cs : List Cmd) (z : P) (n : Nat) (y : P)
    (h : replay rules cs z = some (n,y)) :
    runP (parent false) n z = some y := by
  induction cs generalizing z n y with
  | nil =>
    simp [replay] at h
    obtain ⟨hn,hy⟩ := h
    subst n; subst y; rfl
  | cons c cs ih =>
    simp only [replay] at h
    cases he : applyCmd rules z c with
    | none => simp [he] at h
    | some p =>
      rcases p with ⟨k,w⟩
      cases hf : replay rules cs w with
      | none => simp [he,hf] at h
      | some v =>
        rcases v with ⟨j,u⟩
        simp [he,hf] at h
        obtain ⟨hn,hy⟩ := h
        subst n; subst y
        exact joinP (apply_sound rules z c k w he) (ih w j u hf)

#print axioms replay_sound
end BB6.Agent3OneLBD0
