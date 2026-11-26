import SweepPumping
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.LA.Pair126
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

-- F1 writes zero and moves right; it either enters B or stays F.
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,true,if v then 5 else 1⟩)
  | _,_ => none

def O := rep [true,true]
def Zs := rep [false,false]
def G := rep [false,false,false,false]
def A (L R : List Bool) : Z0 := ⟨0,false::L,R⟩

-- Finite lists represent infinitely zero-padded tapes.
def EqL (a b : List Bool) : Prop := ∀ n, a.getD n false = b.getD n false

def EqZ (a b : Z0) : Prop := a.q=b.q ∧ EqL a.l b.l ∧ EqL a.r b.r

theorem eqL_refl (a : List Bool) : EqL a a := fun _ => rfl
theorem eqL_symm {a b : List Bool} (h : EqL a b) : EqL b a := fun n => (h n).symm
theorem eqL_trans {a b c : List Bool} (h : EqL a b) (g : EqL b c) : EqL a c := fun n => (h n).trans (g n)
theorem eqL_cons {a b : List Bool} (x : Bool) (h : EqL a b) : EqL (x::a) (x::b) := by
  intro n; cases n with
  | zero => rfl
  | succ n => exact h n

theorem eqL_head {a b : List Bool} (h : EqL a b) : a.headD false = b.headD false := by
  simpa only [headD_getD] using h 0

theorem eqL_tail {a b : List Bool} (h : EqL a b) : EqL a.tail b.tail := by
  intro n; simpa only [getD_tail] using h (n+1)

theorem eqL_zero (n : Nat) : EqL (List.replicate n false) [] := by
  induction n with
  | zero => exact eqL_refl _
  | succ n ih =>
    intro k; cases k with
    | zero => rfl
    | succ k => exact ih k

theorem eqZ_refl (a : Z0) : EqZ a a := ⟨rfl,eqL_refl _,eqL_refl _⟩
theorem eqZ_symm {a b : Z0} (h : EqZ a b) : EqZ b a := ⟨h.1.symm,eqL_symm h.2.1,eqL_symm h.2.2⟩
theorem eqZ_trans {a b c : Z0} (h : EqZ a b) (g : EqZ b c) : EqZ a c :=
  ⟨h.1.trans g.1,eqL_trans h.2.1 g.2.1,eqL_trans h.2.2 g.2.2⟩

theorem eqZ_move (mv : Move) {a b : Z0} (h : EqZ a b) : EqZ (move0 mv a) (move0 mv b) := by
  cases hr : mv.right
  · simp only [move0,hr,Bool.false_eq_true,↓reduceIte]
    exact ⟨rfl,eqL_tail h.2.1,eqL_cons _ h.2.2⟩
  · simp only [move0,hr,↓reduceIte]
    have hd := eqL_head h.2.2
    rw [hd]
    exact ⟨rfl,eqL_cons _ (eqL_cons _ (eqL_tail h.2.1)),eqL_tail h.2.2⟩

theorem eqZ_step (p : PartialMachine) {a b c : Z0} (h : EqZ a b)
    (hr : step0 p a = some c) : ∃ d, step0 p b = some d ∧ EqZ c d := by
  unfold step0 at hr ⊢
  have he : (a.q,a.l.headD false) = (b.q,b.l.headD false) := Prod.ext h.1 (eqL_head h.2.1)
  rw [← he]
  cases hs : (p (a.q,a.l.headD false)).bind id with
  | none => rw [hs] at hr; contradiction
  | some mv =>
    simp only [hs,Option.map_some,Option.some.injEq] at hr
    subst c
    exact ⟨move0 mv b,rfl,eqZ_move mv h⟩

theorem eqZ_run (p : PartialMachine) (n : Nat) {a b c : Z0} (h : EqZ a b)
    (hr : run0 p n a = some c) : ∃ d, run0 p n b = some d ∧ EqZ c d := by
  induction n generalizing a b with
  | zero =>
    simp only [run0,Option.some.injEq] at hr; subst c
    exact ⟨b,rfl,h⟩
  | succ n ih =>
    simp only [run0] at hr ⊢
    cases hs : step0 p a with
    | none => simp [hs] at hr
    | some u =>
      obtain ⟨w,hw,he⟩ := eqZ_step p h hs
      rw [hw]; simp only [Option.bind_some]
      rw [hs] at hr
      exact ih he hr

-- 1 00 advances one zero pair while adding a left one pair.
theorem adv (v : Bool) (L R : List Bool) :
    run0 (table v) 8 (A L (true::false::false::R)) = some (A (true::true::L) (true::R)) := by
  cases v <;> rfl

theorem transfer (v : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v) (8*n) (A L (true::(Zs n++R))) = some (A (O n++L) (true::R)) := by
  simpa only [A,O,Zs,List.cons_append,List.nil_append] using
    sweepR (table v) 0 [false] [true] [false,false] [true,true] 8 (adv v) n L R

theorem Zs_comm (n : Nat) (L : List Bool) : Zs n ++ false::L = false::(Zs n++L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Zs,rep,List.cons_append,List.nil_append] at ih ⊢
    rw [ih]

-- The long first odd run is consumed two cells at a time in F/B or F/F.
theorem push (v : Bool) (n : Nat) (L S : List Bool) :
    run0 (table v) (2*n+16) (A L (true::(O (n+1)++false::false::S))) =
      some (A (true::true::false::(Zs n++true::L)) (false::S)) := by
  have h0 : run0 (table v) 2 (A L (true::(O (n+1)++false::false::S))) =
      some ⟨5,true::false::true::L,true::(O n++false::false::S)⟩ := by cases v <;> rfl
  have h1 : run0 (table v) (2*n) ⟨5,true::false::true::L,true::(O n++false::false::S)⟩ =
      some ⟨5,true::(Zs n++false::true::L),true::false::false::S⟩ := by
    simpa only [O,Zs,List.cons_append,List.nil_append] using
      sweepR (table v) 5 [true] [true] [true,true] [false,false] 2
        (by intro X Y; cases v <;> rfl) n (false::true::L) (false::false::S)
  have h2 : run0 (table v) 6 ⟨5,true::(Zs n++false::true::L),true::false::false::S⟩ =
      some (A (false::(Zs n++true::L)) (true::false::true::S)) := by
    rw [Zs_comm]
    cases v <;> rfl
  have h3 : run0 (table v) 8 (A (false::(Zs n++true::L)) (true::false::true::S)) =
      some (A (true::true::false::(Zs n++true::L)) (false::S)) := by cases v <;> rfl
  have h := join0 (join0 (join0 h0 h1) h2) h3
  rw [show 2+2*n+6+8=2*n+16 by omega] at h
  exact h

-- Zero-prefix phase: E erases the leading even run on the left.
theorem zeroPhase (v : Bool) (a : Nat) (X S : List Bool) :
    run0 (table v) (8+2*a) (A (O a++false::X) (false::false::false::S)) =
      some ⟨0,X,true::(Zs (a+1)++true::true::S)⟩ := by
  have h0 : run0 (table v) 6 (A (O a++false::X) (false::false::false::S)) =
      some ⟨4,true::(O a++false::X),false::true::true::S⟩ := by cases v <;> rfl
  have h1 : run0 (table v) (2*a) ⟨4,true::(O a++false::X),false::true::true::S⟩ =
      some ⟨4,true::false::X,false::(Zs a++true::true::S)⟩ := by
    simpa only [O,Zs,List.cons_append,List.nil_append] using
      sweepL (table v) 4 [true] [false] [true,true] [false,false] 2
        (by intro L R; cases v <;> rfl) a (false::X) (true::true::S)
  have h2 : run0 (table v) 2 ⟨4,true::false::X,false::(Zs a++true::true::S)⟩ =
      some ⟨0,X,true::(Zs (a+1)++true::true::S)⟩ := by cases v <;> rfl
  have h := join0 (join0 h0 h1) h2
  rw [show 6+2*a+2=8+2*a by omega] at h
  exact h

theorem pop (v : Bool) (a b : Nat) (X S : List Bool) :
    run0 (table v) (10+2*a) (A (O a++false::true::(O b++X)) (false::false::false::S)) =
      some (A (O (b+1)++X) (false::(Zs a++true::true::S))) := by
  have h := zeroPhase v a (true::(O b++X)) S
  have h' : run0 (table v) 2 ⟨0,true::(O b++X),true::(Zs (a+1)++true::true::S)⟩ =
      some (A (O (b+1)++X) (false::(Zs a++true::true::S))) := by cases v <;> rfl
  have H := join0 h h'
  rw [show 8+2*a+2=10+2*a by omega] at H
  exact H

theorem eqL_append (p : List Bool) {a b : List Bool} (h : EqL a b) : EqL (p++a) (p++b) := by
  induction p with
  | nil => exact h
  | cons x p ih => exact eqL_cons x ih

theorem A_eq {L L' R R' : List Bool} (hl : EqL L L') (hr : EqL R R') : EqZ (A L R) (A L' R') :=
  ⟨rfl,eqL_cons false hl,hr⟩

def RelRun (p : PartialMachine) (n : Nat) (a b : Z0) : Prop :=
  ∃ z, run0 p n a = some z ∧ EqZ z b

theorem rel_exact {p : PartialMachine} {n : Nat} {a b : Z0} (h : run0 p n a = some b) :
    RelRun p n a b := ⟨b,h,eqZ_refl _⟩

theorem rel_pad {p : PartialMachine} {n : Nat} {a b a' b' : Z0}
    (ha : EqZ a a') (hb : EqZ b b') (h : run0 p n a = some b) : RelRun p n a' b' := by
  obtain ⟨z,hz,he⟩ := eqZ_run p n ha h
  exact ⟨z,hz,eqZ_trans (eqZ_symm he) hb⟩

-- A right word has positive even one-runs and positive zero gaps of length 0 mod 4.
inductive Word where
  | last (n : Nat)
  | more (n g : Nat) (w : Word)

def word : Word → List Bool
  | .last n => O (n+1)
  | .more n g w => O (n+1) ++ (false::false::false::false::(G g++word w))

abbrev Suffix := Option (Nat × Word)
def suffix : Suffix → List Bool
  | none => []
  | some (g,w) => G g++word w

def prepend : Suffix → Word
  | none => .last 0
  | some (0,.last n) => .last (n+1)
  | some (0,.more n g w) => .more (n+1) g w
  | some (g+1,w) => .more 0 g w

theorem prepend_spec (s : Suffix) : word (prepend s) = true::true::suffix s := by
  cases s with
  | none => rfl
  | some x =>
    rcases x with ⟨g,w⟩
    cases g with
    | zero => cases w <;> rfl
    | succ g => rfl

theorem Zs_double (n : Nat) : Zs (2*n) = G n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    change false::false::false::false::Zs (2*n) = false::false::false::false::G n
    rw [ih]

-- A frame stores an odd zero-run and an odd one-run. All except the bottom
-- frame have an odd one-run of length 1 mod 4.
def frame (n b : Nat) (X : List Bool) := false::(Zs n++true::(O b++X))
inductive Frames where
  | bottom (n b : Nat)
  | cons (n c : Nat) (rest : Frames)

def frames : Frames → List Bool
  | .bottom n b => frame n b []
  | .cons n c rest => frame n (2*c) (frames rest)

-- P scans a first odd one-run of at least three cells. Q erases the left
-- prefix against three leading zeros. The top counter is even at a nonempty
-- P stack, odd at a nonempty Q stack. Empty stacks have no parity restriction.
inductive Section where
  | pEmpty (a : Nat) (w : Word)
  | pStack (c : Nat) (f : Frames) (w : Word)
  | qEmpty (a : Nat) (s : Suffix)
  | qStack (c : Nat) (f : Frames) (s : Suffix)

def cfg : Section → Z0
  | .pEmpty a w => A (O a) (true::word w)
  | .pStack c f w => A (O (2*c)++frames f) (true::word w)
  | .qEmpty a s => A (O a) (false::false::false::suffix s)
  | .qStack c f s => A (O (2*c+1)++frames f) (false::false::false::suffix s)

theorem push_word (v : Bool) (w : Word) (L : List Bool) :
    ∃ n s t, 0 < t ∧ RelRun (table v) t (A L (true::word w))
      (A (true::true::false::(Zs n++true::L)) (false::false::false::suffix s)) := by
  cases w with
  | last n =>
    refine ⟨n,none,2*n+16,by omega,?_⟩
    apply rel_pad (a := A L (true::(O (n+1)++[false,false])))
      (b := A (true::true::false::(Zs n++true::L)) [false])
    · apply A_eq (eqL_refl _)
      apply eqL_cons true
      simpa only [word,List.append_nil] using eqL_append (O (n+1)) (show EqL [false,false] [] from eqL_zero 2)
    · apply A_eq (eqL_refl _)
      exact eqL_trans (eqL_zero 1) (eqL_symm (eqL_zero 3))
    · exact push v n L []
  | more n g w =>
    exact ⟨n,some (g,w),2*n+16,by omega,rel_exact (push v n L (false::false::(G g++word w)))⟩

-- After a zero-prefix phase with a nonminimal frame, all the newly exposed
-- zero pairs can be transferred back at once, yielding the next P section.
theorem drain (v : Bool) (a n b : Nat) (X S : List Bool) :
    run0 (table v) (8+2*a+8*(a+1))
      (A (O a++frame (n+1) b X) (false::false::false::S)) =
    some (A (O (a+1)++frame n b X) (true::true::true::S)) := by
  have h := zeroPhase v a (false::frame n b X) S
  exact join0 h (transfer v (a+1) (frame n b X) (true::true::S))

theorem empty_drain (v : Bool) (a : Nat) (S : List Bool) :
    RelRun (table v) (8+2*a+8*(a+1))
      (A (O a) (false::false::false::S))
      (A (O (a+1)) (true::true::true::S)) := by
  have h := zeroPhase v a [false] S
  have H := join0 h (transfer v (a+1) [] (true::true::S))
  apply rel_pad (a := A (O a++[false,false]) (false::false::false::S))
    (b := A (O (a+1)++[]) (true::true::true::S))
  · apply A_eq _ (eqL_refl _)
    simpa only [List.append_nil] using eqL_append (O a) (show EqL [false,false] [] from eqL_zero 2)
  · rw [List.append_nil]; exact eqZ_refl _
  · exact H

theorem pop_odd (v : Bool) (c b : Nat) (X : List Bool) (s : Suffix) :
    run0 (table v) (10+2*(2*c+1))
      (A (O (2*c+1)++frame 0 b X) (false::false::false::suffix s)) =
    some (A (O (b+1)++X) (false::false::false::suffix (some (c,prepend s)))) := by
  have h := pop v (2*c+1) b X (suffix s)
  rw [show Zs (2*c+1) = false::false::G c by
    change false::false::Zs (2*c) = false::false::G c
    rw [Zs_double]] at h
  simpa only [frame,Zs,rep,List.nil_append,suffix,prepend_spec,List.cons_append] using h

theorem sectionReturn (v : Bool) (u : Section) :
    ∃ t u', 0 < t ∧ RelRun (table v) t (cfg u) (cfg u') := by
  cases u with
  | pEmpty a w =>
    obtain ⟨n,s,t,hp,h⟩ := push_word v w (O a)
    exact ⟨t,.qStack 0 (.bottom n a) s,hp,by simpa only [cfg,frames,frame,List.append_nil,List.nil_append,show O (2*0+1) = [true,true] by rfl,List.cons_append] using h⟩
  | pStack c f w =>
    obtain ⟨n,s,t,hp,h⟩ := push_word v w (O (2*c)++frames f)
    exact ⟨t,.qStack 0 (.cons n c f) s,hp,h⟩
  | qEmpty a s =>
    refine ⟨8+2*a+8*(a+1),.pEmpty (a+1) (prepend s),by omega,?_⟩
    simpa only [cfg,prepend_spec] using empty_drain v a (suffix s)
  | qStack c f s =>
    cases f with
    | bottom n b =>
      cases n with
      | zero =>
        refine ⟨10+2*(2*c+1),.qEmpty (b+1) (some (c,prepend s)),by omega,?_⟩
        exact rel_exact (by simpa only [cfg,frames,List.append_nil] using pop_odd v c b [] s)
      | succ n =>
        refine ⟨8+2*(2*c+1)+8*((2*c+1)+1),.pStack (c+1) (.bottom n b) (prepend s),by omega,?_⟩
        apply rel_exact
        simpa only [cfg,frames,prepend_spec,show 2*c+1+1=2*(c+1) by omega] using
          drain v (2*c+1) n b [] (suffix s)
    | cons n d rest =>
      cases n with
      | zero =>
        refine ⟨10+2*(2*c+1),.qStack d rest (some (c,prepend s)),by omega,?_⟩
        exact rel_exact (pop_odd v c (2*d) (frames rest) s)
      | succ n =>
        refine ⟨8+2*(2*c+1)+8*((2*c+1)+1),.pStack (c+1) (.cons n d rest) (prepend s),by omega,?_⟩
        apply rel_exact
        simpa only [cfg,frames,prepend_spec,show 2*c+1+1=2*(c+1) by omega] using
          drain v (2*c+1) n (2*d) (frames rest) (suffix s)

/-- All live-prefix lengths are unbounded, starting from the authentic blank.
The padded equivalence is a bisimulation on the original source zipper. -/
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  have first : EqZ (cfg (.qEmpty 0 none)) ⟨0,[],[]⟩ := by
    exact ⟨rfl,eqL_zero 1,eqL_zero 3⟩
  have arbitrary : ∀ k : Nat, ∃ t z u, k ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some z ∧ EqZ (cfg u) z := by
    intro k
    induction k with
    | zero => exact ⟨0,⟨0,[],[]⟩,.qEmpty 0 none,by omega,rfl,first⟩
    | succ k ih =>
      obtain ⟨t,z,u,ht,hr,he⟩ := ih
      obtain ⟨s,u',hs,w,hw,he'⟩ := sectionReturn v u
      obtain ⟨z',hz',hzz⟩ := eqZ_run (table v) s he hw
      exact ⟨t+s,z',u',by omega,join0 hr hz',eqZ_trans (eqZ_symm he') hzz⟩
  intro n
  obtain ⟨t,z,u,ht,hr,_⟩ := arbitrary n
  have hz : (zrun (table v) t start).map project = some z := (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms sectionReturn
#print axioms never
end BB6.Agent8Raw54.LA.Pair126
