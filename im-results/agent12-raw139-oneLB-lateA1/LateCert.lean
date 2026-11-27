import Counter286Bridge

namespace BB6.Agent12LateA1
open Counter286 (C Ray Word z o nilRay cons tail pre rep pre_append rep_end_word)
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open BB6.Agent12Counter286 (moveC observe observe_move observed_slot)

def lookup (v : Bool) (q : Fin 6) (b : Bool) : Option Move :=
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => none
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,false,5⟩
  | 2,false => some ⟨true,false,3⟩
  | 2,true => some ⟨false,true,2⟩
  | 3,false => some ⟨false,true,4⟩
  | 3,true => some ⟨false,false,4⟩
  | 4,false => some ⟨true,false,1⟩
  | 4,true => some ⟨true,true,2⟩
  | 5,false => if v then some ⟨true,true,3⟩ else some ⟨false,false,4⟩
  | 5,true => some ⟨false,false,0⟩
  | _,_ => none

def ctr (v : Bool) : PartialMachine := fromCodes [7,24,11,22,14,9,17,16,6,11,if v then 15 else 16,0]

theorem table_match (v : Bool) (s : Slot) : ctr v s = (lookup v s.1 s.2).map some := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> cases v <;> rfl

def step (v : Bool) (c : C) : Option C := (lookup v c.q (c.r 0)).map (fun mv => moveC mv c)
def run (v : Bool) : Nat → C → Option C
  | 0,c => some c
  | n+1,c => (step v c).bind (run v n)

theorem run_add (v : Bool) (n k : Nat) (c : C) :
    run v (n+k) c = (run v n c).bind (run v k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step v c with
    | none => rfl
    | some t => exact ih t

def CF (l r : Ray) : C := ⟨2,l,r⟩
def EF (u r : Ray) : C := ⟨4,tail u,cons (u 0) r⟩
def AF (l r : Ray) : C := ⟨0,l,r⟩

def leftCost (v t : Bool) : Nat := if t && v then 7 else 3
def rightCost (t : Bool) : Nat := if t then 5 else 1
def inWord (t : Bool) : Word := if t then [z,o,z] else [o]
def bufWord (t : Bool) : Word := if t then [o,o,z] else [o]
def outWord (t : Bool) : Word := if t then [o,z,z] else [z]

theorem enter (v : Bool) (u : Ray) : run v 2 (CF (cons o u) nilRay) = some (EF u (pre [z,o] nilRay)) := by
  cases v <;> rfl

theorem left_one (v t : Bool) (u s : Ray) :
    run v (leftCost v t) (EF (pre (inWord t) u) (cons z s)) = some (EF u (cons z (pre (bufWord t) s))) := by
  cases v <;> cases t <;> rfl

theorem right_one (v t : Bool) (l r : Ray) :
    run v (rightCost t) (CF l (pre (bufWord t) r)) = some (CF (pre (outWord t) l) r) := by
  cases v <;> cases t <;> rfl

theorem delim0 (v : Bool) (w s : Ray) : run v 6 (EF (pre [z,z] w) (cons z s)) = some (CF (pre [o,z,o] w) s) := by
  cases v <;> rfl

theorem delim1 (v : Bool) (w s : Ray) : run v 10 (EF (pre [z,o,o,z] w) (cons z s)) = some (CF (pre [o,z,z,o,o] w) s) := by
  cases v <;> rfl

theorem delim2 (v : Bool) (w s : Ray) : run v 3 (EF (pre [z,o,o,o] w) (cons z s)) = some (AF w (pre [o,z,o,o,z] s)) := by
  cases v <;> rfl

theorem finish (v : Bool) (l : Ray) : run v 4 (CF l (cons o nilRay)) = some (CF (pre [o,z] l) nilRay) := by
  cases v <;> rfl


theorem left_rep (v t : Bool) (n : Nat) (u s : Ray) :
    run v (n * leftCost v t) (EF (pre (rep (inWord t) n) u) (cons z s)) =
      some (EF u (cons z (pre (rep (bufWord t) n) s))) := by
  induction n generalizing s with
  | zero => simp [rep,pre,run]
  | succ n ih =>
    rw [Nat.succ_mul, Nat.add_comm (n * leftCost v t), rep, pre_append, run_add, left_one]
    rw [Option.bind_some, ih, rep_end_word, pre_append]

theorem right_rep (v t : Bool) (n : Nat) (l r : Ray) :
    run v (n * rightCost t) (CF l (pre (rep (bufWord t) n) r)) =
      some (CF (pre (rep (outWord t) n) l) r) := by
  induction n generalizing l with
  | zero => simp [rep,pre,run]
  | succ n ih =>
    rw [Nat.succ_mul, Nat.add_comm (n * rightCost t), rep, pre_append, run_add, right_one]
    rw [Option.bind_some, ih, rep_end_word, pre_append]

-- Packed little-endian rays. Every checked arithmetic prefix identity is a tape identity.
def ray (u : Nat) : Ray := fun i => u.testBit i


theorem ray_cons (b : Bool) (u : Nat) : ray (b.toNat + 2*u) = cons b (ray u) := by
  funext i
  cases i with
  | zero => cases b <;> simp [ray, cons, Nat.testBit_zero] <;> omega
  | succ i =>
    simp only [ray, cons, Nat.testBit_succ]
    rw [show (b.toNat+2*u)/2=u by cases b <;> simp <;> omega]

def pack (w : Word) (u : Nat) : Nat :=
  match w with
  | [] => u
  | b::w => b.toNat + 2*pack w u

theorem ray_pack (w : Word) (u : Nat) : ray (pack w u) = pre w (ray u) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [pack,pre,ray_cons,ih]

def base (t : Bool) : Nat := if t then 8 else 2
def pow (t : Bool) (n : Nat) : Nat := base t ^ n
def inDigit (t : Bool) : Nat := if t then 2 else 1
def outDigit (t : Bool) : Nat := if t then 1 else 0
def geom (t : Bool) (n : Nat) : Nat := (pow t n - 1)/(base t - 1)

theorem pow_pos (t : Bool) (n : Nat) : 0 < pow t n := by
  unfold pow; apply Nat.pow_pos; cases t <;> decide

theorem geom_succ (t : Bool) (n : Nat) : geom t (n+1) = 1+base t*geom t n := by
  cases t with
  | false =>
    have hp := pow_pos false n
    simp [geom,pow,base,Nat.pow_succ] at hp ⊢
    omega
  | true =>
    have hmod : 8^n % 7 = 1 := by
      induction n with
      | zero => decide
      | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    have hp := pow_pos true n
    simp [geom,pow,base,Nat.pow_succ] at hp ⊢
    omega

theorem pack_rep_in (t : Bool) (n u : Nat) : pack (rep (inWord t) n) u = inDigit t*geom t n + pow t n*u := by
  induction n with
  | zero => cases t <;> simp [pack,rep,geom,pow,base,inDigit]
  | succ n ih =>
    rw [rep,show ∀ a b : Word, pack (a++b) u=pack a (pack b u) by intro a b; induction a <;> simp [pack, *], ih,geom_succ]
    cases t <;> simp [pack,inWord,inDigit,pow,base,Nat.pow_succ', Nat.mul_assoc] <;> omega

theorem pack_rep_out (t : Bool) (n u : Nat) : pack (rep (outWord t) n) u = outDigit t*geom t n + pow t n*u := by
  induction n with
  | zero => cases t <;> simp [pack,rep,geom,pow,base,outDigit]
  | succ n ih =>
    rw [rep,show ∀ a b : Word, pack (a++b) u=pack a (pack b u) by intro a b; induction a <;> simp [pack, *], ih,geom_succ]
    cases t <;> simp [pack,outWord,outDigit,pow,base,Nat.pow_succ', Nat.mul_assoc] <;> omega


def inp (t : Bool) (n : Nat) : Nat := inDigit t * geom t n
def outp (t : Bool) (n : Nat) : Nat := outDigit t * geom t n

theorem ray_in (t : Bool) (n u : Nat) : ray (inp t n + pow t n*u) = pre (rep (inWord t) n) (ray u) := by
  unfold inp; rw [← pack_rep_in t n u]; exact ray_pack _ _

theorem ray_out (t : Bool) (n u : Nat) : ray (outp t n + pow t n*u) = pre (rep (outWord t) n) (ray u) := by
  unfold outp; rw [← pack_rep_out t n u]; exact ray_pack _ _

theorem prefix_of_guard (t : Bool) (n u : Nat) (h : u % pow t n = inp t n) :
    ray u = pre (rep (inWord t) n) (ray (u / pow t n)) := by
  have he : inp t n + pow t n*(u/pow t n)=u := by rw [← h,Nat.mod_add_div]
  calc
    ray u = ray (inp t n + pow t n*(u/pow t n)) := congrArg ray he.symm
    _ = _ := ray_in _ _ _

-- The run-length predictor is untrusted: the arithmetic prefix guard is checked independently.
def predict (t : Bool) (u : Nat) : Nat :=
  let x := if t then 7*u+2 else u+1
  (Nat.log2 (x ^^^ (x-1))) / (if t then 3 else 1)

inductive Result where
  | back (u a b extra : Nat)
  | hit (a b : Nat)
  deriving DecidableEq, Repr

def Result.push (t : Bool) (k : Nat) : Result → Result
  | .back u a b e => .back (outp t k + pow t k*u) (a + if t then k else 0) (b + if t then 0 else k) e
  | .hit a b => .hit (a + if t then k else 0) (b + if t then 0 else k)

-- A certificate is a list of maximal or nonmaximal token runs. Only exact prefixes are trusted.
def scan : List (Bool × Nat) → Nat → Option Result
  | [],u =>
    if u%4=0 then some (.back (5+8*(u/4)) 0 0 0)
    else if u%16=6 then some (.back (25+32*(u/16)) 0 0 4)
    else if u%16=14 then some (.hit 0 0)
    else none
  | (t,k)::cert,u =>
    if 0<k ∧ u%pow t k=inp t k then
      (scan cert (u/pow t k)).map (Result.push t k)
    else none

def backTime (v : Bool) (a b e : Nat) : Nat := 6+(8+4*v.toNat)*a+4*b+e
def hitTime (v : Bool) (a b : Nat) : Nat := 3+(3+4*v.toNat)*a+3*b

def ScanSound (v : Bool) (u : Nat) (s : Ray) : Result → Prop
  | .back w a b e => run v (backTime v a b e) (EF (ray u) (cons z s)) = some (CF (ray w) s)
  | .hit a b => ∃ c, run v (hitTime v a b) (EF (ray u) (cons z s)) = some c ∧ c.q=0 ∧ c.r 0=true

theorem scan_sound (v : Bool) (cert : List (Bool × Nat)) (u : Nat) (s : Ray) (res : Result) (h : scan cert u = some res) : ScanSound v u s res := by
  induction cert generalizing u s res with
  | nil =>
    simp only [scan] at h
    split at h
    · rename_i hu
      have he : res = .back (5+8*(u/4)) 0 0 0 := (Option.some.inj h).symm
      subst res
      have hp : ray u = pre [z,z] (ray (u/4)) := by
        rw [← ray_pack]; congr 1; simp [pack,z]; omega
      have ho : ray (5+8*(u/4)) = pre [o,z,o] (ray (u/4)) := by
        rw [← ray_pack]; congr 1; simp [pack,o,z]; omega
      simp only [ScanSound,hp,ho]
      simpa [backTime] using delim0 v (ray (u/4)) s
    · split at h
      · rename_i hu
        have he : res = .back (25+32*(u/16)) 0 0 4 := (Option.some.inj h).symm
        subst res
        have hp : ray u = pre [z,o,o,z] (ray (u/16)) := by
          rw [← ray_pack]; congr 1; simp [pack,z,o]; omega
        have ho : ray (25+32*(u/16)) = pre [o,z,z,o,o] (ray (u/16)) := by
          rw [← ray_pack]; congr 1; simp [pack,o,z]; omega
        simp only [ScanSound,hp,ho]
        simpa [backTime] using delim1 v (ray (u/16)) s
      · split at h
        · rename_i hu
          have he : res = .hit 0 0 := (Option.some.inj h).symm
          subst res
          have hp : ray u = pre [z,o,o,o] (ray (u/16)) := by
            rw [← ray_pack]; congr 1; simp [pack,z,o]; omega
          simp only [ScanSound,hp,hitTime,Nat.mul_zero,Nat.add_zero]
          exact ⟨_,delim2 v (ray (u/16)) s,rfl,rfl⟩
        · simp at h
  | cons tk cert ih =>
    rcases tk with ⟨t,k⟩
    simp only [scan] at h
    split at h
    · rename_i hg
      cases hs : scan cert (u/pow t k) with
      | none => simp [hs] at h
      | some result =>
        have hr : res = Result.push t k result := (Option.some.inj (by simpa [hs] using h)).symm
        subst res
        have hh := ih (u/pow t k) (pre (rep (bufWord t) k) s) result hs
        have hp := prefix_of_guard t k u hg.2
        cases result with
        | back w a b e =>
          simp only [ScanSound,Result.push,ray_out,hp] at *
          rw [show backTime v (a + if t then k else 0) (b + if t then 0 else k) e = k*leftCost v t+backTime v a b e+k*rightCost t by cases t <;> cases v <;> simp [backTime,leftCost,rightCost] <;> omega]
          rw [run_add,run_add,left_rep,Option.bind_some,hh,Option.bind_some,right_rep]
        | hit a b =>
          simp only [ScanSound,Result.push,hp] at *
          obtain ⟨c,hc,hq,hb⟩ := hh
          refine ⟨c,?_,hq,hb⟩
          rw [show hitTime v (a + if t then k else 0) (b + if t then 0 else k) = k*leftCost v t+hitTime v a b by cases t <;> cases v <;> simp [hitTime,leftCost] <;> omega]
          rw [run_add,left_rep,Option.bind_some,hc]
    · contradiction


-- One whole C-frontier return, or a first A1 query.
inductive Event where
  | back (u da db : Nat)
  | hit (da db : Nat)
  deriving DecidableEq, Repr

def next (cert : List (Bool × Nat)) (u : Nat) : Option Event :=
  if u%2=1 then
    (scan cert (u/2)).map fun
      | .back w a b e => .back (1+4*w) (6+backTime false a b e) (6+backTime true a b e)
      | .hit a b => .hit (2+hitTime false a b) (2+hitTime true a b)
  else none

def frontier (u : Nat) : C := CF (ray u) nilRay

def choose (v : Bool) (a b : Nat) : Nat := if v then b else a

def EventSound (v : Bool) (u : Nat) : Event → Prop
  | .back w da db => run v (choose v da db) (frontier u) = some (frontier w)
  | .hit da db => ∃ c, run v (choose v da db) (frontier u) = some c ∧ c.q=0 ∧ c.r 0=true

theorem next_sound (v : Bool) (cert : List (Bool × Nat)) (u : Nat) (e : Event) (h : next cert u = some e) : EventSound v u e := by
  unfold next at h
  split at h
  · rename_i hu
    have hr : ray u = cons o (ray (u/2)) := by
      rw [← ray_cons]; congr 1; simp [o]; omega
    have he := enter v (ray (u/2))
    cases hs : scan cert (u/2) with
    | none => simp [hs] at h
    | some r =>
      have hh := scan_sound v cert (u/2) (cons o nilRay) r hs
      cases r with
      | back w a b extra =>
        simp [hs] at h; subst e
        simp only [ScanSound] at hh
        have hf : ray (1+4*w) = pre [o,z] (ray w) := by
          rw [← ray_pack]; congr 1; simp [pack,o,z]; omega
        have ht : choose v (6+backTime false a b extra) (6+backTime true a b extra) = 2+backTime v a b extra+4 := by cases v <;> simp [choose] <;> omega
        simp only [EventSound,ht,frontier,hr,hf]
        rw [run_add,run_add,he,Option.bind_some]; change (run v (backTime v a b extra) (EF (ray (u / 2)) (cons z (cons o nilRay)))).bind (run v 4) = _; rw [hh,Option.bind_some,finish]
      | hit a b =>
        simp [hs] at h; subst e
        obtain ⟨c,hc,hq,hb⟩ := hh
        have ht : choose v (2+hitTime false a b) (2+hitTime true a b) = 2+hitTime v a b := by cases v <;> rfl
        simp only [EventSound,ht,frontier,hr]
        refine ⟨c,?_,hq,hb⟩
        rw [run_add,he,Option.bind_some]; exact hc
  · simp at h

-- Accumulate complete returns from a block of certificates.
def advance : List (List (Bool × Nat)) → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | [],u,a,b => some (u,a,b)
  | cert::rest,u,a,b =>
    match next cert u with
    | some (.back w da db) => advance rest w (a+da) (b+db)
    | _ => none

theorem advance_sound (v : Bool) (certs : List (List (Bool × Nat))) (u a b w x y : Nat)
    (h : advance certs u a b = some (w,x,y)) :
    run v (choose v x y - choose v a b) (frontier u) = some (frontier w) ∧ choose v a b ≤ choose v x y := by
  induction certs generalizing u a b with
  | nil => simp [advance] at h; obtain ⟨rfl,rfl,rfl⟩ := h; simp [run]
  | cons cert rest ih =>
    simp only [advance] at h
    cases hn : next cert u with
    | none => simp [hn] at h
    | some e =>
      have he := next_sound v cert u e hn
      cases e with
      | hit da db => simp [hn] at h
      | back u' da db =>
        rw [hn] at h
        obtain ⟨hc,hge⟩ := ih u' (a+da) (b+db) h
        constructor
        · have ht : choose v x y - choose v a b = choose v da db + (choose v x y - choose v (a+da) (b+db)) := by cases v <;> simp [choose] at * <;> omega
          rw [ht,run_add,he,Option.bind_some,hc]
        · cases v <;> simp [choose] at * <;> omega


def blankC : C := ⟨0,nilRay,nilRay⟩

theorem seed (v : Bool) : run v 2 blankC = some (frontier 3) := by
  have hz : ray 0 = nilRay := by funext n; simp [ray,nilRay]
  have h3 : ray 3 = cons o (cons o nilRay) := by
    have he := ray_pack [o,o] 0
    simpa [hz,pack,pre,o] using he
  cases v <;> simp only [frontier,CF,h3] <;> rfl

theorem step_sound (v : Bool) (m : Machine) (hm : compatible (ctr v) m) (c : Config) (d : C)
    (hs : step v (observe c) = some d) :
    ∃ c', rawStep m c = some c' ∧ observe c' = d := by
  unfold step at hs
  rw [(observed_slot c).1,(observed_slot c).2] at hs
  change (lookup v (readSlot c).1 (readSlot c).2).map (fun mv => moveC mv (observe c)) = some d at hs
  cases ht : lookup v (readSlot c).1 (readSlot c).2 with
  | none => simp [ht] at hs
  | some mv =>
    have hctr : ctr v (readSlot c) = some (some mv) := by rw [table_match,ht]; rfl
    have hmv := hm _ _ hctr
    refine ⟨applyMove c mv, ?_, ?_⟩
    · simp [rawStep,hmv]
    · rw [observe_move]
      simpa [ht] using hs

theorem run_sound (v : Bool) (m : Machine) (hm : compatible (ctr v) m) (n : Nat) (c : Config) (d : C)
    (hs : run v n (observe c) = some d) :
    ∃ c', BB6Coverage.run m n c = some c' ∧ observe c' = d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl,Option.some.inj hs⟩
  | succ n ih =>
    cases ht : step v (observe c) with
    | none => simp [run,ht] at hs
    | some e =>
      obtain ⟨c',hc',he⟩ := step_sound v m hm c e ht
      have hh : run v n (observe c') = some d := by
        rw [he]; simpa [run,ht] using hs
      obtain ⟨c'',hc'',hd⟩ := ih c' hh
      refine ⟨c'',?_,hd⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have h1 : BB6Coverage.run m 1 c = some c' := by simpa [BB6Coverage.run] using hc'
      rw [h1]; exact hc''

theorem all_other_moves (v : Bool) (s : Slot) (hs : s ≠ (0,true)) : ∃ mv, ctr v s = some (some mv) := by
  rcases s with ⟨q,b⟩
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have hlt := q.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h | h | h <;> subst q <;> cases b <;> cases v <;> first | (exact ⟨_,rfl⟩) | contradiction

theorem run_total (m : Machine) (h : ∀ s, ∃ mv, m s = some mv) (n : Nat) (c : Config) : ∃ d, BB6Coverage.run m n c = some d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl⟩
  | succ n ih =>
    obtain ⟨d,hd⟩ := ih c
    obtain ⟨mv,hmv⟩ := h (readSlot d)
    refine ⟨applyMove d mv,?_⟩
    simp [BB6Coverage.run,hd,rawStep,hmv]

theorem query_weighted (v : Bool) (n B : Nat) (hb : n+6≤B)
    (h : ∃ d, run v n blankC = some d ∧ d.q=0 ∧ d.r 0=true) :
    ∀ m, compatible (ctr v) m → WeightedBound B m := by
  intro m hm k delay hk hd
  obtain ⟨d,hr,hq,hs⟩ := h
  have he : observe blank = blankC := rfl
  rw [← he] at hr
  obtain ⟨c,hc,ho⟩ := run_sound v m hm n blank d hr
  have hslot : readSlot c = (0,true) := by
    have hx := observed_slot c
    rw [ho,hq,hs] at hx
    exact Prod.ext hx.1.symm hx.2.symm
  cases hmv : m (0,true) with
  | some mv =>
    have ht : ∀ s, ∃ mv, m s = some mv := by
      intro s
      by_cases h : s = (0,true)
      · rw [h]; exact ⟨mv,hmv⟩
      · obtain ⟨mv',hp⟩ := all_other_moves v s h
        exact ⟨mv',hm s _ hp⟩
    obtain ⟨d',hd'⟩ := run_total m ht (k+1) blank
    rw [hk.2] at hd'; contradiction
  | none =>
    have hn : BB6Coverage.run m (n+1) blank = none := by
      rw [BB6Coverage.run,hc]; simp [rawStep,hslot,hmv]
    have hkn : k=n := by
      by_cases hne : k=n
      · exact hne
      · rcases Nat.lt_or_gt_of_ne hne with hlt|hgt
        · have he' : n=(k+1)+(n-(k+1)) := by omega
          rw [he',run_append,hk.2] at hc; contradiction
        · have he' : k=(n+1)+(k-(n+1)) := by omega
          have hk' := hk.1
          rw [he',run_append,hn] at hk'; contradiction
    have hdelay : delay≤5 := by
      have hmem := (List.mem_filter.mp hd).1
      simp at hmem; omega
    omega

end BB6.Agent12LateA1
