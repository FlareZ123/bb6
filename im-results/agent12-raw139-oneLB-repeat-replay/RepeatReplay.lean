import LateCert

namespace BB6.Agent12RepeatReplay
open Counter286 (C Ray Word z o nilRay cons tail pre rep pre_append rep_end_word)
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open BB6.Agent12Counter286 (moveC observe observe_move observed_slot)
open BB6.Agent12LateA1 (ray ray_cons pack ray_pack)

def lookup (p : PartialMachine) (q : Fin 6) (b : Bool) : Option Move := (p (q,b)).join

def step (p : PartialMachine) (c : C) : Option C := (lookup p c.q (c.r 0)).map (fun mv => moveC mv c)
def run (p : PartialMachine) : Nat → C → Option C
  | 0,c => some c
  | n+1,c => (step p c).bind (run p n)

theorem run_add (p : PartialMachine) (n k : Nat) (c : C) :
    run p (n+k) c = (run p n c).bind (run p k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step p c with
    | none => rfl
    | some t => exact ih t

-- Finite prefix windows, with the exterior rays universally quantified.
structure Window where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def Window.view (w : Window) (l r : Ray) : C := ⟨w.q,pre w.l l,pre w.r r⟩

def localStep (p : PartialMachine) (w : Window) : Option Window :=
  match w.r with
  | [] => none
  | b::r =>
    match lookup p w.q b with
    | none => none
    | some mv =>
      if mv.right then some ⟨mv.next,mv.write::w.l,r⟩
      else match w.l with
        | [] => none
        | a::l => some ⟨mv.next,l,a::mv.write::r⟩

def localRun (p : PartialMachine) : Nat → Window → Option Window
  | 0,w => some w
  | n+1,w => (localStep p w).bind (localRun p n)

theorem localStep_sound (p : PartialMachine) (w w' : Window) (l r : Ray) (h : localStep p w = some w') :
    step p (w.view l r) = some (w'.view l r) := by
  rcases w with ⟨q,L,R⟩
  cases R with
  | nil => simp [localStep] at h
  | cons b R =>
    cases hm : lookup p q b with
    | none => simp [localStep,hm] at h
    | some mv =>
      rcases mv with ⟨write,right,next⟩
      cases right with
      | true =>
        simp [localStep,hm] at h; subst w'
        simp only [step,Window.view,pre,Counter286.head_cons,hm,Option.map_some,moveC,ite_true,Counter286.tail_cons]
      | false =>
        cases L with
        | nil => simp [localStep,hm] at h
        | cons a L =>
          simp [localStep,hm] at h; subst w'
          simp only [step,Window.view,pre,Counter286.head_cons,hm,Option.map_some,moveC,Bool.false_eq_true,ite_false,Counter286.tail_cons]

theorem localRun_sound (p : PartialMachine) (n : Nat) (w w' : Window) (l r : Ray) (h : localRun p n w = some w') :
    run p n (w.view l r) = some (w'.view l r) := by
  induction n generalizing w with
  | zero => have he : w=w' := Option.some.inj h; subst w'; rfl
  | succ n ih =>
    simp only [localRun] at h
    cases hs : localStep p w with
    | none => simp [hs] at h
    | some w1 =>
      rw [run,localStep_sound p w w1 l r hs,Option.bind_some]
      exact ih w1 (by simpa [hs] using h)

structure Rule where
  q : Fin 6
  steps : Nat
  right : Bool
  l : Word
  r : Word
  consumed : Word
  produced : Word
  deriving DecidableEq, Repr

def Rule.entry (a : Rule) : Window := if a.right then ⟨a.q,a.l,a.r++a.consumed⟩ else ⟨a.q,a.l++a.consumed,a.r⟩
def Rule.exit (a : Rule) : Window := if a.right then ⟨a.q,a.l++a.produced,a.r⟩ else ⟨a.q,a.l,a.r++a.produced⟩
def Rule.valid (p : PartialMachine) (a : Rule) : Bool := decide (localRun p a.steps a.entry = some a.exit)

def Rule.input (a : Rule) (n : Nat) (l r : Ray) : C :=
  if a.right then ⟨a.q,pre a.l l,pre a.r (pre (rep a.consumed n) r)⟩
  else ⟨a.q,pre a.l (pre (rep a.consumed n) l),pre a.r r⟩
def Rule.output (a : Rule) (n : Nat) (l r : Ray) : C :=
  if a.right then ⟨a.q,pre a.l (pre (rep a.produced n) l),pre a.r r⟩
  else ⟨a.q,pre a.l l,pre a.r (pre (rep a.produced n) r)⟩

theorem repeat_sound (p : PartialMachine) (a : Rule) (h : a.valid p = true) (n : Nat) (l r : Ray) :
    run p (n*a.steps) (a.input n l r) = some (a.output n l r) := by
  have hc : localRun p a.steps a.entry = some a.exit := of_decide_eq_true h
  induction n generalizing l r with
  | zero => cases hd : a.right <;> simp [Rule.input,Rule.output,hd,rep,pre,run]
  | succ n ih =>
    cases hd : a.right with
    | true =>
      have hs := localRun_sound p a.steps a.entry a.exit l (pre (rep a.consumed n) r) hc
      simp only [Rule.entry,Rule.exit,hd,ite_true,Window.view,pre_append] at hs
      simp only [Rule.input,Rule.output,hd,ite_true,rep,pre_append]
      rw [Nat.succ_mul,Nat.add_comm (n*a.steps),run_add,hs,Option.bind_some]
      have hh := ih (pre a.produced l) r
      simp only [Rule.input,Rule.output,hd,ite_true] at hh
      rw [hh,← pre_append (rep a.produced n) a.produced,← rep_end_word,rep,pre_append]
    | false =>
      have hs := localRun_sound p a.steps a.entry a.exit (pre (rep a.consumed n) l) r hc
      simp only [Rule.entry,Rule.exit,hd,Bool.false_eq_true,ite_false,Window.view,pre_append] at hs
      simp only [Rule.input,Rule.output,hd,Bool.false_eq_true,ite_false,rep,pre_append]
      rw [Nat.succ_mul,Nat.add_comm (n*a.steps),run_add,hs,Option.bind_some]
      have hh := ih l (pre a.produced r)
      simp only [Rule.input,Rule.output,hd,Bool.false_eq_true,ite_false] at hh
      rw [hh,← pre_append (rep a.produced n) a.produced,← rep_end_word,rep,pre_append]

-- Constant-time packed prefix arithmetic (one exponentiation per repeated word).
def scale (w : Word) : Nat := 2^w.length
def value (w : Word) : Nat := pack w 0

theorem pack_eq (w : Word) (u : Nat) : pack w u = value w + scale w*u := by
  induction w with
  | nil => simp [pack,value,scale]
  | cons b w ih =>
    unfold value at *
    simp only [pack,List.length_cons,scale,Nat.pow_succ',ih,Nat.mul_add,Nat.mul_assoc]
    omega

theorem geo_exists (b : Nat) (hb : 1<b) (n : Nat) : ∃ g, b^n = 1+(b-1)*g := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨g,hg⟩ := ih
    refine ⟨1+b*g,?_⟩
    calc
      b^(n+1) = b*b^n := Nat.pow_succ' ..
      _ = b*(1+(b-1)*g) := by rw [hg]
      _ = b+(b-1)*(b*g) := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm b (b-1)]
      _ = 1+(b-1)*(1+b*g) := by rw [Nat.mul_add,Nat.mul_one]; omega

def geo (b n : Nat) : Nat := (b^n-1)/(b-1)

theorem geo_identity (b : Nat) (hb : 1<b) (n : Nat) : b^n = 1+(b-1)*geo b n := by
  obtain ⟨g,hg⟩ := geo_exists b hb n
  have he : geo b n = g := by
    unfold geo; rw [hg, Nat.add_sub_cancel_left]
    exact Nat.mul_div_cancel_left g (by omega)
  rw [he]; exact hg

theorem geo_succ (b : Nat) (hb : 1<b) (n : Nat) : geo b (n+1) = 1+b*geo b n := by
  have h : b^(n+1) = 1+(b-1)*(1+b*geo b n) := by
    calc
      b^(n+1) = b*b^n := Nat.pow_succ' ..
      _ = b*(1+(b-1)*geo b n) := by rw [← geo_identity b hb n]
      _ = b+(b-1)*(b*geo b n) := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm b (b-1)]
      _ = 1+(b-1)*(1+b*geo b n) := by rw [Nat.mul_add,Nat.mul_one]; omega
  unfold geo at h ⊢
  rw [h,Nat.add_sub_cancel_left]
  exact Nat.mul_div_cancel_left _ (by omega)

def repScale (w : Word) (n : Nat) := scale w ^ n
def repValue (w : Word) (n : Nat) := value w * geo (scale w) n

theorem pack_append (a b : Word) (u : Nat) : pack (a++b) u = pack a (pack b u) := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [pack,ih]

theorem pack_repeat (w : Word) (n u : Nat) : pack (rep w n) u = repValue w n + repScale w n * u := by
  cases w with
  | nil =>
    have h : ∀ k, rep [] k = [] := by intro k; induction k <;> simp [rep, *]
    simp [h,repValue,repScale,value,scale,pack]
  | cons b w =>
    have hs : 1<scale (b::w) := by
      simp only [scale,List.length_cons,Nat.pow_succ']
      have hp : 0<2^w.length := Nat.pow_pos (by decide)
      omega
    induction n with
    | zero => simp [rep,pack,repValue,repScale,geo]
    | succ n ih =>
      rw [rep,pack_append,pack_eq (b::w),ih]
      unfold repValue repScale
      rw [geo_succ _ hs,Nat.pow_succ']
      simp only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc,Nat.mul_left_comm (value (b::w)) (scale (b::w))]
      omega


structure Packed where
  q : Fin 6
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def Packed.view (s : Packed) : C := ⟨s.q,ray s.l,ray s.r⟩
def Packed.read (s : Packed) : Bool := s.r%2==1

def packedStep (p : PartialMachine) (s : Packed) : Option Packed :=
  (lookup p s.q s.read).map fun mv =>
    if mv.right then ⟨mv.next,mv.write.toNat+2*s.l,s.r/2⟩
    else ⟨mv.next,s.l/2,s.l%2+2*mv.write.toNat+4*(s.r/2)⟩

theorem ray_split (x : Nat) : ray x = cons (x%2==1) (ray (x/2)) := by
  have he : (x%2==1).toNat = x%2 := by
    have h : x%2=0 ∨ x%2=1 := by omega
    rcases h with h|h <;> rw [h] <;> rfl
  calc
    ray x = ray ((x%2==1).toNat+2*(x/2)) := by congr 1; omega
    _ = _ := ray_cons _ _

theorem ray_head (x : Nat) : ray x 0 = (x%2==1) := by rw [ray_split]; rfl
theorem ray_tail (x : Nat) : tail (ray x) = ray (x/2) := by rw [ray_split]; rfl

theorem packedStep_sound (p : PartialMachine) (s s' : Packed) (h : packedStep p s = some s') :
    step p s.view = some s'.view := by
  unfold packedStep at h
  cases hm : lookup p s.q s.read with
  | none => simp [hm] at h
  | some mv =>
    rcases mv with ⟨w,d,q⟩
    cases d with
    | true =>
      simp [hm] at h; subst s'
      unfold Packed.read at hm
      simp only [step,Packed.view,ray_head,hm,Option.map_some,moveC,ite_true,ray_cons,ray_tail]
    | false =>
      simp [hm] at h; subst s'
      unfold Packed.read at hm
      simp only [step,Packed.view,ray_head,hm,Option.map_some,moveC,Bool.false_eq_true,ite_false,ray_tail]
      have he : (s.l%2==1).toNat = s.l%2 := by
        have h : s.l%2=0 ∨ s.l%2=1 := by omega
        rcases h with h|h <;> rw [h] <;> rfl
      rw [show s.l%2+2*w.toNat+4*(s.r/2) = (s.l%2==1).toNat+2*(w.toNat+2*(s.r/2)) by omega,ray_cons,ray_cons]

def packedRun (p : PartialMachine) : Nat → Packed → Option Packed
  | 0,s => some s
  | n+1,s => (packedStep p s).bind (packedRun p n)

theorem packedRun_sound (p : PartialMachine) (n : Nat) (s s' : Packed) (h : packedRun p n s = some s') :
    run p n s.view = some s'.view := by
  induction n generalizing s with
  | zero => have he : s=s' := Option.some.inj h; subst s'; rfl
  | succ n ih =>
    simp only [packedRun] at h
    cases hs : packedStep p s with
    | none => simp [hs] at h
    | some s1 =>
      rw [run,packedStep_sound p s s1 hs,Option.bind_some]
      exact ih s1 (by simpa [hs] using h)

-- Prefix guards verify all consumed bits, including anchor bits.
def strip (w : Word) (x : Nat) : Option Nat :=
  if x%scale w=value w then some (x/scale w) else none

def stripRep (anchor w : Word) (n x : Nat) : Option Nat :=
  let base := scale anchor * repScale w n
  let pref := pack anchor (repValue w n)
  if x%base=pref then some (x/base) else none

def putRep (anchor w : Word) (n x : Nat) : Nat := pack anchor (repValue w n+repScale w n*x)

theorem strip_sound (w : Word) (x y : Nat) (h : strip w x = some y) : ray x = pre w (ray y) := by
  unfold strip at h
  split at h
  · rename_i hg
    have hy := Option.some.inj h
    have hx : x=pack w y := by rw [pack_eq,← hy,← hg,Nat.mod_add_div]
    rw [hx,ray_pack]
  · contradiction

theorem putRep_sound (a w : Word) (n x : Nat) : ray (putRep a w n x) = pre a (pre (rep w n) (ray x)) := by
  unfold putRep
  rw [← pack_repeat,ray_pack,ray_pack]

theorem stripRep_sound (a w : Word) (n x y : Nat) (h : stripRep a w n x = some y) :
    ray x = pre a (pre (rep w n) (ray y)) := by
  simp only [stripRep] at h
  split at h
  · rename_i hg
    have hy := Option.some.inj h
    have hx : x=putRep a w n y := by
      unfold putRep
      rw [pack_eq a (repValue w n+repScale w n*y),pack_eq a (repValue w n)] at *
      rw [Nat.mul_add,← Nat.add_assoc,← Nat.mul_assoc,← hy,← hg,Nat.mod_add_div]
    rw [hx,putRep_sound]
  · contradiction

def applyRepeat (a : Rule) (n : Nat) (s : Packed) : Option Packed :=
  if s.q=a.q then
    if a.right then do
      let l ← strip a.l s.l
      let r ← stripRep a.r a.consumed n s.r
      some ⟨a.q,putRep a.l a.produced n l,pack a.r r⟩
    else do
      let l ← stripRep a.l a.consumed n s.l
      let r ← strip a.r s.r
      some ⟨a.q,pack a.l l,putRep a.r a.produced n r⟩
  else none

theorem applyRepeat_sound (p : PartialMachine) (a : Rule) (n : Nat) (s s' : Packed) (hv : a.valid p=true)
    (h : applyRepeat a n s = some s') : run p (n*a.steps) s.view = some s'.view := by
  unfold applyRepeat at h
  split at h
  · rename_i hq
    split at h
    · rename_i hd
      cases hl : strip a.l s.l with
      | none => simp [hl] at h
      | some l =>
        cases hr : stripRep a.r a.consumed n s.r with
        | none => simp [hl,hr] at h
        | some r =>
          simp [hl,hr] at h; subst s'
          have hl' := strip_sound _ _ _ hl
          have hr' := stripRep_sound _ _ _ _ _ hr
          have hh := repeat_sound p a hv n (ray l) (ray r)
          simp only [Rule.input,Rule.output,hd,ite_true] at hh
          simpa only [Packed.view,hq,hl',hr',putRep_sound,ray_pack] using hh
    · rename_i hd
      have hd' : a.right=false := by cases he : a.right <;> simp_all
      cases hl : stripRep a.l a.consumed n s.l with
      | none => simp [hl] at h
      | some l =>
        cases hr : strip a.r s.r with
        | none => simp [hl,hr] at h
        | some r =>
          simp [hl,hr] at h; subst s'
          have hl' := stripRep_sound _ _ _ _ _ hl
          have hr' := strip_sound _ _ _ hr
          have hh := repeat_sound p a hv n (ray l) (ray r)
          simp only [Rule.input,Rule.output,hd',Bool.false_eq_true,ite_false] at hh
          simpa only [Packed.view,hq,hl',hr',putRep_sound,ray_pack] using hh
  · contradiction


-- Explicitly counted commands. Dictionary validation is separate from replay.
inductive Command where
  | raw (n : Nat)
  | repeated (id n : Nat)
  deriving DecidableEq, Repr

def command (p : PartialMachine) (rules : List Rule) (c : Command) (s : Packed) : Option (Packed×Nat) :=
  match c with
  | .raw n => (packedRun p n s).map fun s' => (s',n)
  | .repeated i n => do
    let a ← rules[i]?
    let s' ← applyRepeat a n s
    some (s',n*a.steps)

def validate (p : PartialMachine) (rules : List Rule) : Bool := rules.all (fun a => a.valid p)

theorem command_sound (p : PartialMachine) (rules : List Rule) (c : Command) (s s' : Packed) (n : Nat)
    (hv : validate p rules=true) (hc : command p rules c s = some (s',n)) :
    run p n s.view = some s'.view := by
  cases c with
  | raw k =>
    simp only [command] at hc
    cases hs : packedRun p k s with
    | none => simp [hs] at hc
    | some t =>
      simp [hs] at hc
      obtain ⟨rfl,rfl⟩ := hc
      exact packedRun_sound p k s t hs
  | repeated i k =>
    simp only [command] at hc
    cases ha : rules[i]? with
    | none => simp [ha] at hc
    | some a =>
      cases hs : applyRepeat a k s with
      | none => simp [ha,hs] at hc
      | some t =>
        simp [ha,hs] at hc
        obtain ⟨rfl,rfl⟩ := hc
        have hv' : a.valid p = true := by
          exact List.all_eq_true.mp hv a (List.mem_of_getElem? ha)
        exact applyRepeat_sound p a k s t hv' hs

def execute (p : PartialMachine) (rules : List Rule) : List Command → Packed → Nat → Option (Packed×Nat)
  | [],s,n => some (s,n)
  | c::cs,s,n => do
    let (s',k) ← command p rules c s
    execute p rules cs s' (n+k)

theorem execute_sound (p : PartialMachine) (rules : List Rule) (cs : List Command) (s s' : Packed) (a b : Nat)
    (hv : validate p rules=true) (he : execute p rules cs s a = some (s',b)) :
    run p (b-a) s.view = some s'.view ∧ a≤b := by
  induction cs generalizing s a with
  | nil => simp [execute] at he; obtain ⟨rfl,rfl⟩ := he; simp [run]
  | cons c cs ih =>
    simp only [execute] at he
    cases hc : command p rules c s with
    | none => simp [hc] at he
    | some t =>
      rcases t with ⟨u,k⟩
      have hs := command_sound p rules c s u k hv hc
      simp [hc] at he
      obtain ⟨hh,hge⟩ := ih u (a+k) he
      constructor
      · rw [show b-a=k+(b-(a+k)) by omega,run_add,hs,Option.bind_some,hh]
      · omega

def start : Packed := ⟨0,0,0⟩

theorem start_view : start.view = observe blank := by
  have hz : ray 0 = nilRay := by funext n; simp [ray,nilRay]
  simp only [start,Packed.view,hz]
  rfl

theorem step_sound (p : PartialMachine) (m : Machine) (hm : compatible p m) (c : Config) (d : C)
    (hs : step p (observe c) = some d) :
    ∃ c', rawStep m c = some c' ∧ observe c' = d := by
  unfold step at hs
  rw [(observed_slot c).1,(observed_slot c).2] at hs
  change ((p (readSlot c)).join).map (fun mv => moveC mv (observe c)) = some d at hs
  cases ht : p (readSlot c) with
  | none => simp [ht] at hs
  | some mv =>
    cases mv with
    | none => simp [ht] at hs
    | some mv =>
      have hmv := hm _ _ ht
      refine ⟨applyMove c mv, ?_, ?_⟩
      · simp [rawStep,hmv]
      · rw [observe_move]
        simpa [ht] using hs

theorem run_sound (p : PartialMachine) (m : Machine) (hm : compatible p m) (n : Nat) (c : Config) (d : C)
    (hs : run p n (observe c) = some d) :
    ∃ c', BB6Coverage.run m n c = some c' ∧ observe c' = d := by
  induction n generalizing c with
  | zero => exact ⟨c,rfl,Option.some.inj hs⟩
  | succ n ih =>
    cases ht : step p (observe c) with
    | none => simp [run,ht] at hs
    | some e =>
      obtain ⟨c',hc',he⟩ := step_sound p m hm c e ht
      have hh : run p n (observe c') = some d := by
        rw [he]; simpa [run,ht] using hs
      obtain ⟨c'',hc'',hd⟩ := ih c' hh
      refine ⟨c'',?_,hd⟩
      rw [show n+1=1+n by omega, BB6Coverage.run_append]
      have h1 : BB6Coverage.run m 1 c = some c' := by simpa [BB6Coverage.run] using hc'
      rw [h1]; exact hc''

-- Generic last-hole bound, for any exact table and physical query slot.
theorem weighted_last (p : PartialMachine) (n B : Nat) (hole : Slot) (last : Packed)
    (hbound : n+6≤B)
    (hother : ∀ s, s≠hole → ∃ mv, p s = some (some mv))
    (hquery : (last.q,last.read)=hole)
    (hreach : run p n start.view = some last.view) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hm k delay hk hd
  rw [start_view] at hreach
  obtain ⟨c,hc,ho⟩ := run_sound p m hm n blank last.view hreach
  have hslot : readSlot c = hole := by
    have hx := observed_slot c
    rw [ho] at hx
    simp only [Packed.view,ray_head] at hx
    change last.q = c.state ∧ last.read = c.tape c.head at hx
    rw [← hquery]
    exact Prod.ext hx.1.symm hx.2.symm
  cases hmv : m hole with
  | some mv =>
    have ht : ∀ s, ∃ mv, m s = some mv := by
      intro s
      by_cases h : s=hole
      · rw [h]; exact ⟨mv,hmv⟩
      · obtain ⟨mv',hp⟩ := hother s h
        exact ⟨mv',hm s _ hp⟩
    obtain ⟨d',hd'⟩ := BB6.Agent12LateA1.run_total m ht (k+1) blank
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

end BB6.Agent12RepeatReplay
