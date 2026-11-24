import Lean
set_option maxHeartbeats 0
namespace HeldMacro

inductive Q where | A | B | C | D | E | F deriving DecidableEq, Repr
open Q
structure Config where
  q : Q
  l : Nat -- nearest bit is least significant
  r : Nat -- includes head as least significant bit
  deriving DecidableEq, Repr

def step (c : Config) : Option Config :=
  let a := c.r % 2
  let l := c.l
  let r := c.r / 2
  let goR (w : Nat) (q : Q) := some ⟨q,2*l+w,r⟩
  let goL (w : Nat) (q : Q) := some ⟨q,l/2,l%2+2*w+4*r⟩
  match c.q with
  | A => if a = 0 then goR 1 B else goR 1 D
  | B => if a = 0 then goR 1 C else goL 0 D
  | C => if a = 0 then goL 0 A else goR 0 E
  | D => if a = 0 then goL 1 A else goL 1 B
  | E => if a = 0 then goR 0 F else none
  | F => if a = 0 then goL 0 A else goR 1 A

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

structure Affine where
  coeff : Nat
  off : Nat
  deriving DecidableEq, Repr
namespace Affine
def eval (a : Affine) (n : Nat) := a.coeff*n+a.off
def half (a : Affine) : Affine := ⟨a.coeff/2,a.off/2⟩
def bit (a : Affine) := a.off%2
def even (a : Affine) : Bool := a.coeff%2 == 0
def push (a : Affine) (w : Nat) : Affine := ⟨2*a.coeff,2*a.off+w⟩
def leftOut (a : Affine) (b w : Nat) : Affine := ⟨4*a.coeff,b+2*w+4*a.off⟩

theorem even_coeff (a : Affine) (h : a.even = true) : a.coeff = 2*(a.coeff/2) := by
  simp [even] at h
  omega

theorem bit_eval (a : Affine) (h : a.even = true) (x : Nat) : a.eval x % 2 = a.bit := by
  unfold eval bit
  rw [even_coeff a h, Nat.mul_assoc, Nat.mul_add_mod]

theorem half_eval (a : Affine) (h : a.even = true) (x : Nat) : a.eval x / 2 = a.half.eval x := by
  unfold eval half
  rw [even_coeff a h, Nat.mul_assoc, Nat.mul_add_div (by decide : 2 > 0)]
  simp

theorem push_eval (a : Affine) (w x : Nat) : (a.push w).eval x = 2*a.eval x+w := by
  simp [push,eval,Nat.mul_add,Nat.mul_assoc]
  omega

theorem leftOut_eval (a : Affine) (b w x : Nat) : (a.leftOut b w).eval x = b+2*w+4*a.eval x := by
  simp [leftOut,eval,Nat.mul_add,Nat.mul_assoc]
  omega
end Affine

structure SConfig where
  q : Q
  l : Affine
  r : Affine
  deriving DecidableEq, Repr

def SConfig.eval (c : SConfig) (u v : Nat) : Config := ⟨c.q,c.l.eval u,c.r.eval v⟩

-- Outer none means a symbolic coefficient cannot be divided exactly.
-- Inner none denotes the actual undefined E1 row.
def sstep (c : SConfig) : Option (Option SConfig) :=
  if !c.l.even || !c.r.even then none else
  let a := c.r.bit
  let goR (w : Nat) (q : Q) := some (some (⟨q,c.l.push w,c.r.half⟩ : SConfig))
  let goL (w : Nat) (q : Q) := some (some (⟨q,c.l.half,c.r.half.leftOut c.l.bit w⟩ : SConfig))
  match c.q with
  | A => if a = 0 then goR 1 B else goR 1 D
  | B => if a = 0 then goR 1 C else goL 0 D
  | C => if a = 0 then goL 0 A else goR 0 E
  | D => if a = 0 then goL 1 A else goL 1 B
  | E => if a = 0 then goR 0 F else some none
  | F => if a = 0 then goL 0 A else goR 1 A

theorem sstep_sound (c : SConfig) (out : Option SConfig) (h : sstep c = some out) (u v : Nat) :
    step (c.eval u v) = out.map (fun x => x.eval u v) := by
  unfold sstep at h
  split at h
  · contradiction
  · rename_i he
    have hh : c.l.even = true ∧ c.r.even = true := by simpa using he
    have hl := hh.1
    have hr := hh.2
    have hbit := Affine.bit_eval c.r hr v
    have hlbit := Affine.bit_eval c.l hl u
    have hhalf := Affine.half_eval c.r hr v
    have hlhalf := Affine.half_eval c.l hl u
    unfold step SConfig.eval
    simp only [hbit, hhalf, hlbit, hlhalf]
    cases hq : c.q <;> simp only [hq] at h ⊢ <;>
      split at h <;> simp at h <;> subst out <;> simp_all [Affine.push_eval,Affine.leftOut_eval]

def srun : Nat → SConfig → Option SConfig
  | 0,c => some c
  | n+1,c => (sstep c).bind fun o => o.bind (srun n)

theorem srun_sound (n : Nat) (c c' : SConfig) (h : srun n c = some c') (u v : Nat) :
    run n (c.eval u v) = some (c'.eval u v) := by
  induction n generalizing c with
  | zero => simp [srun] at h; subst c'; rfl
  | succ n ih =>
    simp only [srun] at h
    cases hs : sstep c with
    | none => simp [hs] at h
    | some o =>
      cases o with
      | none => simp [hs] at h
      | some d =>
        simp [hs] at h
        simp [run, sstep_sound c (some d) hs u v, ih d h]

inductive SResult where
  | next (steps : Nat) (c : SConfig)
  | stop (steps : Nat) (c : SConfig)
  deriving DecidableEq, Repr
open SResult

def symbolic (q : Q) (b a : Nat) : SResult :=
  match q with
  | A =>
    if a%2=1 then next (if a%4=1 then 5 else 3) ⟨D,⟨1,0⟩,⟨64,b+4+8*(a/4)⟩⟩
    else if a%4=2 then next 3 ⟨B,⟨1,0⟩,⟨64,b+2+8*(a/4)⟩⟩
    else if a%8=0 then next 9 ⟨B,⟨1,0⟩,⟨64,b+10+16*(a/8)⟩⟩
    else if a%16=12 then stop 3 ⟨E,⟨16,8*b+6⟩,⟨4,a/8⟩⟩
    else if a%32=4 then next 5 ⟨A,⟨16,8*b+6⟩,⟨4,a/8⟩⟩
    else next 5 ⟨A,⟨64,32*b+25⟩,⟨1,a/32⟩⟩
  | B =>
    if a%2=1 then next 1 ⟨D,⟨1,0⟩,⟨64,b+4*(a/2)⟩⟩
    else if a%4=0 then next 7 ⟨D,⟨1,0⟩,⟨64,b+4+8*(a/4)⟩⟩
    else if a%8=6 then stop 2 ⟨E,⟨8,4*b+2⟩,⟨8,a/4⟩⟩
    else if a%16=2 then next 4 ⟨A,⟨8,4*b+2⟩,⟨8,a/4⟩⟩
    else next 4 ⟨A,⟨32,16*b+9⟩,⟨2,a/16⟩⟩
  | D => next 1 ⟨if a%2=0 then A else B,⟨1,0⟩,⟨64,b+2+4*(a/2)⟩⟩
  | _ => stop 0 ⟨q,⟨2,b⟩,⟨32,a⟩⟩

def boundaryQ (q : Q) : Bool := q == A || q == B || q == D

def startS (q : Q) (b a : Nat) : SConfig := ⟨q,⟨2,b⟩,⟨32,a⟩⟩

def check (q : Q) (b a : Nat) : Bool :=
  match symbolic q b a with
  | next n c => 0 < n && srun n (startS q b a) == some c && boundaryQ c.q
  | stop n c => srun n (startS q b a) == some c && sstep c == some none

theorem finite_check (q : Q) (b : Fin 2) (a : Fin 32) (hq : boundaryQ q = true) : check q b.val a.val = true := by
  have hA : ∀ (b : Fin 2) (a : Fin 32), check A b.val a.val = true := by decide
  have hB : ∀ (b : Fin 2) (a : Fin 32), check B b.val a.val = true := by decide
  have hD : ∀ (b : Fin 2) (a : Fin 32), check D b.val a.val = true := by decide
  cases q with
  | A => exact hA b a
  | B => exact hB b a
  | D => exact hD b a
  | C | E | F => simp [boundaryQ] at hq

inductive Result where
  | next (steps : Nat) (c : Config)
  | stop (steps : Nat) (c : Config)
  deriving DecidableEq, Repr

def SResult.eval (x : SResult) (u v : Nat) : Result :=
  match x with
  | next n c => .next n (c.eval u v)
  | stop n c => .stop n (c.eval u v)

def advance (c : Config) : Result := (symbolic c.q (c.l%2) (c.r%32)).eval (c.l/2) (c.r/32)

def validResult (c : Config) : Result → Prop
  | .next n c' => 0 < n ∧ run n c = some c' ∧ boundaryQ c'.q = true
  | .stop n c' => run n c = some c' ∧ step c' = none

theorem correct (c : Config) (h : boundaryQ c.q = true) : validResult c (advance c) := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have hc : (startS c.q b.val a.val).eval (c.l/2) (c.r/32) = c := by
    cases c
    simp [b,a,startS,SConfig.eval,Affine.eval]
    omega
  have H := finite_check c.q b a h
  change validResult c ((symbolic c.q b.val a.val).eval (c.l/2) (c.r/32))
  unfold check at H
  cases he : symbolic c.q b.val a.val with
  | next n d =>
    rw [he] at H
    change (decide (0 < n) && (srun n (startS c.q b.val a.val) == some d) && boundaryQ d.q) = true at H
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at H
    have hs := srun_sound n (startS c.q b.val a.val) d H.1.2 (c.l/2) (c.r/32)
    rw [hc] at hs
    exact ⟨H.1.1,hs,H.2⟩
  | stop n d =>
    rw [he] at H
    change ((srun n (startS c.q b.val a.val) == some d) && (sstep d == some none)) = true at H
    simp only [Bool.and_eq_true,beq_iff_eq] at H
    have hs := srun_sound n (startS c.q b.val a.val) d H.1 (c.l/2) (c.r/32)
    rw [hc] at hs
    exact ⟨hs,sstep_sound d none H.2 (c.l/2) (c.r/32)⟩

theorem run_add (m n : Nat) (c : Config) : run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run,Option.bind_assoc]
    cases step c <;> simp [ih]

-- Any invariant closed under macro successors and excluding macro stops
-- establishes primitive nonhalting, including every step inside a macro.
theorem forever_of_invariant (P : Config → Prop)
    (closed : ∀ c, P c → boundaryQ c.q = true ∧ ∃ k d, advance c = .next k d ∧ P d)
    (c : Config) (hc : P c) : ∀ n, ∃ d, run n c = some d := by
  intro n
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    obtain ⟨hb,k,d,ha,hd⟩ := closed c hc
    have hs := correct c hb
    rw [ha] at hs
    obtain ⟨hk,hr,_⟩ := hs
    by_cases hle : k ≤ n
    · obtain ⟨e,he⟩ := ih (n-k) (by omega) d hd
      refine ⟨e,?_⟩
      rw [show n = k+(n-k) by omega,run_add,hr]
      exact he
    · have hk' : k = n+(k-n) := by omega
      have hs' := hr
      rw [hk',run_add] at hs'
      cases h : run n c with
      | none => simp [h] at hs'
      | some e => exact ⟨e,rfl⟩

-- The left ray is a concatenation of 1, 10 and 100 (far to near).
-- This is a semantic invariant of the macro reduction, not a sampled property.
inductive LeftWord : Nat → Prop where
  | blank : LeftWord 0
  | one {n} : LeftWord n → LeftWord (2*n+1)
  | ten {n} : LeftWord n → LeftWord (4*n+2)
  | hundred {n} : LeftWord n → LeftWord (8*n+4)

theorem LeftWord.pop {n : Nat} (h : LeftWord n) : LeftWord (n/2) := by
  cases h with
  | blank => exact .blank
  | @one n h => simpa [show (2*n+1)/2 = n by omega] using h
  | @ten n h => simpa [show (4*n+2)/2 = 2*n+1 by omega] using LeftWord.one h
  | @hundred n h => simpa [show (8*n+4)/2 = 4*n+2 by omega] using LeftWord.ten h

theorem LeftWord.push110 {n : Nat} (h : LeftWord n) : LeftWord (8*n+6) := by
  have hh := LeftWord.ten (LeftWord.one h)
  rwa [show 4*(2*n+1)+2 = 8*n+6 by omega] at hh

theorem LeftWord.push11001 {n : Nat} (h : LeftWord n) : LeftWord (32*n+25) := by
  have hh := LeftWord.one (LeftWord.hundred (LeftWord.one h))
  rwa [show 2*(8*(2*n+1)+4)+1 = 32*n+25 by omega] at hh

theorem LeftWord.push1001 {n : Nat} (h : LeftWord n) : LeftWord (16*n+9) := by
  have hh := LeftWord.one (LeftWord.hundred h)
  rwa [show 2*(8*n+4)+1 = 16*n+9 by omega] at hh

def leftShape (b : Nat) (d : SConfig) : Bool :=
  d.l == ⟨1,0⟩ || d.l == ⟨16,8*b+6⟩ || d.l == ⟨64,32*b+25⟩ ||
  d.l == ⟨8,4*b+2⟩ || d.l == ⟨32,16*b+9⟩

def checkLeft (q : Q) (b a : Nat) : Bool :=
  match symbolic q b a with
  | .next _ d => leftShape b d
  | .stop _ _ => true

theorem finite_left (q : Q) (b : Fin 2) (a : Fin 32) (hq : boundaryQ q = true) : checkLeft q b.val a.val = true := by
  have hA : ∀ (b : Fin 2) (a : Fin 32), checkLeft A b.val a.val = true := by decide
  have hB : ∀ (b : Fin 2) (a : Fin 32), checkLeft B b.val a.val = true := by decide
  have hD : ∀ (b : Fin 2) (a : Fin 32), checkLeft D b.val a.val = true := by decide
  cases q with
  | A => exact hA b a
  | B => exact hB b a
  | D => exact hD b a
  | C | E | F => simp [boundaryQ] at hq

theorem left_preserved (c d : Config) (k : Nat) (hb : boundaryQ c.q = true)
    (ha : advance c = .next k d) (hl : LeftWord c.l) : LeftWord d.l := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have H := finite_left c.q b a hb
  change (symbolic c.q b.val a.val).eval (c.l/2) (c.r/32) = .next k d at ha
  unfold checkLeft at H
  cases he : symbolic c.q b.val a.val with
  | stop n e => rw [he] at ha; simp [SResult.eval] at ha
  | next n e =>
    rw [he] at H
    change leftShape b.val e = true at H
    rw [he] at ha
    simp [SResult.eval] at ha
    obtain ⟨_,hd⟩ := ha
    rw [←hd]
    simp only [SConfig.eval]
    simp only [leftShape,Bool.or_eq_true,beq_iff_eq,or_assoc] at H
    rcases H with H|H|H|H|H <;> rw [H] <;> simp only [Affine.eval]
    · simpa using hl.pop
    · have heq : 16*(c.l/2)+(8*b.val+6) = 8*c.l+6 := by simp [b]; omega
      rw [heq]; exact hl.push110
    · have heq : 64*(c.l/2)+(32*b.val+25) = 32*c.l+25 := by simp [b]; omega
      rw [heq]; exact hl.push11001
    · have heq : 8*(c.l/2)+(4*b.val+2) = 4*c.l+2 := by simp [b]; omega
      rw [heq]; exact .ten hl
    · have heq : 32*(c.l/2)+(16*b.val+9) = 16*c.l+9 := by simp [b]; omega
      rw [heq]; exact hl.push1001

-- B always sees a 1 immediately to the right; D always sees a 0 there.
-- This removes B0's seven-step turn branch from all reachable macro states.
def controlInv (q : Q) (a : Nat) : Bool :=
  if q = B then a%4 >= 2 else if q = D then a%4 < 2 else true

def checkControl (q : Q) (b a : Nat) : Bool :=
  match symbolic q b a with
  | .next _ d =>
    (d.q != B && d.q != D) || (d.r.coeff%4 == 0 && controlInv d.q d.r.off)
  | .stop _ _ => true

theorem finite_control (q : Q) (b : Fin 2) (a : Fin 32) (hq : boundaryQ q = true) : checkControl q b.val a.val = true := by
  have hA : ∀ (b : Fin 2) (a : Fin 32), checkControl A b.val a.val = true := by decide
  have hB : ∀ (b : Fin 2) (a : Fin 32), checkControl B b.val a.val = true := by decide
  have hD : ∀ (b : Fin 2) (a : Fin 32), checkControl D b.val a.val = true := by decide
  cases q with
  | A => exact hA b a
  | B => exact hB b a
  | D => exact hD b a
  | C | E | F => simp [boundaryQ] at hq

theorem control_preserved (c d : Config) (k : Nat) (hb : boundaryQ c.q = true)
    (ha : advance c = .next k d) : controlInv d.q d.r = true := by
  let b : Fin 2 := ⟨c.l%2,by omega⟩
  let a : Fin 32 := ⟨c.r%32,by omega⟩
  have H := finite_control c.q b a hb
  change (symbolic c.q b.val a.val).eval (c.l/2) (c.r/32) = .next k d at ha
  unfold checkControl at H
  cases he : symbolic c.q b.val a.val with
  | stop n e => rw [he] at ha; simp [SResult.eval] at ha
  | next n e =>
    rw [he] at H
    change ((e.q != B && e.q != D) || (e.r.coeff%4 == 0 && controlInv e.q e.r.off)) = true at H
    rw [he] at ha
    simp [SResult.eval] at ha
    obtain ⟨_,hd⟩ := ha
    rw [←hd]
    simp only [SConfig.eval]
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at H
    rcases H with H|H
    · simp [controlInv,H.1,H.2]
    · have hmod : e.r.eval (c.r/32) % 4 = e.r.off % 4 := by
        unfold Affine.eval
        have hc : e.r.coeff = 4*(e.r.coeff/4) := by omega
        rw [hc,Nat.mul_assoc,Nat.mul_add_mod]
      unfold controlInv at H ⊢
      rw [hmod]
      exact H.2

#print axioms correct
#print axioms forever_of_invariant
#print axioms left_preserved
#print axioms control_preserved
end HeldMacro
