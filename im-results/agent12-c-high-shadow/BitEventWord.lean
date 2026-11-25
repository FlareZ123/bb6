import StreakWord
import BitPlanes
namespace BB6.Agent12BitEventWord
open BB6.Agent12WordBlock BB6.Agent12StreakWord BB6.Agent12BitPlanes

/-- The high bit is consumed first. A one ends an ordinary shift. -/
def word (q : Nat) (d : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => if q.testBit n then (d+1)::word q 0 n else word q (d+1) n

structure BitState where
  b : Int
  m : Nat
  o : Int
  deriving DecidableEq, Repr

def lift (s : State) : BitState := ⟨s.a+2+parity s,s.m,parity s⟩
def idle (d : Nat) (s : BitState) : BitState := ⟨(2:Int)^d*s.b,s.m+3*d,s.o⟩
def tick (e : Bool) (s : BitState) : BitState :=
  let m := s.m+3+e.toNat
  if e then ⟨2*s.b-(m:Int)+2-2*s.o+(m:Int)%2,m,(m:Int)%2⟩ else ⟨2*s.b,m,s.o⟩

def walk (q : Nat) : Nat → BitState → BitState
  | 0,s => s
  | n+1,s => walk q n (tick (q.testBit n) s)

theorem idle_zero (s : BitState) : idle 0 s=s := by cases s; simp [idle]

theorem tick_false_idle (d : Nat) (s : BitState) : tick false (idle d s)=idle (d+1) s := by
  simp only [tick,idle,Bool.toNat_false,Nat.add_zero, Bool.false_eq_true,ite_false,Int.pow_succ]
  congr 1 <;> grind

theorem tick_true_lift (d : Nat) (s : State) : tick true (idle d (lift s))=lift (step (d+1) s) := by
  simp only [tick,idle,lift,step,parity,Bool.toNat_true,ite_true,Int.pow_succ]
  push_cast
  congr 1 <;> grind

/-- An unfinished suffix of zeros is forbidden: the final bit must be a
    return. This connects the purely bitwise interpreter to ordinary words. -/
theorem walk_word (q n d : Nat) (s : State)
    (h0 : n=0 → d=0) (h1 : 0<n → q.testBit 0=true) :
    walk q n (idle d (lift s))=lift (run (word q d n) s) := by
  induction n generalizing d s with
  | zero => simp [walk,word,run,h0 rfl,idle_zero]
  | succ n ih =>
    by_cases h : q.testBit n=true
    · simp only [walk,word,h,ite_true,run,tick_true_lift]
      rw [←idle_zero (lift (step (d+1) s))]
      exact ih 0 _ (by simp) (fun _=>h1 (by omega))
    · have hfalse : q.testBit n=false := Bool.eq_false_iff.mpr h
      have hn : n≠0 := by intro he; subst n; exact h (h1 (by omega))
      simp only [walk,word,hfalse,Bool.false_eq_true,ite_false,tick_false_idle]
      exact ih (d+1) s (fun e=>False.elim (hn e)) (fun _=>h1 (by omega))

theorem word_count (q n d : Nat) (counts : List Nat) (N : Nat)
    (hn : n≤N) (hc : countCheck N q counts) :
    (word q d n).length + value counts n=value counts 0 := by
  induction n generalizing d with
  | zero => simp [word]
  | succ n ih =>
    have hrec:=count_rec N q counts hc n
    cases hb : q.testBit n
    · simp [word,hb]
      have h := ih (d+1) (by omega)
      simp [bit,hb] at hrec
      omega
    · simp [word,hb]
      have h := ih 0 (by omega)
      simp [bit,hb] at hrec
      omega

/-- Length of the consecutive one-run starting at bit j, capped at len. -/
def runLen (q : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | len+1,j => if q.testBit j then 1+runLen q len (j+1) else 0

/-- At each bit, an intersection of d+1 adjacent shifted masks. -/
def runMask (q : Nat) : Nat → Nat
  | 0 => q
  | d+1 => q&&&(runMask q d>>>1)

theorem runLen_mask (q d len j : Nat) (h : d+1≤runLen q len j) : (runMask q d).testBit j=true := by
  induction d generalizing len j with
  | zero =>
    cases len with
    | zero => simp [runLen] at h
    | succ len =>
      by_cases hb : q.testBit j=true
      · exact hb
      · simp [runLen,hb] at h
  | succ d ih =>
    cases len with
    | zero => simp [runLen] at h
    | succ len =>
      by_cases hb : q.testBit j=true
      · have h' : d+1≤runLen q len (j+1) := by simp [runLen,hb] at h; omega
        simpa [runMask,hb,Nat.add_comm] using ih len (j+1) h'
      · simp [runLen,hb] at h

theorem runLen_bound (q D len j : Nat) (h : runMask q D=0) : runLen q len j≤D := by
  by_cases hc : runLen q len j≤D
  · exact hc
  · have hh := runLen_mask q D len j (by omega)
    simp [h] at hh

def ones (q N j : Nat) : Nat := runLen q (N-j) j
def zeros (q N j : Nat) : Nat := runLen ((2^N-1)^^^q) (N-j) j

theorem ones_step (q N j : Nat) (h : j<N) :
    ones q N j=if q.testBit j then 1+ones q N (j+1) else 0 := by
  unfold ones
  rw [show N-j=(N-(j+1))+1 by omega,runLen]

theorem zeros_step (q N j : Nat) (h : j<N) :
    zeros q N j=if q.testBit j then 0 else 1+zeros q N (j+1) := by
  unfold zeros
  rw [show N-j=(N-(j+1))+1 by omega,runLen,Nat.testBit_xor,Nat.testBit_two_pow_sub_one]
  cases hb:q.testBit j <;> simp [h,hb]

/-- This parallel no-run check implies the exact ordinary-word guard. No
    decoded list or intermediate machine state is evaluated by the checker. -/
theorem word_guard (q N n d c R D E : Nat)
    (hn : n≤N) (hR : 1≤R)
    (hz : runMask ((2^N-1)^^^q) (R-1)=0) (ho : runMask q D=0)
    (hE : (runMask q E).testBit 0=false)
    (hd : d=zeros q N n) (hc : c≤D) (hco : d=0 → c≤ones q N n)
    (h0 : n=0 → d=0) (h1 : 0<n → q.testBit 0=true) :
    boundedWord R D c (word q d n)=true ∧ endStreak c (word q d n)≤E := by
  induction n generalizing d c with
  | zero =>
    have hbound : ones q N 0≤E := by
      by_cases h : ones q N 0≤E
      · exact h
      · have hh:=runLen_mask q E (N-0) 0 (by unfold ones at h; omega)
        rw [hE] at hh
        contradiction
    exact ⟨by simp [word,boundedWord,hc],by simpa [word,endStreak] using Nat.le_trans (hco (h0 rfl)) hbound⟩
  | succ n ih =>
    have hzn := zeros_step q N n (by omega)
    have hon := ones_step q N n (by omega)
    have hdmax : d≤R-1 := by rw [hd]; exact runLen_bound _ _ _ _ hz
    cases hb:q.testBit n
    · have hdz : d+1=zeros q N n := by simp [hb] at hzn; omega
      have hnz : n≠0 := by intro e; subst n; rw [h1 (by omega)] at hb; contradiction
      simp only [word,hb,Bool.false_eq_true,ite_false]
      exact ih (d+1) c (by omega) hdz hc (by omega) (fun h=>False.elim (hnz h)) (fun _=>h1 (by omega))
    · have hz0 : 0=zeros q N n := by simp [hb] at hzn; omega
      have hcnew : advance c (d+1)≤ones q N n := by
        simp only [advance]
        by_cases h : d=0
        · simp [h]; simp [hb] at hon; have h' := hco h; omega
        · simp [h]
      have hcnew' : advance c (d+1)≤D := Nat.le_trans hcnew (runLen_bound _ _ _ _ ho)
      obtain ⟨hbw,he⟩:=ih 0 (advance c (d+1)) (by omega) hz0 hcnew' (fun _=>hcnew) (by simp) (fun _=>h1 (by omega))
      simp only [word,hb,ite_true,boundedWord,endStreak]
      exact ⟨by simp [hc,show 1≤d+1 by omega,show d+1≤R by omega,hbw],he⟩

theorem word_guard_top (q N R D E : Nat) (_hN : 0<N) (hR : 1≤R)
    (hz : runMask ((2^N-1)^^^q) (R-1)=0) (ho : runMask q D=0)
    (hE : (runMask q E).testBit 0=false) (h1 : q.testBit 0=true) :
    boundedWord R D 0 (word q 0 N)=true ∧ endStreak 0 (word q 0 N)≤E :=
  word_guard q N N 0 0 R D E (by omega) hR hz ho hE (by simp [zeros,runLen]) (by omega) (by simp) (by simp) (fun _=>h1)

#print axioms walk_word
#print axioms word_count
#print axioms word_guard_top
end BB6.Agent12BitEventWord
