import Raw13Coupled6OneRACost
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRABatch
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy Raw13Coupled6OneRACost
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bv (b : Bool) : Nat := if b then 1 else 0
def dig (b : Bool) : List Bool := if b then d1 else d0
def bitOut (b : Bool) (n : Nat) : Bool := (bv b+n)%2 == 1
def wraps (b : Bool) (n : Nat) : Nat := (bv b+n)/2

theorem wraps_false_succ (n : Nat) : wraps false (n+1) = wraps true n := by
  simp [wraps,bv,Nat.add_comm]
theorem wraps_true_succ (n : Nat) : wraps true (n+1) = 1+wraps false n := by
  unfold wraps bv; simp only [ite_true,ite_false,Bool.false_eq_true]; omega

theorem out_false_succ (n : Nat) : bitOut false (n+1) = bitOut true n := by
  simp [bitOut,bv,Nat.add_comm]
theorem out_true_succ (n : Nat) : bitOut true (n+1) = bitOut false n := by
  unfold bitOut bv; simp only [ite_true,ite_false,Bool.false_eq_true]
  rw [show (1+(n+1))%2=n%2 by omega,Nat.zero_add]

/-- One low bit over an arbitrary high increment system. A carry crosses a
    delimiter of 3*m ones and requests exactly 2^m high steps. -/
theorem bit_delim_batch (m n : Nat) (b : Bool) {c : Nat} {R S : List Bool}
    (hs : StepsC (wraps b n * 2^m) c R S) :
    StepsC n (8*n+c+wraps b n*fillOver m)
      (dig b ++ rep one (3*m) ++ R)
      (dig (bitOut b n) ++ rep one (3*m) ++ S) := by
  induction n generalizing b c R S with
  | zero =>
    have he : wraps b 0 * 2^m=0 := by cases b <;> simp [wraps,bv]
    rw [he] at hs
    cases hs
    cases b <;> simp [wraps,bv,bitOut,dig] <;> exact .nil _
  | succ n ih =>
    cases b with
    | false =>
      rw [wraps_false_succ] at hs ⊢
      have h := ih true hs
      have h0 : GoodC 8 (dig false ++ rep one (3*m) ++ R) (dig true ++ rep one (3*m) ++ R) := by
        simpa [dig,List.append_assoc] using good_zeroC (rep one (3*m) ++ R)
      have H := StepsC.cons h0 h
      rw [out_false_succ]
      rw [show 8*(n+1)+c+wraps true n*fillOver m=8+(8*n+c+wraps true n*fillOver m) by omega]
      exact H
    | true =>
      rw [wraps_true_succ,Nat.add_mul,Nat.one_mul] at hs
      obtain ⟨T,a,d,had,h1,h2⟩ := splitC hs
      have h := ih false h2
      have h0 : GoodC (8+a+fillOver m) (dig true ++ rep one (3*m) ++ R) (dig false ++ rep one (3*m) ++ T) := by
        simpa [dig,rep,List.append_assoc] using overflow_delimiterC 0 m a h1
      have H := StepsC.cons h0 h
      rw [out_true_succ,wraps_true_succ,Nat.add_mul,Nat.one_mul]
      rw [show 8*(n+1)+c+(fillOver m+wraps false n*fillOver m)= (8+a+fillOver m)+(8*n+d+wraps false n*fillOver m) by omega]
      exact H

/-- Width-one terminal words. The one V overflow is the only possible wrap
    before the U terminal blocks further Good increments. -/
def U : List Bool := [false,true,true]
def V : List Bool := [true]

def termBitBatch (b v : Bool) (n : Nat) : Prop :=
  wraps b n ≤ (if v then 1 else 0) →
  StepsC n (8*n+10*wraps b n) (dig b ++ if v then V else U)
    (dig (bitOut b n) ++ if v && (wraps b n == 0) then V else U)

theorem terminal_bit (b v : Bool) (n : Nat) : termBitBatch b v n := by
  unfold termBitBatch
  intro h
  have hb : bv b ≤ 1 := by cases b <;> decide
  have hv : (if v then 1 else 0 : Nat) ≤ 1 := by cases v <;> decide
  have hn : n ≤ 3 := by unfold wraps at h; omega
  have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
  rcases hc with rfl|rfl|rfl|rfl <;> cases b <;> cases v <;>
    simp [wraps,bv,bitOut,dig,U,V] at h ⊢
  all_goals first
    | exact .nil _
    | exact .cons (good_zeroC _) (.nil _)
    | exact .cons (overflowVC 0) (.nil _)
    | exact .cons (good_zeroC _) (.cons (overflowVC 0) (.nil _))
    | exact .cons (overflowVC 0) (.cons (good_zeroC _) (.nil _))
    | exact .cons (good_zeroC _) (.cons (overflowVC 0) (.cons (good_zeroC _) (.nil _)))

/-- A right word is a stack of binary digits, with an optional unary
    delimiter after each digit. The literal tail permits no increment. -/
inductive Word where
  | lit (R : List Bool)
  | term (b v : Bool)
  | bit (b : Bool) (m : Nat) (tail : Word)
  deriving Repr, DecidableEq

namespace Word

def encode : Word → List Bool
  | .lit R => R
  | .term b v => dig b ++ if v then V else U
  | .bit b m t => dig b ++ rep one (3*m) ++ t.encode

def cap : Word → Nat
  | .lit _ => 0
  | .term b v => (if v then 3 else 1)-bv b
  | .bit b m t => 2*(t.cap / 2^m + 1)-1-bv b

def advance : Word → Nat → Option (Word × Nat)
  | .lit R,n => if n=0 then some (.lit R,0) else none
  | .term b v,n => if wraps b n ≤ (if v then 1 else 0) then
      some (.term (bitOut b n) (v && wraps b n == 0),8*n+10*wraps b n) else none
  | .bit b m t,n => do
      let (u,c) ← t.advance (wraps b n*2^m)
      return (.bit (bitOut b n) m u,8*n+c+wraps b n*fillOver m)

theorem advance_sound {w u : Word} {n c : Nat} (h : w.advance n = some (u,c)) :
    StepsC n c w.encode u.encode := by
  induction w generalizing n c u with
  | lit R =>
    simp only [advance] at h
    split at h
    · rename_i hn
      subst n
      cases h
      exact .nil _
    · contradiction
  | term b v =>
    by_cases hc : wraps b n ≤ (if v then 1 else 0)
    · simp only [advance,if_pos hc,Option.some.injEq] at h
      cases h
      exact terminal_bit b v n hc
    · simp only [advance,if_neg hc] at h
      contradiction
  | bit b m t ih =>
    cases ht : t.advance (wraps b n*2^m) with
    | none => simp [advance,ht] at h
    | some a =>
      obtain ⟨v,d⟩ := a
      simp [advance,ht] at h
      obtain ⟨rfl,rfl⟩ := h
      exact bit_delim_batch m n b (ih ht)

end Word

#print axioms bit_delim_batch
#print axioms terminal_bit
#print axioms Word.advance_sound
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRABatch
