import RepeatReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent12DigitCarry
open Counter286 (C Ray Word z o nilRay cons pre tail)
open BB6Coverage hiding run
open BB6Coverage.FAR
open BB6.Agent12RepeatReplay (run run_add step lookup run_sound)
open BB6.Agent12Counter286 (observe moveC)

def Plus (p : PartialMachine) (c d : C) : Prop := ∃ n, 0<n ∧ run p n c = some d
 theorem Plus.trans {p c d e} (h : Plus p c d) (g : Plus p d e) : Plus p c e := by
  obtain ⟨n,hn,hn'⟩ := h; obtain ⟨k,hk,hk'⟩ := g
  exact ⟨n+k,by omega,by rw [run_add,hn']; exact hk'⟩

theorem prefix_run (p : PartialMachine) (n k : Nat) (c d : C) (h : run p (n+k) c = some d) : ∃ e, run p n c = some e := by
  rw [run_add] at h
  cases hn : run p n c with
  | none => simp [hn] at h
  | some e => exact ⟨e,rfl⟩

theorem never_of_inv (p : PartialMachine) (I : C → Prop) (h0 : I (observe blank))
    (hs : ∀ c, I c → ∃ d, Plus p c d ∧ I d) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have H : ∀ n, ∃ k d, n ≤ k ∧ run p k (observe blank) = some d ∧ I d := by
    intro n; induction n with
    | zero => exact ⟨0,observe blank,by omega,rfl,h0⟩
    | succ n ih =>
      obtain ⟨k,c,hk,hc,hi⟩ := ih
      obtain ⟨d,⟨l,hl,hd⟩,hj⟩ := hs c hi
      exact ⟨k+l,d,by omega,by rw [run_add,hc]; exact hd,hj⟩
  intro n
  obtain ⟨k,d,hk,hd,_⟩ := H n
  have he : n+(k-n)=k := by omega
  rw [← he] at hd
  obtain ⟨e,he⟩ := prefix_run p n (k-n) (observe blank) d hd
  obtain ⟨c,hc,_⟩ := run_sound p m hm n blank e he
  change (BB6Coverage.run m n blank).isSome = true
  rw [hc]; rfl

def repeatBit (b : Bool) : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => cons b (repeatBit b n r)
 theorem repeatBit_add (b : Bool) (n k : Nat) (r : Ray) : repeatBit b (n+k) r = repeatBit b n (repeatBit b k r) := by
  induction n with
  | zero => simp [repeatBit]
  | succ n ih => rw [show n+1+k=n+k+1 by omega]; simp [repeatBit,ih]

theorem reset (p : PartialMachine) (h0 : lookup p 5 false = some ⟨false,true,0⟩)
    (h1 : lookup p 5 true = some ⟨false,false,5⟩) (n : Nat) (r : Ray) :
    run p (n+2) ⟨5,repeatBit true n nilRay,cons true r⟩ = some ⟨0,nilRay,repeatBit false (n+1) r⟩ := by
  induction n generalizing r with
  | zero =>
    change run p 2 ⟨5,nilRay,cons true r⟩ = _
    simp only [repeatBit,run,step,Counter286.head_cons,h0,h1,Option.map_some,moveC,Bool.false_eq_true,ite_false,Counter286.tail_cons,Counter286.cons_zero_blank,Option.bind_some,Counter286.nilRay]
    change some (⟨0,cons false nilRay,cons false r⟩ : C) = _
    rw [Counter286.cons_zero_blank]
  | succ n ih =>
    have h : run p (n+2) ⟨5,repeatBit true n nilRay,cons true (cons false r)⟩ = some ⟨0,nilRay,repeatBit false (n+1) (cons false r)⟩ := ih (cons false r)
    change (step p ⟨5,cons true (repeatBit true n nilRay),cons true r⟩).bind (run p (n+2)) = _
    simp only [step,lookup,Counter286.head_cons] at * -- simplify step using the slot equations below
    change (p (5,true)).join = some ⟨false,false,5⟩ at h1
    simp only [h1,Option.map_some,moveC,Bool.false_eq_true,ite_false,Counter286.head_cons,Counter286.tail_cons,Option.bind_some]
    rw [h, repeatBit_add false (n+1) 1]; rfl

-- A finite low-endian list of digits, with arbitrarily many implicit zero digits.
structure Spec (p : PartialMachine) where
  base : Nat
  width : Nat
  positive : 0<base
  digits : Fin base → Word
  zeroWord : digits ⟨0,positive⟩ = List.replicate width false
  nonmax : ∀ (d : Fin base), ∀ (h : d.val+1 < base), ∀ L R,
    Plus p ⟨0,L,cons false (pre (digits d) R)⟩ ⟨5,L,cons true (pre (digits ⟨d.val+1,h⟩) R)⟩
  carry : ∀ (d : Fin base), d.val+1 = base → ∀ L R,
    Plus p ⟨0,L,cons false (pre (digits d) R)⟩ ⟨0,repeatBit true width L,cons false R⟩
  h0 : lookup p 5 false = some ⟨false,true,0⟩
  h1 : lookup p 5 true = some ⟨false,false,5⟩
  gtOne : 1<base

def encode {p} (s : Spec p) : List (Fin s.base) → Ray
  | [] => nilRay
  | d::ds => pre (s.digits d) (encode s ds)
 theorem pre_replicate (b : Bool) (n : Nat) (r : Ray) : pre (List.replicate n b) r = repeatBit b n r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,pre,repeatBit,ih]
 theorem repeat_zero_nil (n : Nat) : repeatBit false n nilRay = nilRay := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatBit,ih]
 theorem zero_digit {p} (s : Spec p) (r : Ray) : pre (s.digits ⟨0,s.positive⟩) r = repeatBit false s.width r := by rw [s.zeroWord,pre_replicate]
 theorem encode_zeros {p} (s : Spec p) (k : Nat) (ds : List (Fin s.base)) :
    encode s (List.replicate k ⟨0,s.positive⟩ ++ ds) = repeatBit false (s.width*k) (encode s ds) := by
  induction k with
  | zero => simp [repeatBit]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,encode,zero_digit,ih,Nat.mul_succ,Nat.add_comm (s.width*k),repeatBit_add]

theorem next {p} (s : Spec p) (ds : List (Fin s.base)) (k : Nat) :
    ∃ es, Plus p ⟨0,repeatBit true (s.width*k) nilRay,cons false (encode s ds)⟩
      ⟨0,nilRay,cons false (encode s es)⟩ := by
  induction ds generalizing k with
  | nil =>
    let d : Fin s.base := ⟨0,s.positive⟩
    have h : d.val+1<s.base := s.gtOne
    have ha := s.nonmax d h (repeatBit true (s.width*k) nilRay) nilRay
    have hz : pre (s.digits d) nilRay = nilRay := by rw [zero_digit,repeat_zero_nil]
    rw [hz] at ha
    let e : Fin s.base := ⟨d.val+1,h⟩
    have hb := reset p s.h0 s.h1 (s.width*k) (pre (s.digits e) nilRay)
    have he : repeatBit false (s.width*k+1) (pre (s.digits e) nilRay) = cons false (encode s (List.replicate k d ++ [e])) := by
      rw [encode_zeros]; rw [show s.width*k+1=1+s.width*k by omega,repeatBit_add]; rfl
    rw [he] at hb
    exact ⟨_,ha.trans ⟨_,by omega,hb⟩⟩
  | cons d ds ih =>
    by_cases h : d.val+1 < s.base
    · have ha := s.nonmax d h (repeatBit true (s.width*k) nilRay) (encode s ds)
      let e : Fin s.base := ⟨d.val+1,h⟩
      have hb := reset p s.h0 s.h1 (s.width*k) (pre (s.digits e) (encode s ds))
      have he : repeatBit false (s.width*k+1) (pre (s.digits e) (encode s ds)) = cons false (encode s (List.replicate k ⟨0,s.positive⟩ ++ e::ds)) := by
        rw [encode_zeros]; rw [show s.width*k+1=1+s.width*k by omega,repeatBit_add]; rfl
      rw [he] at hb
      exact ⟨_,ha.trans ⟨_,by omega,hb⟩⟩
    · have h' : d.val+1=s.base := by have := d.isLt; omega
      have ha := s.carry d h' (repeatBit true (s.width*k) nilRay) (encode s ds)
      rw [← repeatBit_add, Nat.add_comm s.width, ← Nat.mul_succ] at ha
      obtain ⟨es,hb⟩ := ih (k+1)
      exact ⟨es,ha.trans hb⟩

theorem never {p} (s : Spec p) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_inv p (fun c => ∃ ds, c = ⟨0,nilRay,cons false (encode s ds)⟩) _ _ m hm
  · exact ⟨[],by change Counter286.blankC = _; simp [Counter286.blankC,encode]⟩
  · intro c hc; obtain ⟨ds,rfl⟩ := hc
    obtain ⟨es,he⟩ := next s ds 0
    exact ⟨_,he,es,rfl⟩

namespace R3312
def parent : PartialMachine := fromCodes [7,24,11,23,13,16,14,9,6,3,1,20]
def digit (d : Fin 3) : Word := match d.val with
  | 0 => [z,z,z,z,z]
  | 1 => [z,z,o,z,z]
  | _ => [z,z,o,o,o]
def spec : Spec parent where
  base := 3
  width := 5
  positive := by decide
  digits := digit
  zeroWord := rfl
  nonmax := by
    intro d h L R
    have hd : d=0 ∨ d=1 := by omega
    rcases hd with rfl|rfl
    · exact ⟨10,by decide,rfl⟩
    · exact ⟨14,by decide,rfl⟩
  carry := by
    intro d h L R
    have hd : d=2 := by omega
    subst d
    exact ⟨13,by decide,rfl⟩
  h0 := rfl
  h1 := rfl
  gtOne := by decide
 theorem never (m : Machine) (hm : compatible parent m) : NeverHalts m := BB6.Agent12DigitCarry.never spec m hm
#print axioms never
end R3312

namespace R23138
def parent : PartialMachine := fromCodes [7,22,11,24,13,18,14,9,3,19,1,20]
def digit (d : Fin 2) : Word := if d.val=0 then [z,z,z,z,z] else [z,o,o,z,z]
def spec : Spec parent where
  base := 2
  width := 5
  positive := by decide
  digits := digit
  zeroWord := rfl
  nonmax := by
    intro d h L R
    have hd : d=0 := by omega
    subst d
    exact ⟨10,by decide,rfl⟩
  carry := by
    intro d h L R
    have hd : d=1 := by omega
    subst d
    exact ⟨7,by decide,rfl⟩
  h0 := rfl
  h1 := rfl
  gtOne := by decide
 theorem never (m : Machine) (hm : compatible parent m) : NeverHalts m := BB6.Agent12DigitCarry.never spec m hm
#print axioms never
end R23138
end BB6.Agent12DigitCarry
