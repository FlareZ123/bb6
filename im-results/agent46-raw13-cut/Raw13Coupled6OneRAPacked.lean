import Raw13Coupled6OneRAPackedBase
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
open BB6Coverage Agent31Pump Raw13Coupled6OneRAHierarchy Raw13Coupled6OneRACost Raw13Coupled6OneRABatch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pref (k r : Nat) : Nat := 2^k-1+2^k*r

theorem pack_pref (k : Nat) (r : List Bool) : pack (rep one k ++ r)=pref k (pack r) := by
  rw [pack_append,pack_rep_one,length_rep_one]; rfl

def digP (b : Bool) : Nat := if b then 6 else 10

theorem pack_dig (b : Bool) : pack (dig b)=digP b := by cases b <;> rfl
theorem length_dig (b : Bool) : (dig b).length=4 := by cases b <;> rfl

def termP (v : Bool) : Nat := if v then 1 else 6

theorem pack_term (v : Bool) : pack (if v then V else U)=termP v := by cases v <;> rfl

inductive PWord where
 | lit (r : Nat)
 | term (b v : Bool)
 | bit (b : Bool) (m : Nat) (t : PWord)
 deriving Repr, DecidableEq
namespace PWord

def denote : PWord → List Bool
 | .lit r => decode r
 | .term b v => dig b ++ if v then V else U
 | .bit b m t => dig b ++ rep one (3*m) ++ t.denote

def enc : PWord → Nat
 | .lit r => r
 | .term b v => digP b+16*termP v
 | .bit b m t => digP b+16*pref (3*m) t.enc

theorem enc_sound (w : PWord) : pack w.denote=w.enc := by
  induction w with
  | lit r => exact pack_decode r
  | term b v => simp only [denote,enc,pack_append,pack_dig,length_dig,pack_term]
  | bit b m t ih =>
    simp only [denote,enc,List.append_assoc]
    rw [pack_append,pack_dig,length_dig,pack_pref,ih]

def cap : PWord → Nat
 | .lit _ => 0
 | .term b v => (if v then 3 else 1)-bv b
 | .bit b m t => 2*(t.cap / 2^m + 1)-1-bv b

def adv : PWord → Nat → Option (PWord × Nat)
 | .lit R,n => if n=0 then some (.lit R,0) else none
 | .term b v,n => if wraps b n ≤ (if v then 1 else 0) then
     some (.term (bitOut b n) (v && wraps b n == 0),8*n+10*wraps b n) else none
 | .bit b m t,n => do
     let (u,c) ← t.adv (wraps b n*2^m)
     return (.bit (bitOut b n) m u,8*n+c+wraps b n*fillOver m)

theorem adv_sound {w u : PWord} {n c : Nat} (h : w.adv n=some (u,c)) : StepsC n c w.denote u.denote := by
  induction w generalizing n c u with
  | lit R =>
    simp only [adv] at h
    split at h
    · rename_i hn
      subst n
      cases h
      exact .nil _
    · contradiction
  | term b v =>
    by_cases hc : wraps b n ≤ (if v then 1 else 0)
    · simp only [adv,if_pos hc,Option.some.injEq] at h
      cases h
      exact terminal_bit b v n hc
    · simp only [adv,if_neg hc] at h
      contradiction
  | bit b m t ih =>
    cases ht : t.adv (wraps b n*2^m) with
    | none => simp [adv,ht] at h
    | some a =>
      obtain ⟨v,d⟩ := a
      simp [adv,ht] at h
      obtain ⟨rfl,rfl⟩ := h
      exact bit_delim_batch m n b (ih ht)
end PWord

def onesP : Nat → Nat → Nat
 | 0,_ => 0
 | fuel+1,r => if r%2==1 then 1+onesP fuel (r/2) else 0

def digitP (r : Nat) : Option Bool :=
 if r%16==10 then some false else if r%16==6 && r>=8 then some true else none

def parseP : Nat → Nat → PWord
 | 0,r => .lit r
 | fuel+1,r =>
   match digitP r with
   | none => .lit r
   | some b =>
     let s:=r/16
     if s==1 then .term b true
     else if s==6 then .term b false
     else let k:=onesP (s.log2+1) s
          if k>0 && k%3==0 && (digitP (s/2^k)).isSome then
            .bit b (k/3) (parseP fuel (s/2^k))
          else .bit b 0 (parseP fuel s)

theorem startP_eq (z : PZ) (k : Nat) (w : PWord) (hq : z.q=0) (hl : z.l%2=0) (hr : z.r=pref k w.enc) :
  packZ (A (false::decode (z.l/2)) (rep one k ++ w.denote))=z := by
  have he : 2*(z.l/2)=z.l := by omega
  cases z
  simp only [packZ,A,pack,bv,ite_false,Nat.zero_add,pack_decode,pack_pref,PWord.enc_sound] at *
  simp_all

def fastFillP (z : PZ) (j : Nat) (w : PWord) : Option (Nat × PZ) :=
  if z.q=0 ∧ z.l%2=0 ∧ z.r=pref (3*j) w.enc then do
    let (u,c) ← w.adv (2^j)
    if z.l=0 then return (c+fillOver j+3,⟨0,0,7+8*pref (3*j) u.enc⟩)
    else return (c+fillOver j,⟨0,z.l+1,pref (3*j) u.enc⟩)
  else none

theorem fastFillP_sound {z : PZ} {j : Nat} {w : PWord} {n : Nat} {out : PZ}
    (h : fastFillP z j w=some (n,out)) : PackedOK z n out := by
  unfold fastFillP at h
  split at h
  · rename_i hz
    cases ha : w.adv (2^j) with
    | none => simp [ha] at h
    | some a =>
      obtain ⟨u,c⟩ := a
      have hs := PWord.adv_sound ha
      have hf := fillC_all j (decode (z.l/2)) hs
      have he := startP_eq z (3*j) w hz.1 hz.2.1 hz.2.2
      simp only [ha] at h
      split at h
      · rename_i hl
        have ht : decode (z.l/2)=[] := by simp [hl,decode]
        rw [ht] at hf he
        have h3 : run0 p 3 (A [true] (rep one (3*j)++u.denote)) = some (A [] ([true,true,true]++rep one (3*j)++u.denote)) := by rfl
        cases h
        have H := packed_of_run (join0 hf h3)
        rw [he] at H
        simp only [packZ,A,List.append_assoc,List.cons_append,List.nil_append,pack,pack_pref,PWord.enc_sound,bv,ite_true] at H
        rw [show 1+2*(1+2*(1+2*pref (3*j) u.enc))=7+8*pref (3*j) u.enc by omega] at H
        exact H
      · cases h
        have H := packed_of_run hf
        rw [he] at H
        have he' : 1+2*(z.l/2)=z.l+1 := by have := hz.2.1; omega
        simpa only [packZ,A,pack,bv,ite_true,pack_decode,pack_pref,PWord.enc_sound,he'] using H
  · contradiction

def fastOneP (z : PZ) (k : Nat) (w : PWord) : Option (Nat × PZ) :=
  if z.q=0 ∧ z.l%2=0 ∧ z.r=pref k w.enc then do
    let (u,c) ← w.adv 1
    return (k+c,⟨0,2^k*(1+2*(z.l/2)),u.enc⟩)
  else none

theorem fastOneP_sound {z : PZ} {k : Nat} {w : PWord} {n : Nat} {out : PZ}
    (h : fastOneP z k w=some (n,out)) : PackedOK z n out := by
  unfold fastOneP at h
  split at h
  · rename_i hz
    cases ha : w.adv 1 with
    | none => simp [ha] at h
    | some a =>
      obtain ⟨u,c⟩ := a
      have hs := PWord.adv_sound ha
      have hg : GoodC c w.denote u.denote := by cases hs with | cons h g => cases g; simpa using h
      have H := packed_of_run (hg k (decode (z.l/2)))
      rw [startP_eq z k w hz.1 hz.2.1 hz.2.2] at H
      simp only [ha] at h
      cases h
      simpa only [packZ,A,pack_append,pack_rep_zero,length_rep_zero,pack,bv,ite_true,pack_decode,PWord.enc_sound,Nat.zero_add] using H
  · contradiction

def rawTimeP (z : PZ) : Nat :=
  if z.l%2==1 then
    if z.l/2%2==1 then 2 else if z.l/4%2==1 then 4 else 3
  else
    let k:=onesP (z.r.log2+1) z.r
    let s:=z.r/2^k
    if s/2%2==0 then k+3 else if s/4%2==1 then k+4 else if s/8%2==1 then k+6 else k+4

def rawStepP (z : PZ) : Option (Nat × PZ) := do
  let t:=rawTimeP z
  let u ← runP t z
  return (t,u)

theorem rawStepP_sound {z : PZ} {n : Nat} {out : PZ} (h : rawStepP z=some (n,out)) : PackedOK z n out := by
  unfold rawStepP at h
  cases hr : runP (rawTimeP z) z with
  | none => simp [hr] at h
  | some u => simp only [hr] at h; cases h; exact packed_raw hr

def macroStepP (z : PZ) : Option (Nat × PZ) :=
  if z.q != 0 then none else
  if z.l%2==1 then rawStepP z else
  let k:=onesP (z.r.log2+1) z.r
  let w:=parseP (z.r.log2+1) (z.r/2^k)
  let f:=if k%3==0 && w.cap>=2^(k/3) then fastFillP z (k/3) w else fastOneP z k w
  match f with
  | some a => some a
  | none => rawStepP z

theorem macroStepP_sound {z : PZ} {n : Nat} {out : PZ} (h : macroStepP z=some (n,out)) : PackedOK z n out := by
  unfold macroStepP at h
  split at h
  · contradiction
  · split at h
    · exact rawStepP_sound h
    · dsimp only at h
      split at h
      · rename_i a ha
        cases h
        split at ha
        · exact fastFillP_sound ha
        · exact fastOneP_sound ha
      · exact rawStepP_sound h

def replayP : Nat → PZ → Option (Nat × PZ)
 | 0,z => some (0,z)
 | n+1,z => do
   let (a,u) ← macroStepP z
   let (b,v) ← replayP n u
   return (a+b,v)

theorem replayP_sound {k : Nat} {z : PZ} {n : Nat} {out : PZ} (h : replayP k z=some (n,out)) : PackedOK z n out := by
  induction k generalizing z n out with
  | zero => cases h; intro a ha; exact ⟨a,rfl,ha⟩
  | succ k ih =>
    cases hm : macroStepP z with
    | none => simp [replayP,hm] at h
    | some a =>
      obtain ⟨t,u⟩ := a
      cases hr : replayP k u with
      | none => simp [replayP,hm,hr] at h
      | some b =>
        obtain ⟨s,v⟩ := b
        simp [replayP,hm,hr] at h
        obtain ⟨rfl,rfl⟩ := h
        exact packed_join (macroStepP_sound hm) (ih hr)

#print axioms replayP_sound
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAReplay
