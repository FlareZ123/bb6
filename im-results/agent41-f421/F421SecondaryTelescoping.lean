import F421SecondarySize
import F421SecondaryExact

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

theorem trimLenLocal (B : Nat) (cs : List PC) : (trimQ B cs).length=cs.length := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih => simp [trimQ,ih]

/-- Universal exact leading (a,b) formula after any arithmetic successor. -/
theorem nextHeadExact (b : Nat) (cs : List PC) :
    (sNext b cs).1 = 2*2^(sNext b cs).2.2.length-1 ∧
    (sNext b cs).2.1 = 3*2^(sNext b cs).2.2.length-1 := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  unfold sNext
  rw [he]
  simp only [Prod.fst,Prod.snd,List.length_append,List.length_singleton]
  have ht := trimLenLocal 1 as
  rw [ht]
  rw [show as.length+1=as.length+1 from rfl,Nat.pow_succ]
  constructor <;> omega

/-- Exact second leading Q head is 3*2^len-1 after any positive number
    of secondary cycles, without evaluating any enormous primary coordinates. -/
theorem iterHeadExact (k a b : Nat) (cs : List PC) :
    let (a',b',ds) := sIter (k+1) (a,b,cs)
    a'=2*2^ds.length-1 ∧ b'=3*2^ds.length-1 := by
  induction k generalizing a b cs with
  | zero =>
    simp only [sIter]
    exact nextHeadExact b cs
  | succ k ih =>
    simpa only [sIter] using ih (sNext b cs).1 (sNext b cs).2.1 (sNext b cs).2.2

/-- One source successor doubles the surviving drain-cell positional scale. -/
theorem nextLengthPower (b : Nat) (cs : List PC) :
    2^(sNext b cs).2.2.length = 2*2^(drain 0 0 (dec cs)).1.length := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  simp only [sNext,he,Prod.fst,Prod.snd,List.length_append,
    List.length_singleton,trimLenLocal,Nat.pow_succ]
  ac_rfl

/-- Affine exact primary-word mass law, using only the P/Q conservation laws. -/
theorem prefixMassAffine (a b : Nat) (cs : List PC)
    (ha : a=2*2^cs.length-1)
    (hp : pSum ((sNext b cs).2.2)=pSum cs+(2*2^cs.length-1)+3)
    (hq : qSum ((sNext b cs).2.2)=qSum cs+b+
         2*(2^cs.length-2^(drain 0 0 (dec cs)).1.length))
    (hl : (drain 0 0 (dec cs)).1.length≤cs.length) :
    let (a',b',ys) := sNext b cs
    prefixMass a' b' ys+4*2^cs.length =
       prefixMass a b cs +4*2^ys.length+6*2^cs.length+1 := by
  have h := prefixMassIdentity a b cs ha hp hq hl
  have hpw := nextLengthPower b cs
  rcases he : sNext b cs with ⟨a1,b1,cs1⟩
  rw [he] at h hpw
  simp only [Prod.fst,Prod.snd] at h hpw
  simp only [he,Prod.fst,Prod.snd]
  omega

/-- Q-mass affine law, under an exact secondary leading Q run. -/
theorem qMassAffine (b : Nat) (cs : List PC)
    (hb : b=3*2^cs.length-1)
    (hq : qSum ((sNext b cs).2.2)=qSum cs+b+
      2*(2^cs.length-2^(drain 0 0 (dec cs)).1.length))
    (hl : (drain 0 0 (dec cs)).1.length≤cs.length) :
    qSum ((sNext b cs).2.2)+2^(sNext b cs).2.2.length+1 =
      qSum cs+5*2^cs.length := by
  have hd := nextLengthPower b cs
  have hm : 0<2^cs.length := Nat.pow_pos (by decide)
  have hle : 2^(drain 0 0 (dec cs)).1.length ≤ 2^cs.length :=
    Nat.pow_le_pow_right (n:=2) (by decide) hl
  omega

def lengthSum : Nat → Nat × Nat × List PC → Nat
  | 0,_ => 0
  | k+1, (_,b,cs) => 2^cs.length+lengthSum k (sNext b cs)

#print axioms nextHeadExact
#print axioms iterHeadExact
#print axioms prefixMassAffine
#print axioms qMassAffine
end F421SecondaryLifetimes
