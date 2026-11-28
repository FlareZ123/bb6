import Raw14042DTerminals
import Raw14042CTerminals
import Raw14042BTerminals
import Raw14042MixedTerminals
import Raw14042Right
import Raw14042C

namespace Raw14042SourceReach
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042ArithmeticInvariant
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary

abbrev R := Reach M42

def aTail : Nat → Raw140ERSuffix.Tail
  | 0 => .t542 | 1 => .t152 | 2 => .t1121
  | 3 => .t5215 | 4 => .t1155 | 5 => .t11511
  | _ => .t542

def bTail : Nat → Raw140Double.Tail
  | 0 => .s62 | 1 => .s64 | 2 => .s6221
  | 3 => .s6421 | 4 => .s6405 | 5 => .s62542
  | _ => .s62

def cTail : Nat → Raw14042Counter.CTail
  | 0 => .c31 | 1 => .c32 | 2 => .c315
  | 3 => .c325 | 4 => .c3242 | 5 => .c35221
  | _ => .c31

theorem aTail_rank (s : Nat) (hs : s < 6) : Raw14042BGeneral.arank (aTail s) = s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bTail_rank (s : Nat) (hs : s < 6) : Raw140Double.rank (bTail s) = s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cTail_rank (s : Nat) (hs : s < 6) : Raw14042CGeneral.crank (cTail s) = s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem aTail_unique (t : Raw140ERSuffix.Tail) (s : Nat) (hs : s<6)
    (h : Raw14042BGeneral.arank t=s) : t=aTail s := by
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases t <;> simp_all [aTail,Raw14042BGeneral.arank]

private theorem bTail_unique (t : Raw140Double.Tail) (s : Nat) (hs : s<6)
    (h : Raw140Double.rank t=s) : t=bTail s := by
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases t <;> simp_all [bTail,Raw140Double.rank]

private theorem cTail_unique (t : Raw14042Counter.CTail) (s : Nat) (hs : s<6)
    (h : Raw14042CGeneral.crank t=s) : t=cTail s := by
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases t <;> simp_all [cTail,Raw14042CGeneral.crank]

theorem aTail_next (s : Nat) (hs : s<6) :
    Raw140ERSuffix.rho (aTail s)=aTail (Raw14042ArithmeticInvariant.next s) := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bTail_next (s : Nat) (hs : s<6) :
    Raw140Double.rho (bTail s)=bTail (Raw14042ArithmeticInvariant.next s) := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cTail_next (s : Nat) (hs : s<6) :
    Raw14042Counter.next (cTail s)=cTail (Raw14042ArithmeticInvariant.next s) := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem aTail_carry (s : Nat) (hs : s<6) :
    Raw14042Bank.extra (aTail s)=Raw14042ArithmeticInvariant.carry s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bTail_carry (s : Nat) (hs : s<6) :
    Raw140Double.carry (bTail s)=Raw14042ArithmeticInvariant.carry s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem cTail_carry (s : Nat) (hs : s<6) :
    Raw14042Counter.ccarry (cTail s)=Raw14042ArithmeticInvariant.carry s := by
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem bTrip_eq (n : Nat) : Raw14042DGeneral.TB n = Raw14042Right.T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Raw14042DGeneral.TB,Raw140Double.trips,Raw140Double.triple,
      Raw140Double.word,Bool.false_eq_true,ite_false,ite_true,
      Raw14042Right.T,List.cons_append,List.nil_append,ih]

def encode (x : Section) : Prim :=
  match x.kind with
  | .a => Raw14042BGeneral.aCfg x.p x.n (aTail x.s)
  | .b => boundary 1 true (U 5 x.p) (Raw14042Right.T x.n ++ Raw140Double.tailWord (bTail x.s))
  | .c => Raw14042CGeneral.cCfg x.p x.n (cTail x.s)

theorem aOut {src : Prim} {p n r : Nat} (hr : r<6)
    (h : ∃ t : Raw140ERSuffix.Tail, Raw14042BGeneral.arank t=r ∧
      R src (Raw14042BGeneral.aCfg p n t)) :
    R src (encode ⟨.a,p,n,r⟩) := by
  obtain ⟨t,ht,hR⟩ := h
  have he := aTail_unique t r hr ht
  subst t
  simpa only [encode] using hR

theorem bOut {src : Prim} {p n r : Nat} (hr : r<6)
    (h : ∃ t : Raw140Double.Tail, Raw140Double.rank t=r ∧
      R src (Raw14042DGeneral.B p n t)) :
    R src (encode ⟨.b,p,n,r⟩) := by
  obtain ⟨t,ht,hR⟩ := h
  have he := bTail_unique t r hr ht
  subst t
  simp only [Raw14042DGeneral.B] at hR
  rw [bTrip_eq] at hR
  simpa only [encode] using hR

theorem cOut {src : Prim} {p n r : Nat} (hr : r<6)
    (h : ∃ t : Raw14042Counter.CTail, Raw14042CGeneral.crank t=r ∧
      R src (Raw14042CGeneral.cCfg p n t)) :
    R src (encode ⟨.c,p,n,r⟩) := by
  obtain ⟨t,ht,hR⟩ := h
  have he := cTail_unique t r hr ht
  subst t
  simpa only [encode] using hR

theorem dRROdd (k h : Nat) (s : Raw140Double.Tail) (src : Prim)
    (ho : (k+h)%2=1) (H : Raw14042DTerminals.RR k h s src) :
    R src (encode ⟨.b,2*(k+h)+2,(k+Raw140Double.rank s)/6,
      (k+Raw140Double.rank s)%6⟩) := by
  apply bOut (Nat.mod_lt _ (by decide))
  simpa only [Raw14042DTerminals.RR] using H

theorem dRR (k h : Nat) (src : Prim) (ho : (k+h)%2=1)
    (H : Raw14042DTerminals.RR k h .s62 src) :
    R src (encode (Raw14042ArithmeticInvariant.d k h)) := by
  have G := dRROdd k h .s62 src ho H
  simpa only [Raw14042ArithmeticInvariant.d,ho,if_pos,Raw140Double.rank,
    Nat.add_zero] using G

theorem ccRR (k m : Nat) (s : Raw14042Counter.CTail) (src : Prim)
    (he : (m+k)%2=0) (H : Raw14042CTerminals.RR k m s src) :
    R src (encode (Raw14042ArithmeticInvariant.cc k m (Raw14042CGeneral.crank s))) := by
  let r := (Raw14042CGeneral.crank s+k+2)%6
  have G : R src (encode ⟨.c,2*(k+m)+6,(k+Raw14042CGeneral.crank s+2)/6,r⟩) := by
    apply cOut (Nat.mod_lt _ (by decide))
    simpa only [Raw14042CTerminals.RR,Nat.add_comm k m,Nat.add_comm (Raw14042CGeneral.crank s) k,
      r] using H
  simpa only [Raw14042ArithmeticInvariant.cc,he,if_pos,Nat.add_comm k m,
    Nat.add_comm k (Raw14042CGeneral.crank s),r] using G

theorem bsRR (k u v : Nat) (s : Raw140ERSuffix.Tail) (src : Prim)
    (ho : (k+v+1)%2=1) (H : Raw14042BTerminals.RR k u v s src) :
    R src (encode (Raw14042ArithmeticInvariant.bs k u v (Raw14042BGeneral.arank s))) := by
  let q := k+Raw14042BGeneral.arank s
  let r := q%6
  let r' := Raw14042ArithmeticInvariant.next r
  have hrlt : r<6 := Nat.mod_lt _ (by decide)
  have hq : 6*(q/6)+r=q := by
    dsimp [r]
    omega
  have hdiv : u+(k+Raw14042BGeneral.arank s+1)/6-1 =
      q/6+u+Raw14042ArithmeticInvariant.carry r-1 := by
    dsimp [q,r]
    simp only [Raw14042ArithmeticInvariant.carry]
    split <;> omega
  have hmod : (k+Raw14042BGeneral.arank s+1)%6 = r' := by
    dsimp [q,r,r',Raw14042ArithmeticInvariant.next]
    omega
  have G : R src (encode ⟨.a,2*(k+v+1)+6,
      u+(k+Raw14042BGeneral.arank s+1)/6-1,
      (k+Raw14042BGeneral.arank s+1)%6⟩) := by
    apply aOut (Nat.mod_lt _ (by decide))
    simpa only [Raw14042BTerminals.RR] using H
  rw [hdiv,hmod] at G
  simpa only [Raw14042ArithmeticInvariant.bs,ho,if_pos,q,r,r'] using G

theorem drain_reach (x : Section) (hx : good x) (hn : 2≤x.n) :
    R (encode x) (encode (drainStep x)) := by
  rcases hx with ⟨hp,he,hs⟩
  cases hk : x.kind with
  | a =>
    have h := Raw14042Bank.return42 (x.n-2) (x.p-1) (aTail x.s)
    have hnext := aTail_next x.s hs
    have hcarry := aTail_carry x.s hs
    simpa only [encode,hk,drainStep,Raw14042BGeneral.aCfg,
      show x.p-1+1=x.p by omega,show x.n-2+2=x.n by omega,
      show x.p-1+13=x.p+12 by omega,hnext,hcarry] using h
  | b =>
    have h := Raw14042Right.rightReturn42 (x.n-2) x.p (bTail x.s)
    have hnext := bTail_next x.s hs
    have hcarry := bTail_carry x.s hs
    simpa only [encode,hk,drainStep,show x.n-2+2=x.n by omega,hnext,hcarry] using h
  | c =>
    have h := Raw14042C.returnC x.p (x.n-2) (cTail x.s)
    have hnext := cTail_next x.s hs
    have hcarry := cTail_carry x.s hs
    simpa only [encode,hk,drainStep,Raw14042C.C,Raw14042CGeneral.cCfg,
      show x.n-2+2=x.n by omega,hnext,hcarry] using h

#print axioms drain_reach
end Raw14042SourceReach
