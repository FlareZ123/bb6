import PlaneSum
namespace BB6.Agent12LaneClock
open BB6.Agent12WordBlock BB6.Agent12BitEventWord BB6.Agent12BitPlanes BB6.Agent12PlaneOps BB6.Agent12LaneWord BB6.Agent12LaneCertificate BB6.Agent12LaneGenerator BB6.Agent12PlaneSum

/-- Identical polynomial to Agent12Clock.cost6, kept generic here so the
    parallel arithmetic proof does not import the raw-machine bridge. -/
def weight6 (A M X r o : Int) : Int :=
  -4*A^2 + 16*A*o - 22*A + 4*M^2 - 4*M*X - 8*M*o + 24*M*r - M +
  4*X^2 - 8*X*o - 12*X*r + 11*X - 96*o*r + 96*o + 36*r^2 - 51*r + 39

def edgeCalls (r : Nat) (s : State) : Int := gap s+r+parity s*(3-3*(r:Int))
def edgeWeight (r : Nat) (s : State) : Int := weight6 s.a s.m (step r s).a r (parity s)

/-- Latest event state (including the current event), age in bits since
    that event, and left coordinates aligned at each destination event. -/
structure Aligned where
  bs : List Nat
  ms : List Nat
  p : Nat
  age : List Nat
  a : List Nat
  x : List Nat
  deriving Repr

def origin (w : Aligned) (j : Nat) : BitState := ⟨(value w.bs j:Int),value w.ms j,(bit w.p j:Int)⟩
def nonEvents (N q : Nat) := (2^N-1)^^^q

def alignmentChecked (N q : Nat) (v : Trace) (w : Aligned) : Prop :=
  origin w N=lane v N ∧ value w.age N=0 ∧
  equalOn q w.bs v.bs ∧ equalOn q w.ms v.ms ∧ equalOn q [w.p] [v.p] ∧ equalOn q w.age [] ∧
  equalOn (nonEvents N q) w.bs (shiftP w.bs) ∧ equalOn (nonEvents N q) w.ms (shiftP w.ms) ∧
  equalOn (nonEvents N q) [w.p] [w.p>>>1] ∧
  equalOn (nonEvents N q) w.age (addP (shiftP w.age) [full N]) ∧
  equalOn q (addP (addP w.a [0,full N]) [w.p>>>1]) (shiftP w.bs) ∧
  equalOn q (addP (addP w.x [0,full N]) [v.p]) v.bs

instance (N q : Nat) (v : Trace) (w : Aligned) : Decidable (alignmentChecked N q v w) := by
  unfold alignmentChecked; infer_instance

structure OriginSpec (q N : Nat) (u orig : Nat→BitState) (age : Nat→Nat) : Prop where
  top : orig N=u N ∧ age N=0
  event : ∀ j<N, q.testBit j=true → orig j=u j ∧ age j=0
  idle : ∀ j<N, q.testBit j=false → orig j=orig (j+1) ∧ age j=age (j+1)+1

theorem origin_spec (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) :
    OriginSpec q N (lane v) (origin w) (value w.age) := by
  obtain ⟨ht,hage,hb,hm,hp,ha,hbn,hmn,hpn,han,_,_⟩:=h
  refine ⟨⟨ht,hage⟩,?_,?_⟩
  · intro j hj he
    have h1:=equalOn_sound _ _ _ hb j he
    have h2:=equalOn_sound _ _ _ hm j he
    have h3:=equalOn_sound _ _ _ hp j he
    have h4:=equalOn_sound _ _ _ ha j he
    simp only [value,Nat.mul_zero,Nat.add_zero] at h3 h4
    simp only [origin,lane,BitState.mk.injEq]
    exact ⟨⟨by omega,h2,by omega⟩,h4⟩
  · intro j hj he
    have hmask : (nonEvents N q).testBit j=true := by simp [nonEvents,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hj,he]
    have h1:=equalOn_sound _ _ _ hbn j hmask
    have h2:=equalOn_sound _ _ _ hmn j hmask
    have h3:=equalOn_sound _ _ _ hpn j hmask
    have h4:=equalOn_sound _ _ _ han j hmask
    simp only [value,Nat.mul_zero,Nat.add_zero,bit_shr] at h3
    simp only [addP_sound,value_shiftP,value,Nat.mul_zero,Nat.add_zero,bit_full N j (by omega)] at h4
    simp only [origin,BitState.mk.injEq,value_shiftP] at h1 h2 ⊢
    exact ⟨⟨by omega,h2,by omega⟩,h4⟩

def callsAt (u orig : Nat→BitState) (age : Nat→Nat) (j : Nat) : Int :=
  let a:=orig (j+1)
  let r:=(age (j+1)+1:Nat)
  (a.m:Int)-(a.b-2-a.o)+r+a.o*(3-3*(r:Int))

def weightAt (u orig : Nat→BitState) (age : Nat→Nat) (j : Nat) : Int :=
  let a:=orig (j+1)
  let b:=u j
  weight6 (a.b-2-a.o) a.m (b.b-2-b.o) (age (j+1)+1:Nat) a.o

def rPlanes (N : Nat) (w : Aligned) : List Nat := addP (shiftP w.age) [full N]

def callsTerms (N : Nat) (w : Aligned) : List (Int×List Nat) :=
  let m:=shiftP w.ms
  let r:=rPlanes N w
  let o:=[w.p>>>1]
  [(1,m),(-1,w.a),(1,r),(3,o),(-3,mulP o r)]

def weightTerms (N : Nat) (w : Aligned) : List (Int×List Nat) :=
  let a:=w.a
  let m:=shiftP w.ms
  let x:=w.x
  let r:=rPlanes N w
  let o:=[w.p>>>1]
  [(-4,mulP a a),(16,mulP a o),(-22,a),(4,mulP m m),(-4,mulP m x),(-8,mulP m o),
   (24,mulP m r),(-1,m),(4,mulP x x),(-8,mulP x o),(-12,mulP x r),(11,x),
   (-96,mulP o r),(96,o),(36,mulP r r),(-51,r),(39,[full N])]

theorem aligned_coords (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) (j : Nat) (hj:j<N) (he:q.testBit j=true) :
    (value w.a j:Int)=(origin w (j+1)).b-2-(origin w (j+1)).o ∧
    (value w.x j:Int)=(lane v j).b-2-(lane v j).o := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,ha,hx⟩:=h
  have h1:=equalOn_sound _ _ _ ha j he
  have h2:=equalOn_sound _ _ _ hx j he
  have hz:bit 0 j=0 := by simp [bit]
  simp only [addP_sound,value_shiftP,value,bit_shr,bit_full N j (by omega),hz,Nat.mul_zero,Nat.add_zero,Nat.zero_add] at h1 h2
  simp only [origin,lane]; exact ⟨by omega,by omega⟩

theorem calls_eval (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) (j : Nat) (hj:j<N) (he:q.testBit j=true) :
    evalTerms (callsTerms N w) j=callsAt (lane v) (origin w) (value w.age) j := by
  have hA:=(aligned_coords N q v w h j hj he).1
  simp only [callsTerms,evalTerms,mulP_sound,rPlanes,addP_sound,value_shiftP,value,bit_shr,bit_full N j (by omega),Nat.mul_zero,Nat.add_zero,Int.natCast_add,Int.natCast_mul,Int.natCast_one]
  simp only [callsAt,origin] at hA ⊢
  rw [hA]
  grind

theorem weight_eval (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) (j : Nat) (hj:j<N) (he:q.testBit j=true) :
    evalTerms (weightTerms N w) j=weightAt (lane v) (origin w) (value w.age) j := by
  obtain ⟨hA,hX⟩:=aligned_coords N q v w h j hj he
  simp only [weightTerms,evalTerms,mulP_sound,rPlanes,addP_sound,value_shiftP,value,bit_shr,bit_full N j (by omega),Nat.mul_zero,Nat.add_zero,Int.natCast_add,Int.natCast_mul,Int.natCast_one]
  simp only [weightAt,origin,lane] at hA hX ⊢
  rw [hA,hX]
  unfold weight6
  grind

theorem calls_sum (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) (hq:q<2^N) :
    sumTerms N q (callsTerms N w)=isum (fun j=>if q.testBit j then callsAt (lane v) (origin w) (value w.age) j else 0) N 0 := by
  rw [sumTerms_sound N q _ hq]
  apply isum_congr; intro j hj; simp only [Nat.zero_add] at *
  cases he:q.testBit j
  · simp [bit,he]
  · simp [bit,he,calls_eval N q v w h j hj he]

theorem weight_sum (N q : Nat) (v : Trace) (w : Aligned) (h:alignmentChecked N q v w) (hq:q<2^N) :
    sumTerms N q (weightTerms N w)=isum (fun j=>if q.testBit j then weightAt (lane v) (origin w) (value w.age) j else 0) N 0 := by
  rw [sumTerms_sound N q _ hq]
  apply isum_congr; intro j hj; simp only [Nat.zero_add] at *
  cases he:q.testBit j
  · simp [bit,he]
  · simp [bit,he,weight_eval N q v w h j hj he]

#print axioms origin_spec
#print axioms calls_sum
#print axioms weight_sum
end BB6.Agent12LaneClock
