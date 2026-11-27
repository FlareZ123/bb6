import Agent5Frame150

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Q0149
open BB6Coverage Agent31Pump Frame150 BB6.Agent13BlankDelay

def block (v : Bool) (n : Nat) : List Bool := rep [v] n
def U (n : Nat) := block true n
def Z (n : Nat) := block false n

theorem blockAdd (v : Bool) (a b : Nat) : block v (a+b) = block v a ++ block v b :=
  (Auto.rep_add [v] a b).symm
theorem blockRep (v : Bool) (a n : Nat) : rep (block v a) n = block v (a*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ,Nat.add_comm (a*n) a,blockAdd]
    simp only [rep,ih]
theorem blockJoin (v : Bool) (a b : Nat) (X : List Bool) :
    block v a ++ (block v b ++ X) = block v (a+b) ++ X := by
  rw [blockAdd,List.append_assoc]
theorem blockJoinLast (v : Bool) (a b : Nat) :
    block v a ++ block v b = block v (a+b) := (blockAdd v a b).symm
theorem blockZero (v : Bool) : block v 0 = [] := rfl

theorem Uadd (a b : Nat) : U (a+b) = U a ++ U b := blockAdd true a b
theorem Zadd (a b : Nat) : Z (a+b) = Z a ++ Z b := blockAdd false a b

def T (x y : Nat) : Z0 := ⟨0,U y ++ [false,false] ++ U x,[false]⟩
def S (x b : Nat) (W : List Bool) : Z0 := ⟨2,[false,false] ++ U x,[true,false] ++ U b ++ W⟩
def S4 (x b c d : Nat) := S x b (Z c ++ U d)

theorem weq_of_eq {a b : List Bool} (h : a=b) : WEq a b := by
  subst b
  exact WEq.refl _

def R0 (p : PartialMachine) (s t : Z0) : Prop :=
  ∃ k u, run0 p k s = some u ∧ ZEq u t
theorem R0.refl (p : PartialMachine) (s : Z0) : R0 p s s :=
  ⟨0,s,rfl,ZEq.refl _⟩
theorem r0of {p s t} (a : RE p s t) : R0 p s t := by
  obtain ⟨k,u,_,h,e⟩ := a
  exact ⟨k,u,h,e⟩
theorem r0trans {p s t u} (a : R0 p s t) (b : R0 p t u) : R0 p s u := by
  obtain ⟨k,v,h,hv⟩ := a
  obtain ⟨n,w,g,hw⟩ := b
  obtain ⟨w',g',he⟩ := runEq p n hv.symm g
  exact ⟨k+n,w',join0 h g',he.symm.trans hw⟩
theorem then0 {p s t u} (a : RE p s t) (b : R0 p t u) : RE p s u := by
  obtain ⟨k,v,hk,h,hv⟩ := a
  obtain ⟨n,w,g,hw⟩ := b
  obtain ⟨w',g',he⟩ := runEq p n hv.symm g
  exact ⟨k+n,w',by omega,join0 h g',he.symm.trans hw⟩
theorem thenP {p s t u} (a : RE p s t) (b : RE p t u) : RE p s u :=
  then0 a (r0of b)

structure Rules (p : PartialMachine) where
  init : ∀ x n, RE p (T x (n+1)) (S x n [])
  odd : ∀ x b W, b%2=1 → RE p (S x b (false::W)) (S 0 (x+2) (Z b ++ true::W))
  reduce : ∀ x b W, b%2=0 → 0<b → RE p (S x b ([false,false,false,false]++W)) (S (x+2) (b+2) W)
  finish : ∀ x b, b%2=0 → 0<b → RE p (S x b [false,true]) (T (x+2) (b+2))
  turn1 : ∀ x b, b%2=0 → 0<b → RE p (S x b [false,false,false,true]) (S (x+2) (b+3) [false,true,true])
  turn3 : ∀ x b, b%2=0 → 0<b → RE p (S x b [false,false,false,true,true,true]) (S (x+2) (b+3) [false,true,true,true,true])
  five : ∀ x b, b%2=0 → 0<b → RE p (S x b [false,true,true,true,true,true]) (S (x+2) b [false,false,false,false,true])

theorem odd4 {p} (r : Rules p) (x b d : Nat) (hb : b%2=1) :
    RE p (S4 x b 1 d) (S4 0 (x+2) b (d+1)) := by
  simpa [S4,Z,U,block,rep] using r.odd x b (U d) hb

theorem oddBlank {p} (r : Rules p) (x b : Nat) (hb : b%2=1) :
    RE p (S x b []) (S4 0 (x+2) b 1) := by
  have e : ZEq (S x b []) (S x b [false]) :=
    ⟨rfl,WEq.refl _,by simpa [S,List.append_assoc,rep] using
        (WEq.pad ([true,false]++U b) 1).symm⟩
  simpa [S4,U,block,rep] using (r.odd x b [] hb).transport e

theorem reduceN {p} (r : Rules p) (x b n c d : Nat) (hb : b%2=0) (hp : 0<b) :
    R0 p (S4 x b (4*n+c) d) (S4 (x+2*n) (b+2*n) c d) := by
  induction n generalizing x b with
  | zero => simpa using R0.refl p (S4 x b c d)
  | succ n ih =>
    have hz : Z (4*(n+1)+c) = [false,false,false,false] ++ Z (4*n+c) := by
      rw [show 4*(n+1)+c=4+(4*n+c) by omega,Zadd]
      rfl
    have a : RE p (S4 x b (4*(n+1)+c) d) (S4 (x+2) (b+2) (4*n+c) d) := by
      simpa [S4,hz,List.append_assoc] using r.reduce x b (Z (4*n+c)++U d) hb hp
    have bb := ih (x+2) (b+2) (by omega) (by omega)
    rw [show x+2+2*n=x+2*(n+1) by omega,show b+2+2*n=b+2*(n+1) by omega] at bb
    exact r0trans (r0of a) bb

theorem mergeOne (x b : Nat) : S4 x b 0 1 = S x (b+1) [] := by
  unfold S4 S
  rw [Uadd]
  simp [Z,U,block,rep,List.append_assoc]

theorem exceptional {p} (r : Rules p) (k : Nat) :
    RE p (S4 (2*k) (4*k+4) 3 1) (T (2*k+8) (4*k+18)) := by
  have a : RE p (S4 (2*k) (4*k+4) 3 1) (S4 (2*k+2) (4*k+7) 1 2) := by
    simpa [S4,Z,U,block,rep,show 4*k+4+3=4*k+7 by omega] using
      r.turn1 (2*k) (4*k+4) (by omega) (by omega)
  have b := odd4 r (2*k+2) (4*k+7) 2 (by omega)
  rw [show 2*k+2+2=2*k+4 by omega] at b
  have c := reduceN r 0 (2*k+4) (k+1) 3 3 (by omega) (by omega)
  rw [show 4*(k+1)+3=4*k+7 by omega,show 0+2*(k+1)=2*k+2 by omega,
    show 2*k+4+2*(k+1)=4*k+6 by omega] at c
  have d : RE p (S4 (2*k+2) (4*k+6) 3 3) (S4 (2*k+4) (4*k+9) 1 4) := by
    simpa [S4,Z,U,block,rep,show 2*k+2+2=2*k+4 by omega,show 4*k+6+3=4*k+9 by omega] using
      r.turn3 (2*k+2) (4*k+6) (by omega) (by omega)
  have e := odd4 r (2*k+4) (4*k+9) 4 (by omega)
  rw [show 2*k+4+2=2*k+6 by omega] at e
  have f := reduceN r 0 (2*k+6) (k+2) 1 5 (by omega) (by omega)
  rw [show 4*(k+2)+1=4*k+9 by omega,show 0+2*(k+2)=2*k+4 by omega,
    show 2*k+6+2*(k+2)=4*k+10 by omega] at f
  have g : RE p (S4 (2*k+4) (4*k+10) 1 5) (S4 (2*k+6) (4*k+10) 4 1) := by
    simpa [S4,Z,U,block,rep,show 2*k+4+2=2*k+6 by omega] using
      r.five (2*k+4) (4*k+10) (by omega) (by omega)
  have j := reduceN r (2*k+6) (4*k+10) 1 0 1 (by omega) (by omega)
  rw [show 4*1+0=4 by omega,show 2*k+6+2*1=2*k+8 by omega,
    show 4*k+10+2*1=4*k+12 by omega,mergeOne] at j
  have l := oddBlank r (2*k+8) (4*k+13) (by omega)
  rw [show 2*k+8+2=2*k+10 by omega] at l
  have m := reduceN r 0 (2*k+10) (k+3) 1 1 (by omega) (by omega)
  rw [show 4*(k+3)+1=4*k+13 by omega,show 0+2*(k+3)=2*k+6 by omega,
    show 2*k+10+2*(k+3)=4*k+16 by omega] at m
  have n : RE p (S4 (2*k+6) (4*k+16) 1 1) (T (2*k+8) (4*k+18)) := by
    simpa [S4,Z,U,block,rep,show 2*k+6+2=2*k+8 by omega,show 4*k+16+2=4*k+18 by omega] using
      r.finish (2*k+6) (4*k+16) (by omega) (by omega)
  exact thenP (then0 (thenP (then0 (thenP (then0 (thenP (thenP (then0 (thenP (a) b) c) d) e) f) g) j) l) m) n

def P (k : Nat) := T (8*k) (16*k+2)
def Q (k : Nat) := T (8*k+2) (16*k+4)

theorem pToQ {p} (r : Rules p) (k : Nat) : RE p (P k) (Q k) := by
  have a : RE p (P k) (S (8*k) (16*k+1) []) := by
    simpa [P,show 16*k+1+1=16*k+2 by omega] using r.init (8*k) (16*k+1)
  have b := oddBlank r (8*k) (16*k+1) (by omega)
  have c := reduceN r 0 (8*k+2) (4*k) 1 1 (by omega) (by omega)
  rw [show 4*(4*k)+1=16*k+1 by omega,show 0+2*(4*k)=8*k by omega,
    show 8*k+2+2*(4*k)=16*k+2 by omega] at c
  have d : RE p (S4 (8*k) (16*k+2) 1 1) (Q k) := by
    simpa [S4,Q,Z,U,block,rep,show 16*k+2+2=16*k+4 by omega] using
      r.finish (8*k) (16*k+2) (by omega) (by omega)
  exact thenP (then0 (thenP a b) c) d

theorem qToP {p} (r : Rules p) (k : Nat) : RE p (Q k) (P (k+1)) := by
  have a : RE p (Q k) (S (8*k+2) (16*k+3) []) := by
    simpa [Q,show 16*k+3+1=16*k+4 by omega] using r.init (8*k+2) (16*k+3)
  have b := oddBlank r (8*k+2) (16*k+3) (by omega)
  rw [show 8*k+2+2=8*k+4 by omega] at b
  have c := reduceN r 0 (8*k+4) (4*k) 3 1 (by omega) (by omega)
  rw [show 4*(4*k)+3=16*k+3 by omega,show 0+2*(4*k)=8*k by omega,
    show 8*k+4+2*(4*k)=16*k+4 by omega] at c
  have d := exceptional r (4*k)
  rw [show 2*(4*k)=8*k by omega,show 4*(4*k)+4=16*k+4 by omega,
    show 4*(4*k)+18=16*(k+1)+2 by omega,show 8*k+8=8*(k+1) by omega] at d
  exact thenP (then0 (thenP a b) c) (by simpa [P] using d)

def region (s : Z0) := (∃ k, ZEq s (P k)) ∨ (∃ k, ZEq s (Q k))

theorem closed {p} (r : Rules p) (s : Z0) (hs : region s) :
    ∃ k t, 0<k ∧ region t ∧ run0 p k s = some t := by
  rcases hs with ⟨k,e⟩ | ⟨k,e⟩
  · obtain ⟨n,t,hn,hr,he⟩ := (pToQ r k).transport e
    exact ⟨n,t,hn,Or.inr ⟨k,he⟩,hr⟩
  · obtain ⟨n,t,hn,hr,he⟩ := (qToP r k).transport e
    exact ⟨n,t,hn,Or.inl ⟨k+1,he⟩,hr⟩

theorem never {p} (r : Rules p) (entry : Nat) (z : Z0)
    (seed : run0 p entry ⟨0,[],[]⟩ = some z) (eq : ZEq z (Q 0))
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Multi.never_of_region p region entry z seed (Or.inr ⟨0,eq⟩) (closed r) m hm

#print axioms never
end BB6Coverage.Agent31Pump.Q0149
