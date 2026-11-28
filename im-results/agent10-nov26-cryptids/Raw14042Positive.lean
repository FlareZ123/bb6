import Raw14042TerminalReach
import Raw14042Growth

namespace Raw14042Positive
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer
open Raw14042ArithmeticInvariant Raw14042SourceReach Raw14042TerminalReach
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem cons3 (a b c : Bool) (r : Ray) (n : Nat) :
    cons a (cons b (cons c r)) (n+3) = r n := by
  cases n <;> rfl

theorem leftRay_rep_skip (a : Sym) (p j : Nat) (X : List Sym) :
    leftRay (List.replicate p a ++ X) (3*p+j) = leftRay X j := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.replicate_succ, List.cons_append]
    rw [show 3*(p+1)+j=(3*p+j)+3 by omega]
    simp only [leftRay,cons3]
    exact ih

theorem leftRay_rep_inside (a : Sym) (p i : Nat) (X : List Sym) (hi : i<p) :
    leftRay (List.replicate p a ++ X) (3*i+2) = a.a := by
  induction p generalizing i with
  | zero => omega
  | succ p ih =>
    rw [List.replicate_succ,List.cons_append]
    cases i with
    | zero => rfl
    | succ i =>
      rw [show 3*(i+1)+2=(3*i+2)+3 by omega]
      simp only [leftRay,cons3]
      exact ih i (by omega)

theorem encode_left_end (b : Bank) (p n s : Nat) :
    (encode ⟨b,p,n,s⟩).l (3*p+2) = false := by
  cases b with
  | a =>
    change leftRay (U 3 p ++ [S 2]) (3*p+2) = false
    simpa [U,S,Sym.ofCode,leftRay,blankRay,cons] using
      leftRay_rep_skip (S 3) p 2 [S 2]
  | b =>
    change leftRay (U 5 p) (3*p+2) = false
    have h := leftRay_rep_skip (S 5) p 2 []
    simpa [U,S,Sym.ofCode,leftRay,blankRay,cons] using h
  | c =>
    change leftRay (U 3 p ++ [S 2]) (3*p+2) = false
    simpa [U,S,Sym.ofCode,leftRay,blankRay,cons] using
      leftRay_rep_skip (S 3) p 2 [S 2]

theorem encode_left_inside (b : Bank) (p n s i : Nat) (hi : i<p) :
    (encode ⟨b,p,n,s⟩).l (3*i+2) = true := by
  cases b with
  | a =>
    change leftRay (U 3 p ++ [S 2]) (3*i+2) = true
    simpa [U,S,Sym.ofCode] using
      leftRay_rep_inside (S 3) p i [S 2] hi
  | b =>
    change leftRay (U 5 p) (3*i+2) = true
    simpa [U,S,Sym.ofCode] using
      leftRay_rep_inside (S 5) p i [] hi
  | c =>
    change leftRay (U 3 p ++ [S 2]) (3*i+2) = true
    simpa [U,S,Sym.ofCode] using
      leftRay_rep_inside (S 3) p i [S 2] hi

theorem encode_ne_of_p_lt (x y : Section) (h : x.p<y.p) :
    encode x ≠ encode y := by
  intro heq
  have hb := congrArg (fun z : Prim => z.l (3*x.p+2)) heq
  have h0 := encode_left_end x.kind x.p x.n x.s
  have h1 := encode_left_inside y.kind y.p y.n y.s x.p h
  change (encode ⟨x.kind,x.p,x.n,x.s⟩).l (3*x.p+2) =
    (encode ⟨y.kind,y.p,y.n,y.s⟩).l (3*x.p+2) at hb
  rw [h0,h1] at hb

theorem step_plus (x : Section) (hx : good x) :
    Raw14042Growth.Plus M42 (encode x) (encode (step x)) := by
  obtain ⟨t,ht⟩ := step_reach x hx
  refine ⟨t,?_,ht⟩
  have hpg := Raw14042Growth.step_growth x hx
  have hne : encode x ≠ encode (step x) :=
    encode_ne_of_p_lt x (step x) (by omega)
  by_contra hpos
  have hz : t=0 := by omega
  subst t
  have heq : encode x = encode (step x) := by
    simpa [run] using ht
  exact hne heq

theorem root_encode :
    encode Raw14042Growth.root = Raw14042Entry.rootS5.prim := by
  rfl

theorem forever (n : Nat) : ∃ c, run M42 n primBlank = some c :=
  Raw14042Growth.root_unbounded encode root_encode step_plus n

#print axioms encode_ne_of_p_lt
#print axioms step_plus
#print axioms forever
end Raw14042Positive
