import SignedPairMacroBridge
import FiniteTripleMacro

namespace SignedPairMacroBridge

inductive SourceWalk : List PeriodicMacro.Letter → Nat → Nat → Nat → Nat → Prop where
  | nil (u D : Nat) : SourceWalk [] u D u D
  | cons {x : PeriodicMacro.Letter} {xs : List PeriodicMacro.Letter}
      {u D v d' U D' : Nat}
      (hp : PairRun x.isE x.j u D v d')
      (rest : SourceWalk xs v d' U D') : SourceWalk (x::xs) u D U D'

theorem sourceWalk_model {xs : List PeriodicMacro.Letter}
    {u D U D' : Nat} (hw : SourceWalk xs u D U D')
    (r : Nat) (hr : 6*u+D=2*r) :
    ∃ s : Nat, 6*U+D'=2*s ∧ PeriodicMacro.Walk xs u r U s := by
  induction hw generalizing r with
  | nil u D =>
    exact ⟨r,hr,PeriodicMacro.Walk.nil u r⟩
  | @cons x xs u D v d' U D' hp rest ih =>
    obtain ⟨mid, hmid, hstep⟩ := pairRun_model_exists hp hr
    obtain ⟨s,hs,hword⟩ := ih mid hmid
    exact ⟨s,hs,PeriodicMacro.Walk.cons hstep hword⟩

/-- Three source-exact signed word copies have exactly affine first
    coordinates if scale exceeds twice the safe half-rank height. -/
theorem source_triple_word_slope (xs : List PeriodicMacro.Letter)
    (u0 D0 u1 D1 u2 D2 u3 D3 r0 : Nat)
    (h0 : SourceWalk xs u0 D0 u1 D1)
    (h1 : SourceWalk xs u1 D1 u2 D2)
    (h2 : SourceWalk xs u2 D2 u3 D3)
    (hr0 : 6*u0+D0=2*r0)
    (hbig : 2*((r0+2*PeriodicMacro.T xs)/3)<PeriodicMacro.M xs) :
    (u0:Int)+(u2:Int)=2*(u1:Int) ∧
      ((PeriodicMacro.M xs:Int)-1)*((u1:Int)-(u0:Int))=
      ((PeriodicMacro.A xs*PeriodicMacro.T xs):Int) := by
  obtain ⟨r1,hr1,w0⟩ := sourceWalk_model h0 r0 hr0
  obtain ⟨r2,hr2,w1⟩ := sourceWalk_model h1 r1 hr1
  obtain ⟨r3,hr3,w2⟩ := sourceWalk_model h2 r2 hr2
  have hsafe0 : 3*u0≤r0 := by omega
  have hsafe1 : 3*u1≤r1 := by omega
  have hsafe2 : 3*u2≤r2 := by omega
  exact PeriodicMacro.triple_word_slope xs u0 u1 u2 u3
    r0 r1 r2 r3 w0 w1 w2 hsafe0 hsafe1 hsafe2 hbig

#print axioms sourceWalk_model
#print axioms source_triple_word_slope
end SignedPairMacroBridge
