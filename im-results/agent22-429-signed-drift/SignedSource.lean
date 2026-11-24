import SignedLift
import BB429NewResidue
import BB429RootMod32

namespace Signed429

def ReachZ (a b : Int) : Prop :=
  ∃ x y : Nat, (x:Int)=a ∧ (y:Int)=b ∧ BB429NewResidue.Reach x y

/-- Adapter to the authentic blank-root inverse and modular laws. -/
theorem source_laws : ReachLaws ReachZ := by
  constructor
  · intro a b ha hb hbad hr
    obtain ⟨A,B,rfl,rfl,h⟩ := hr
    obtain ⟨n,hn⟩ := h
    rcases hbad with h0 | h1 | h2 | h3 | h4
    · have hall := BB429NewResidue.reach_allowed A B ⟨n,hn⟩
      unfold BB429Mod8.Allowed at hall
      apply h0
      unfold allowed
      omega
    · have hh := BB429RootEven8.rooted_positive_even_eight n A B hn (by omega) (by omega)
      omega
    · have hh := BB429RootMod16.rooted_not_7_7 n A B hn (by omega)
      omega
    · rcases h3.1 with h31 | h35
      · have hh := BB429RootMod16.rooted_not_1_6 n A B hn (by omega)
        omega
      · have hh := BB429RootMod16.rooted_not_5_6 n A B hn (by omega)
        omega
    · have hh := BB429RootMod32.rooted_not_5_1 n A B hn (by omega)
      omega
  · intro a b ha ho hr
    obtain ⟨A,B,rfl,rfl,h⟩ := hr
    rcases BB429NewResidue.odd_back A B (by omega) (by omega) h with
      ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy,hm⟩
    · exact Or.inl ⟨x,y,⟨x,y,rfl,rfl,hxy⟩,by omega,by omega⟩
    · exact Or.inr ⟨x,y,⟨x,y,rfl,rfl,hxy⟩,by omega,by omega,by omega⟩
  · intro a b ha he hr
    obtain ⟨A,B,rfl,rfl,h⟩ := hr
    obtain ⟨x,y,hxy,hx,hy,hm⟩ := BB429NewResidue.even_back A B (by omega) (by omega) h
    exact ⟨x,y,⟨x,y,rfl,rfl,hxy⟩,by omega,by omega,by omega⟩

/-- A sufficiently shallow closed signed tree excludes an authentic
positive branch-29 feeder, uniformly in its enormous high power. -/
theorem branch29_root_excluded (q c : Nat) (d e N : Nat)
    (hc : 4≤c) (he : 5≤e) (hprec : 2*d+e≤N)
    (hsize : 128*(c:Int)-97+11*(d:Int)≤(2:Int)^e)
    (hq : q+c=3*2^N)
    (hcl : Closed d (29-32*(c:Int)) (55-64*(c:Int))) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) := by
  have hn := branch29_lift ReachZ source_laws (c:Int) d e N (by omega) he hprec hsize hcl
  intro hr
  apply hn
  refine ⟨32*q+29,64*q+55,?_,?_,hr⟩
  · have hqz := congrArg (fun v : Nat => (v:Int)) hq
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hqz ⊢
    change (q:Int)+(c:Int)=3*(2:Int)^N at hqz
    change 32*(q:Int)+29=96*(2:Int)^N+29-32*(c:Int)
    omega
  · have hqz := congrArg (fun v : Nat => (v:Int)) hq
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hqz ⊢
    change (q:Int)+(c:Int)=3*(2:Int)^N at hqz
    change 64*(q:Int)+55=192*(2:Int)^N+55-64*(c:Int)
    omega

theorem branch29_cert_excluded (q c : Nat) (d e N : Nat)
    (hc : 4≤c) (he : 5≤e) (hprec : 2*d+e≤N)
    (hsize : 128*(c:Int)-97+11*(d:Int)≤(2:Int)^e)
    (hq : q+c=3*2^N)
    (hcert : signedCert d (29-32*(c:Int)) (55-64*(c:Int))=true) :
    ¬BB429NewResidue.Reach (32*q+29) (64*q+55) :=
  branch29_root_excluded q c d e N hc he hprec hsize hq (signedCert_sound _ _ _ hcert)

#print axioms source_laws
#print axioms branch29_root_excluded
#print axioms branch29_cert_excluded
end Signed429
