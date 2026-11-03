import Mixed96Finite
import Mixed96Bridge
namespace A41

private theorem edgeOK_some (a k c:Nat) {t:Nat×Nat×Nat}
    (he : edgeOK a k c=true) (hn:nextC (a,k,c)=some t):
    s96T (qu t)=true := by
  simpa [edgeOK,hn] using he

private theorem checkC_edge (a k c c':Nat) (t:Nat×Nat×Nat)
    (hr:checkC a k c=true)
    (hc:if c<2 then c'=c else c'=c ∨ c'=c+48)
    (ht:nextC (a,k,c')=some t) : s96T (qu t)=true := by
  by_cases hlow:c<2
  · have heq : c'=c := by simpa [hlow] using hc
    subst c'
    have he : edgeOK a k c=true := by simpa [checkC,hlow] using hr
    exact edgeOK_some a k c he ht
  · have heq : c'=c ∨ c'=c+48 := by simpa [hlow] using hc
    have he : edgeOK a k c=true ∧ edgeOK a k (c+48)=true := by
      simpa [checkC,hlow,Bool.and_eq_true] using hr
    rcases heq with hh|hh
    · subst c'
      exact edgeOK_some a k c he.1 ht
    · subst c'
      exact edgeOK_some a k (c+48) he.2 ht

theorem checkState_closed (a k c:Nat)
    (h:checkState a k c=true) (hs:s96 a k c=true)
    (v:Nat×Nat×Nat) (edge:abstractEdge (a,k,c) v) : s96T v=true := by
  have hb : ((checkC a k c=true ∧ checkC (a+96) k c=true) ∧
      checkC a (k+96) c=true) ∧ checkC (a+96) (k+96) c=true := by
    simpa [checkState,hs,Bool.and_eq_true] using h
  obtain ⟨a',k',c',t,ha,hk,hc,hn,hq⟩ := edge
  rcases ha with ha|ha <;> rcases hk with hk|hk
  · subst a';subst k'
    have hv:=checkC_edge a k c c' t hb.1.1.1 hc hn
    simpa [hq] using hv
  · subst a';subst k'
    have hv:=checkC_edge a (k+96) c c' t hb.1.2 hc hn
    simpa [hq] using hv
  · subst a';subst k'
    have hv:=checkC_edge (a+96) k c c' t hb.1.1.2 hc hn
    simpa [hq] using hv
  · subst a';subst k'
    have hv:=checkC_edge (a+96) (k+96) c c' t hb.2 hc hn
    simpa [hq] using hv

#print axioms checkState_closed
end A41
