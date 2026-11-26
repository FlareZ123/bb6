import TraceComplementCover
import LagCert

namespace BB6.Agent43P1Complement
open BB6.Agent45.DelayedCarry

/-- The distance from the nearest endpoint of the low product interval is
    unchanged by reflection. The prefix need not be an authentic trace. -/
theorem resMin_reflect (j t B : Nat) (hj : j≤t) (hB : B≤2^t) :
    resMin j (2^t-B)=resMin j B := by
  let D := 2^j
  let x := (7*B)%D
  let y := (7*(2^t-B))%D
  have hD : 0<D := Nat.two_pow_pos _
  have hx : x<D := Nat.mod_lt _ hD
  have hy : y<D := Nat.mod_lt _ hD
  have he : 7*B+7*(2^t-B)=7*2^t := by omega
  have hdiv : D ∣ 7*2^t := by
    obtain ⟨a,ha⟩ := Nat.pow_dvd_pow 2 hj
    exact ⟨7*a,by rw [ha]; dsimp [D]; ac_rfl⟩
  have hz : (x+y)%D=0 := by
    dsimp [x,y]; rw [←Nat.add_mod,he]
    exact Nat.mod_eq_zero_of_dvd hdiv
  by_cases hlt : x+y<D
  · rw [Nat.mod_eq_of_lt hlt] at hz
    have hx0 : x=0 := by omega
    have hy0 : y=0 := by omega
    change min y (D-y)=min x (D-x)
    rw [hx0,hy0]
  · rw [Nat.mod_eq_sub_mod (show D≤x+y by omega),Nat.mod_eq_of_lt (show x+y-D<D by omega)] at hz
    have hyx : y=D-x := by omega
    have hxy : D-y=x := by omega
    change min y (D-y)=min x (D-x)
    rw [hyx,show D-(D-x)=x by omega,Nat.min_comm]

/-- A multiple of a higher power of two cannot change a lower margin. -/
theorem resMin_high (j t B R : Nat) (hj : j≤t) :
    resMin j (B+2^t*R)=resMin j B := by
  have hd : (2:Nat)^j ∣ 2^t := Nat.pow_dvd_pow 2 hj
  have hm : (7*(B+2^t*R))%2^j=(7*B)%2^j := by
    rw [Nat.mul_add,Nat.add_mod]
    have hdiv : (2:Nat)^j ∣ 7*(2^t*R) := by
      obtain ⟨a,ha⟩ := hd
      exact ⟨7*a*R,by rw [ha]; ac_rfl⟩
    rw [Nat.mod_eq_zero_of_dvd hdiv,Nat.add_zero,Nat.mod_mod]
  simp only [resMin,hm]

/-- The reverse-midpoint algorithm need only enumerate every length-h prefix
    that can extend through the fixed window of length n. It deliberately
    retains candidates that may fail the next n-step lookahead. -/
def MidpointCover (n s h : Nat) (ps qs : List Prefix) : Prop :=
  ∀ B a C c, (B,a)∈ps → C%4=1 → Extend n s B a h C c →
    (∃ D d, Extend n (s+h) C c (n-h) D d) → (C,c)∈qs

/-- The packed implementation checks every low-prefix margin within the
    candidate block, including prefixes that will later be discarded. -/
def AllBlockMargins (n K s h : Nat) (qs : List Prefix) : Prop :=
  ∀ C c, (C,c)∈qs → ∀ j, s<j → j≤s+h →
    (n+K+2)*marginSize n K*2^j<6*2^n*resMin j C

/-- The canonical half has the same inherited margins as the ordinary cover. -/
structure HalfCert (n K s : Nat) (ps : List Prefix) : Prop where
  cover : HalfCovered n s ps
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

private theorem prefix_mod4 (n s B a h C c : Nat) (hs : 1≤s)
    (ht : Trace n s B a) (he : Extend n s B a h C c) (hm : C%4=1) : B%4=1 := by
  obtain ⟨_,hb,ho,_⟩ := trace_bounds n s B a ht
  by_cases h1 : s=1
  · subst s; simp at hb; omega
  · have hs2 : 2≤s := by omega
    have hd : 4 ∣ (2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 hs2
    obtain ⟨R,hR⟩ := extend_mod n s B a h C c he
    rw [hR,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd] at hm
    simpa using hm

private theorem canonical_prefix (n t B a : Nat) (ht : Trace n t B a) (h : B%4=1)
    (s : Nat) (hs : 1≤s) (hst : s≤t) :
    ∃ C c, Trace n s C c ∧ C%4=1 ∧ Extend n s C c (t-s) B a := by
  obtain ⟨C,c,hpre,he⟩ := trace_split n t B a s ht hs hst
  exact ⟨C,c,hpre,prefix_mod4 n s C c (t-s) B a hs hpre he h,he⟩

/-- A complete midpoint list supplies both the next lookahead cover and all
    intermediate margins. This is the source-level interface needed for
    the long-window packed algorithm, rather than the much stronger old
    requirement that one prefix margin cover an entire block by itself. -/
theorem half_midpoint_next (n K s h : Nat) (ps qs : List Prefix)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s) (hh : 1≤h) (hhn : h≤n)
    (hc : HalfCert n K s ps) (hm : MidpointCover n s h ps qs)
    (hg : AllBlockMargins n K s h qs) : HalfCert n K (s+h) qs := by
  constructor
  · intro C c B a ht hp he
    obtain ⟨D,d,hpre,hmod,hExt⟩ := canonical_prefix n (s+h) C c ht hp s hs (by omega)
    have hExt' : Extend n s D d h C c := by simpa using hExt
    have hfull := extend_append n s D d h C c n B a hExt' he
    obtain ⟨F,f,hshort⟩ := extend_prefix n s D d (h+n) B a n hfull (by omega)
    obtain ⟨G,g,htail⟩ := extend_prefix n (s+h) C c n B a (n-h) he (by omega)
    exact hm D d C c (hc.cover D d F f hpre hmod hshort) hp hExt' ⟨G,g,htail⟩
  · intro j hj hjt
    by_cases hjs : j≤s
    · exact hc.margins j hj hjs
    intro B a htr
    suffices hf : ∀ X x, Trace n (n+j) X x → X%4=1 →
        (n+K+2)*marginSize n K*2^j<6*2^n*resMin j X by
      by_cases hp : B%4=1
      · exact hf B a htr hp
      · obtain ⟨_,hb,ho,_⟩ := trace_bounds n (n+j) B a htr
        have hd : (2:Nat)^(n+j)%4=0 := by
          apply Nat.mod_eq_zero_of_dvd
          simpa using Nat.pow_dvd_pow 2 (show 2≤n+j by omega)
        have he : 2^(n+j)-B+B=2^(n+j) := by omega
        have hr := congrArg (fun x : Nat => x%4) he
        rw [Nat.add_mod,hd] at hr
        have h3 : (2^(n+j)-B)%4=1 := by omega
        have hl := hf _ _ (trace_complement n (n+j) B a hn heven htr) h3
        rw [resMin_reflect j (n+j) B (by omega) (by omega)] at hl
        exact hl
    intro X x ht hp
    obtain ⟨C,c,hpre,hmod,hExt⟩ := canonical_prefix n (n+j) X x ht hp (s+h) (by omega) (by omega)
    obtain ⟨D,d,hstart,hDmod,hmid⟩ := canonical_prefix n (s+h) C c hpre hmod s hs (by omega)
    have hmid' : Extend n s D d h C c := by simpa using hmid
    obtain ⟨G,g,htail⟩ := extend_prefix n (s+h) C c (n+j-(s+h)) X x (n-h) hExt (by omega)
    have hfull := extend_append n s D d h C c (n-h) G g hmid' htail
    have hshort : Extend n s D d n G g := by simpa [show h+(n-h)=n by omega] using hfull
    have hC := hm D d C c (hc.cover D d G g hstart hDmod hshort) hmod hmid' ⟨G,g,htail⟩
    have hineq := hg C c hC j (by omega) hjt
    obtain ⟨R,hR⟩ := extend_mod n (s+h) C c (n+j-(s+h)) X x hExt
    rw [hR,resMin_high j (s+h) C R hjt]
    exact hineq

/-- The initial singleton is both halves and carries the seed margin. -/
theorem half_cert_first (n K : Nat) (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) :
    HalfCert n K 1 [(1,(n+2)/2)] := by
  have hc := cert_first n K hgood
  exact ⟨fun B a C c ht _ he => hc.cover B a C c ht he,hc.margins⟩

theorem half_cert_empty (n K s : Nat) (hn : 1≤n) (he : n%2=0) (hs : 2≤s)
    (hc : HalfCert n K s []) : Cert n K s [] := by
  refine ⟨?_,hc.margins⟩
  simpa using complete_half n s [] hn he hs hc.cover

#print axioms resMin_reflect
#print axioms resMin_high
#print axioms half_midpoint_next
#print axioms half_cert_first
#print axioms half_cert_empty
end BB6.Agent43P1Complement
