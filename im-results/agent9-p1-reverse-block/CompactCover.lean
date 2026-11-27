import CompactState
import HalfBlockMargin

namespace BB6.Agent9CompactCover
open BB6.Agent45.DelayedCarry
open BB6.Agent9CompactState
open BB6.Agent43P1Complement

abbrev QPrefix := Nat × Nat

def QHalfCovered (n s : Nat) (ps : List QPrefix) : Prop :=
  ∀ B a C c, Trace n s B a → B%4=1 → Extend n s B a n C c →
    (quotient n s B,a) ∈ ps

structure QHalfCert (n K s : Nat) (ps : List QPrefix) : Prop where
  cover : QHalfCovered n s ps
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

def QMidpointCover (n s h : Nat) (ps qs : List QPrefix) : Prop :=
  ∀ Q a R c, (Q,a) ∈ ps → QExtend n s Q a h R c →
    (∃ S d, QExtend n (s+h) R c (n-h) S d) → (R,c) ∈ qs

def QueueMargin (n K s h Q : Nat) : Prop :=
  (n+K+2)*marginSize n K*2^(s+h)<6*2^n ∨
  ∃ L, L≤n ∧ L≤s ∧ 0<top n L Q ∧ top n L Q+1<2^L ∧
    (n+K+2)*marginSize n K*2^(h+L)<6*2^n

private theorem prefix_mod4 (n s B a h C c : Nat) (hs : 1≤s)
    (ht : Trace n s B a) (he : Extend n s B a h C c) (hm : C%4=1) : B%4=1 := by
  obtain ⟨_,hb,ho,_⟩ := trace_bounds n s B a ht
  by_cases h1 : s=1
  · subst s; simp at hb; omega
  · have hd : 4 ∣ (2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 (show 2≤s by omega)
    obtain ⟨R,hR⟩ := extend_mod n s B a h C c he
    rw [hR,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd] at hm
    simpa using hm

private theorem canonical_prefix (n t B a : Nat) (ht : Trace n t B a) (hm : B%4=1)
    (s : Nat) (hs : 1≤s) (hst : s≤t) :
    ∃ D d, Trace n s D d ∧ D%4=1 ∧ Extend n s D d (t-s) B a := by
  obtain ⟨D,d,hd,he⟩ := trace_split n t B a s ht hs hst
  exact ⟨D,d,hd,prefix_mod4 n s D d (t-s) B a hs hd he hm,he⟩

theorem qcert_of_half (n K s : Nat) (ps : List Prefix) (hc : HalfCert n K s ps) :
    QHalfCert n K s (ps.map fun p => (quotient n s p.1,p.2)) := by
  refine ⟨?_,hc.margins⟩
  intro B a C c ht hm he
  exact List.mem_map.mpr ⟨(B,a),hc.cover B a C c ht hm he,rfl⟩

theorem qcover_next (n s h : Nat) (ps qs : List QPrefix) (hs : 1≤s)
    (hhn : h≤n) (hc : QHalfCovered n s ps) (hm : QMidpointCover n s h ps qs) :
    QHalfCovered n (s+h) qs := by
  intro B a C c ht hmod he
  obtain ⟨D,d,hd,hdmod,hpre⟩ := canonical_prefix n (s+h) B a ht hmod s hs (by omega)
  have hpre' : Extend n s D d h B a := by simpa using hpre
  have hfull := extend_append n s D d h B a n C c hpre' he
  obtain ⟨G,g,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  obtain ⟨F,f,htail⟩ := extend_prefix n (s+h) B a n C c (n-h) he (by omega)
  exact hm _ _ _ _ (hc D d G g hd hdmod hshort)
    (project n s D d h B a hpre') ⟨_,_,project n (s+h) B a (n-h) F f htail⟩

theorem queue_margin_sound (n K s h B : Nat) (hs : 1≤s) (ho : B%2=1)
    (hm : QueueMargin n K s h (quotient n s B)) :
    (n+K+2)*marginSize n K*2^(s+h)<6*2^n*resMin s B := by
  rcases hm with hsmall | ⟨L,hLn,hLs,hlo,hhi,hgap⟩
  · have hd : 2 ∣ (2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 hs
    have hmod : ((7*B)%2^s)%2=1 := by
      rw [Nat.mod_mod_of_dvd _ hd,Nat.mul_mod,ho]
    have hpos : 0<(7*B)%2^s := by omega
    have hlt := Nat.mod_lt (7*B) (Nat.two_pow_pos s)
    have hr : 1≤resMin s B := by unfold resMin; exact Nat.le_min.mpr ⟨by omega,by omega⟩
    exact Nat.lt_of_lt_of_le hsmall (by simpa using Nat.mul_le_mul_left (6*2^n) hr)
  · have hr := top_resMin n L s B hLn hLs hlo hhi
    have hp : (2:Nat)^(s+h)=2^(h+L)*2^(s-L) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp,← Nat.mul_assoc]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hgap (Nat.two_pow_pos _))
      (Nat.mul_le_mul_left (6*2^n) hr)

theorem qmargin_next (n K s h : Nat) (ps : List QPrefix)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s)
    (hc : QHalfCert n K s ps) (hg : ∀ p ∈ ps, QueueMargin n K s h p.1) :
    ∀ j, 1≤j → j≤s+h → LateMargin n K j := by
  intro j hj hjt
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
  obtain ⟨D,d,hd,hdmod,he⟩ := canonical_prefix n (n+j) X x ht hp s hs (by omega)
  obtain ⟨F,f,hshort⟩ := extend_prefix n s D d (n+j-s) X x n he (by omega)
  have hmem := hc.cover D d F f hd hdmod hshort
  have hmargin := queue_margin_sound n K s h D hs (trace_bounds n s D d hd).2.2.1 (hg _ hmem)
  obtain ⟨R,hR⟩ := extend_mod n s D d (n+j-s) X x he
  have hr := resMin_extend s j D R (by omega)
  rw [← hR] at hr
  have hL := Nat.mul_le_mul_left ((n+K+2)*marginSize n K)
    (Nat.pow_le_pow_right (show 0<2 by decide) hjt)
  exact Nat.lt_of_le_of_lt hL (Nat.lt_of_lt_of_le hmargin
    (Nat.mul_le_mul_left (6*2^n) hr))

theorem qcert_next (n K s h : Nat) (ps qs : List QPrefix)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s) (hhn : h≤n)
    (hc : QHalfCert n K s ps) (hm : QMidpointCover n s h ps qs)
    (hg : ∀ p ∈ ps, QueueMargin n K s h p.1) :
    QHalfCert n K (s+h) qs :=
  ⟨qcover_next n s h ps qs hs hhn hc.cover hm,qmargin_next n K s h ps hn heven hs hc hg⟩

/-- The actual canonical filter is needed at s=1.  The abstract queue
    intentionally forgets that first selected bit after it leaves the window. -/
def QTraceMidpointCover (n s h : Nat) (ps qs : List QPrefix) : Prop :=
  ∀ B a C c, (quotient n s B,a)∈ps → Trace n s B a → C%4=1 →
    Extend n s B a h C c →
    (∃ D d, Extend n (s+h) C c (n-h) D d) → (quotient n (s+h) C,c)∈qs

theorem qcover_next_trace (n s h : Nat) (ps qs : List QPrefix)
    (hs : 1≤s) (hhn : h≤n) (hc : QHalfCovered n s ps)
    (hm : QTraceMidpointCover n s h ps qs) :
    QHalfCovered n (s+h) qs := by
  intro B a C c ht hmod he
  obtain ⟨D,d,hd,hdmod,hpre⟩ := canonical_prefix n (s+h) B a ht hmod s hs (by omega)
  have hpre' : Extend n s D d h B a := by simpa using hpre
  have hfull := extend_append n s D d h B a n C c hpre' he
  obtain ⟨G,g,hshort⟩ := extend_prefix n s D d (h+n) C c n hfull (by omega)
  obtain ⟨F,f,htail⟩ := extend_prefix n (s+h) B a n C c (n-h) he (by omega)
  exact hm D d B a (hc D d G g hd hdmod hshort) hd hmod hpre' ⟨F,f,htail⟩

theorem qcert_next_trace (n K s h : Nat) (ps qs : List QPrefix)
    (hn : 1≤n) (heven : n%2=0) (hs : 1≤s) (hhn : h≤n)
    (hc : QHalfCert n K s ps) (hm : QTraceMidpointCover n s h ps qs)
    (hg : ∀ p∈ps,QueueMargin n K s h p.1) :
    QHalfCert n K (s+h) qs :=
  ⟨qcover_next_trace n s h ps qs hs hhn hc.cover hm,qmargin_next n K s h ps hn heven hs hc hg⟩

/-- A larger certified search budget may be shrunk to the first empty
    midpoint layer. The margin polynomial is monotone in K. -/
theorem qcert_shrink (n K K' s : Nat) (ps : List QPrefix) (hK : K'≤K)
    (hc : QHalfCert n K s ps) : QHalfCert n K' s ps := by
  refine ⟨hc.cover,?_⟩
  intro j hj hjs B a ht
  have h1 : n+K'+2≤n+K+2 := by omega
  have h2 : marginSize n K'≤marginSize n K := by unfold marginSize; omega
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2))
    (hc.margins j hj hjs B a ht)

theorem qcert_empty (n K s : Nat) (hn : 1≤n) (heven : n%2=0) (hs : 2≤s)
    (hc : QHalfCert n K s []) : Cert n K s [] := by
  have hh : HalfCovered n s [] := by
    intro B a C c ht hm he
    have h := hc.cover B a C c ht hm he
    simp at h
  exact ⟨by simpa using complete_half n s [] hn heven hs hh,hc.margins⟩

#print axioms qmargin_next
#print axioms qcover_next_trace
#print axioms qcert_next_trace
#print axioms qcert_shrink
#print axioms qcert_of_half
#print axioms qcover_next
#print axioms queue_margin_sound
#print axioms qcert_next
#print axioms qcert_empty

end BB6.Agent9CompactCover
