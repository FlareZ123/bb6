import CompactMidpoint
import PackedMidpoint
import LagSource

namespace BB6.Agent9CompactCertificate

open BB6.Agent45.DelayedCarry
open BB6.Agent9CompactState
open BB6.Agent9CompactCover
open BB6.Agent9CompactMidpoint
open BB6.Agent9PackedMidpoint (packed_half_first_prop)

theorem qcode_source (n s B k c : Nat) :
    recover n B s k c=
      (B+2^s*(qCode n s (quotient n s B) k c).1,
        (qCode n s (quotient n s B) k c).2) := by
  induction k generalizing c with
  | zero => simp [recover,qCode]
  | succ k ih =>
    simp only [recover,qCode,predecessor,reverseDigit,qTarget,fixed_target]
    rw [ih]
    apply Prod.ext
    · simp only [Nat.pow_add,Nat.mul_add]; ac_rfl
    · rfl

/-- Filter only the first selected bit: all subsequent canonicality is
    inherited from the already-certified parent. -/
def qRecoverCanonical (n s h : Nat) (ps : List QPrefix) (mids : Nat → List Nat) : List QPrefix :=
  ps.flatMap fun p => (mids p.1).filterMap fun c =>
    let r := qCode n s p.1 h c
    if r.2=p.2 ∧ (s≠1 ∨ r.1%2=0) then some ((p.1+total n*r.1)/2^h,c) else none

theorem qtrace_midpoint_of_live (n s h : Nat) (ps : List QPrefix)
    (mids : Nat → List Nat) (hhn : h≤n) (hLive : QLive n s h ps mids) :
    QTraceMidpointCover n s h ps (qRecoverCanonical n s h ps mids) := by
  intro B a C c hp ht hcanon he htail
  obtain ⟨D,d,hsuf⟩ := htail
  have ha : a<n+s+3 := by
    have hh := (trace_bounds n s B a ht).2.2.2
    omega
  have hpre := project n s B a h C c he
  have hsuf' := project n (s+h) C c (n-h) D d hsuf
  have hc := qextend_carry_lt n s (quotient n s B) a h (quotient n (s+h) C) c ha hpre
  have hw := qextend_walk n (s+h) _ c (n-h) _ d (by omega) (by omega) hsuf'
  rw [qword_shift n s _ a h _ c (n-h) hpre (by omega)] at hw
  have hm := hLive _ a hp d c hw
  obtain ⟨hr,hQ⟩ := qcode_exact n s _ a h _ c ha hhn hpre
  have hword := qcode_source n s B h c
  rw [recover_exact n s B a h C c ht he hhn] at hword
  have hC := congrArg Prod.fst hword
  change C=B+2^s*(qCode n s (quotient n s B) h c).1 at hC
  have hfilter : s≠1 ∨ (qCode n s (quotient n s B) h c).1%2=0 := by
    by_cases hs : s=1
    · right
      subst s
      obtain ⟨_,hB,hodd,_⟩ := trace_bounds n 1 B a ht
      have hB' : B=1 := by simp at hB; omega
      rw [hB'] at hC
      simp only [Nat.reducePow] at hC
      omega
    · exact Or.inl hs
  unfold qRecoverCanonical
  apply List.mem_flatMap.mpr
  refine ⟨(quotient n s B,a),hp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨c,hm,?_⟩
  simp only [hr,hfilter,true_and,ite_true,Option.some.injEq,Prod.mk.injEq,and_true]
  exact hQ.symm

theorem qcert_canonical_live (n K s h : Nat) (ps qs : List QPrefix)
    (mids : Nat → List Nat) (hn : 1≤n) (heven : n%2=0)
    (hs : 1≤s) (hhn : h≤n) (hc : QHalfCert n K s ps)
    (hLive : QLive n s h ps mids)
    (hcontains : ∀ p∈qRecoverCanonical n s h ps mids,p∈qs)
    (hg : ∀ p∈ps,QueueMargin n K s h p.1) :
    QHalfCert n K (s+h) qs := by
  apply qcert_next_trace n K s h ps qs hn heven hs hhn hc _ hg
  intro B a C c hp ht hcanon he htail
  exact hcontains _ (qtrace_midpoint_of_live n s h ps mids hhn hLive
    B a C c hp ht hcanon he htail)

/-- Empty midpoint image proves extinction at the PARENT horizon n+s,
    exactly matching the numerical solver's END line. -/
theorem qcover_empty_midpoint (n s h : Nat) (ps : List QPrefix)
    (hs : 2≤s) (hhn : h≤n) (hc : QHalfCovered n s ps)
    (hm : QTraceMidpointCover n s h ps []) : QHalfCovered n s [] := by
  intro B a C c ht hcanon he
  obtain ⟨D,d,hpre,hsuf⟩ := extend_split n s B a n C c h he hhn
  have hD : D%4=1 := by
    obtain ⟨X,hX⟩ := extend_mod n s B a h D d hpre
    have hd : 4 ∣ (2:Nat)^s := by simpa using Nat.pow_dvd_pow 2 hs
    rw [hX,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd,hcanon]
    simp
  have h := hm B a D d (hc B a C c ht hcanon he) ht hD hpre ⟨C,c,hsuf⟩
  simp at h

theorem qcert_empty_midpoint (n K s h : Nat) (ps : List QPrefix)
    (hs : 2≤s) (hhn : h≤n) (hc : QHalfCert n K s ps)
    (hm : QTraceMidpointCover n s h ps []) : QHalfCert n K s [] :=
  ⟨qcover_empty_midpoint n s h ps hs hhn hc.cover hm,hc.margins⟩

theorem qcert_empty_live (n K s h : Nat) (ps : List QPrefix)
    (mids : Nat → List Nat) (hs : 2≤s) (hhn : h≤n)
    (hc : QHalfCert n K s ps) (hLive : QLive n s h ps mids)
    (hempty : qRecoverCanonical n s h ps mids=[]) :
    QHalfCert n K s [] := by
  apply qcert_empty_midpoint n K s h ps hs hhn hc
  rw [←hempty]
  exact qtrace_midpoint_of_live n s h ps mids hhn hLive

theorem qcert_first (n K : Nat)
    (hgood : (n+K+2)*marginSize n K*2<6*2^n) :
    QHalfCert n K 1 [(quotient n 1 1,(n+2)/2)] :=
  qcert_of_half n K 1 [(1,(n+2)/2)] (packed_half_first_prop n K hgood)

theorem qcert_n45_first :
    QHalfCert 45352466 900000000 1 [(quotient 45352466 1 1,(45352466+2)/2)] := by
  apply qcert_first
  have hp : (2:Nat)^64≤2^45352466 := Nat.pow_le_pow_right (by decide) (by decide)
  have hsmall : (45352466+900000000+2)*marginSize 45352466 900000000*2<6*2^64 := by decide
  exact Nat.lt_of_lt_of_le hsmall (Nat.mul_le_mul_left 6 hp)

theorem critical_no_reach_of_qcert (n K s : Nat) (hn : 14≤n) (heven : n%2=0)
    (hs : 2≤s) (hK : n+s≤K) (hA : n+(n+s)+2≤2^n)
    (hgap : (n+(n+s)+2)*marginSize n (n+s)<6*2^n)
    (hc : QHalfCert n K s []) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=
  critical_reset_no_reach_of_lag n (n+s) s hn heven (by omega) rfl hA hgap
    (qcert_empty n (n+s) s (by omega) heven hs (qcert_shrink n K (n+s) s [] hK hc))

/-- The actual n45M source goal follows from any empty compact certificate
    within the 900M search budget.  No huge numeral is evaluated. -/
theorem critical_n45_no_reach (s : Nat) (hs : 2≤s)
    (hK : 45352466+s≤900000000) (hc : QHalfCert 45352466 900000000 s []) :
    ¬ BB6.Agent1.Reach 2 (14*2^45352466-2*45352466-10) := by
  apply critical_no_reach_of_qcert 45352466 900000000 s (by decide) (by decide) hs hK _ _ hc
  · have hp : (2:Nat)^64≤2^45352466 := Nat.pow_le_pow_right (by decide) (by decide)
    exact Nat.le_trans (show 45352466+(45352466+s)+2≤2^64 by omega) hp
  · have hp : (2:Nat)^64≤2^45352466 := Nat.pow_le_pow_right (by decide) (by decide)
    have ha : 45352466+(45352466+s)+2≤45352466+900000000+2 := by omega
    have hb : marginSize 45352466 (45352466+s)≤marginSize 45352466 900000000 := by unfold marginSize; omega
    have hsmall : (45352466+900000000+2)*marginSize 45352466 900000000<6*2^64 := by decide
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul ha hb)
      (Nat.lt_of_lt_of_le hsmall (Nat.mul_le_mul_left 6 hp))

/-- Packed queue update: the low h delayed bits leave; the selected word
    enters at position n-h. -/
theorem queue_update (n h Q X : Nat) (hh : h≤n) :
    (Q+total n*X)/2^h=Q/2^h+2^(n-h)*(7*X) := by
  have hp : (2:Nat)^n=2^h*2^(n-h) := by rw [←Nat.pow_add]; congr 1; omega
  have he : total n*X=2^h*(2^(n-h)*(7*X)) := by unfold total; rw [hp]; ac_rfl
  rw [he,Nat.add_mul_div_left _ _ (Nat.two_pow_pos h)]

/-- The actual stored low queue and multiplication carry update, exactly
    the r+7*word operation used by the C++ block reconstruction. -/
theorem queue_update_split (n h lo r X : Nat) (hh : h≤n) :
    ((lo+2^n*r)+total n*X)/2^h =
      lo/2^h+2^(n-h)*((r+7*X)%2^h)+2^n*((r+7*X)/2^h) := by
  rw [queue_update n h _ X hh]
  have hp : (2:Nat)^n=2^h*2^(n-h) := by rw [←Nat.pow_add]; congr 1; omega
  have he : 2^n*r=2^h*(2^(n-h)*r) := by rw [hp]; ac_rfl
  rw [he,Nat.add_mul_div_left _ _ (Nat.two_pow_pos h)]
  have hD := Nat.div_add_mod (r+7*X) (2^h)
  have hmul := congrArg (fun t : Nat => 2^(n-h)*t) hD
  rw [Nat.mul_add] at hmul
  have hf : 2^(n-h)*(2^h*((r+7*X)/2^h))=2^n*((r+7*X)/2^h) := by rw [hp]; ac_rfl
  rw [hf] at hmul
  rw [Nat.mul_add] at hmul
  omega

theorem queue_mul_carry_bound (h r X : Nat) (hr : r<7) (hX : X<2^h) :
    (r+7*X)/2^h<7 := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).2
  omega

#print axioms qcode_source
#print axioms qtrace_midpoint_of_live
#print axioms qcert_canonical_live
#print axioms qcover_empty_midpoint
#print axioms qcert_empty_live
#print axioms qcert_first
#print axioms qcert_n45_first
#print axioms critical_no_reach_of_qcert
#print axioms critical_n45_no_reach
#print axioms queue_update
#print axioms queue_update_split
#print axioms queue_mul_carry_bound
end BB6.Agent9CompactCertificate
