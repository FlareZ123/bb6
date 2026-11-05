import OneResetCount
set_option maxRecDepth 2048
namespace BB6.Agent12TwoReset
open BB6.Agent47P1 BB6.Agent1UpperTail BB6.Agent28

/-- Canonical grammar of positive-depth original inverseAt resets
    separated by authentic t=0 UpperTail segments. -/
inductive Packed (b0 d0 : Nat) : Nat→Nat→Nat→Nat→Prop where
  | zero {b d m r:Nat} (h: UpperTail b0 d0 0 b d m r) :
      Packed b0 d0 b d m 0
  | plus {bp dp mp b d m z r t k c:Nat}
      (hp:Packed b0 d0 bp dp mp z)
      (hb : 8≤bp)(hb4 : bp%4=0)(hd : dp%2=1)
      (hi:inverseAt bp dp t=some (k,c))
      (hk : 2≤k)(hc : c%2=1)(ht : 1≤t)
      (htail:UpperTail (2*k-4) (c+4) (mp+t+1) b d m r) :
      Packed b0 d0 b d m (z+1)

theorem packed_step_zero {b0 d0 b d m z k c : Nat}
    (hp:Packed b0 d0 b d m z)
    (hb : 8≤b)(hb4 : b%4=0)(hd : d%2=1)
    (hi:inverseAt b d 0=some (k,c))(hk : 2≤k)(hc : c%2=1) :
    Packed b0 d0 (2*k-4) (c+4) (m+1) z := by
  cases hp with
  | zero htail =>
      exact Packed.zero (UpperTail.step b d m _ k c htail hb hb4 hd hi hk hc)
  | plus prev hbp hbp4 hdp hip hkp hcp htp htail =>
      exact Packed.plus prev hbp hbp4 hdp hip hkp hcp htp
        (UpperTail.step b d m _ k c htail hb hb4 hd hi hk hc)

/-- The source CountCone reset counter faithfully admits canonical packing. -/
theorem packed_of_count {b0 d0 b d m z : Nat}
    (h:CountCone b0 d0 b d m z) : Packed b0 d0 b d m z := by
  induction h with
  | root => exact Packed.zero UpperTail.root
  | parent b d m z t k c hprev hb hb4 hd hi hk hc ih =>
      by_cases ht:t=0
      · subst t
        simpa only [ite_true,Nat.add_zero] using
          (packed_step_zero ih hb hb4 hd hi hk hc)
      · have htpos:1≤t := by omega
        have hr := Packed.plus ih hb hb4 hd hi hk hc htpos
          (UpperTail.root : UpperTail (2*k-4) (c+4) (m+t+1)
              (2*k-4) (c+4) (m+t+1) 0)
        simpa only [if_neg ht] using hr

/-- Exactly two positive resets imply an authentic five-section source history.
    No arithmetic nor blank-reachability assumption is needed. -/
theorem packed_two_shape {b0 d0 b d m:Nat}
    (h: Packed b0 d0 b d m 2) :
    ∃ bp dp mp r t k c bm dm mm s v j e u,
      UpperTail b0 d0 0 bp dp mp r ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t=some (k,c) ∧ 2≤k ∧ c%2=1 ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) bm dm mm s ∧
      8≤bm ∧ bm%4=0 ∧ dm%2=1 ∧
      inverseAt bm dm v=some (j,e) ∧ 2≤j ∧ e%2=1 ∧ 1≤v ∧
      UpperTail (2*j-4) (e+4) (mm+v+1) b d m u := by
  cases h with
  | plus hp hb hb4 hd hi hk hc ht htail =>
      cases hp with
      | plus hp0 hbp hbp4 hdp hip hkp hcp htp hmid =>
          cases hp0 with
          | zero hpre =>
              exact ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
                hpre,hbp,hbp4,hdp,hip,hkp,hcp,htp,
                hmid,hb,hb4,hd,hi,hk,hc,ht,htail⟩

/-- Exact two-reset decomposition for original source CountCone. -/
theorem count_two_shape {b0 d0 b d m:Nat}
    (h: CountCone b0 d0 b d m 2) :
    ∃ bp dp mp r t k c bm dm mm s v j e u,
      UpperTail b0 d0 0 bp dp mp r ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t=some (k,c) ∧ 2≤k ∧ c%2=1 ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) bm dm mm s ∧
      8≤bm ∧ bm%4=0 ∧ dm%2=1 ∧
      inverseAt bm dm v=some (j,e) ∧ 2≤j ∧ e%2=1 ∧ 1≤v ∧
      UpperTail (2*j-4) (e+4) (mm+v+1) b d m u :=
  packed_two_shape (packed_of_count h)

#print axioms packed_of_count
#print axioms count_two_shape
end BB6.Agent12TwoReset
