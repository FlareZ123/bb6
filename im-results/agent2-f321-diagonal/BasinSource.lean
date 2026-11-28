import BasinDensity

namespace BB6.Agent2F321BasinSource
open BB6.Agent31F321Density
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord
open BB6.Agent2F321DangerCount
open BB6.Agent2F321AnchorDecision
open BB6.Agent2F321Basin
open BB6.Agent2F321BasinDensity

/-- Exact chronological source execution indexed by completed reset count
    and ordinary CounterMove count. No H/F or reset length cutoff. -/
inductive CountedRun : Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (a d : Nat) : CountedRun 0 0 a d a d
  | high {j n a d A D : Nat} (hg : d+2≤a)
      (tail : CountedRun j n (a-d-2) (2*d+3) A D) :
      CountedRun j (n+1) a d A D
  | far {j n a d A D : Nat} (h1 : a<d) (h2 : 3*a+1≤d)
      (tail : CountedRun j n (4*a+6) (d-3*a) A D) :
      CountedRun j (n+1) a d A D
  | reset {j n a d U e A D : Nat} {b : Bool} (hr : Reset b a d U e)
      (tail : CountedRun j n U e A D) : CountedRun (j+1) (n+1) a d A D

theorem reset_source {b a d U e} (hr : Reset b a d U e) : CounterMove a d U e := by
  cases hr with
  | equal a => exact CounterMove.equal a
  | middleEven a d h1 h2 hp => exact CounterMove.middleEven a d h1 h2 hp
  | middleOdd a d h1 h2 hp => exact CounterMove.middleOdd a d h1 h2 hp


/-- Concatenate chronological paths, adding both indices. -/
theorem counted_append {j n i m a d A D U e}
    (hf : CountedRun j n a d A D) (ht : CountedRun i m A D U e) :
    CountedRun (j+i) (n+m) a d U e := by
  induction hf with
  | nil => simpa using ht
  | high hg _ ih => simpa [Nat.add_assoc,Nat.add_comm 1] using CountedRun.high hg (ih ht)
  | far h1 h2 _ ih => simpa [Nat.add_assoc,Nat.add_comm 1] using CountedRun.far h1 h2 (ih ht)
  | reset hr _ ih => simpa [Nat.add_assoc,Nat.add_comm 1] using CountedRun.reset hr (ih ht)

theorem counted_source {j n a d A D} (hc : CountedRun j n a d A D) :
    CounterReach a d n A D := by
  have aux {s r m j n a d A D} (h : CountedRun j n a d A D)
      (hp : CounterReach s r m a d) : CounterReach s r (m+n) A D := by
    induction h generalizing m with
    | nil => simpa using hp
    | high hg _ ih =>
      simpa [Nat.add_assoc,Nat.add_comm 1] using ih (CounterReach.step hp (CounterMove.high _ _ hg))
    | far h1 h2 _ ih =>
      simpa [Nat.add_assoc,Nat.add_comm 1] using ih (CounterReach.step hp (CounterMove.far _ _ h1 h2))
    | reset hr _ ih =>
      simpa [Nat.add_assoc,Nat.add_comm 1] using ih (CounterReach.step hp (reset_source hr))
  simpa using aux hc (CounterReach.nil (seedA:=a) (seedD:=d))

theorem source_counted {n a d A D} (hr : CounterReach a d n A D) :
    ∃ j≤n, CountedRun j n a d A D := by
  induction hr with
  | nil => exact ⟨0,by omega,CountedRun.nil _ _⟩
  | @step n a d A D hp hm ih =>
      rcases ih with ⟨j,hj,hc⟩
      cases hm with
      | high d hg =>
          exact ⟨j,by omega,by simpa using counted_append hc (CountedRun.high hg (CountedRun.nil _ _))⟩
      | far d h1 h2 =>
          exact ⟨j,by omega,by simpa using counted_append hc (CountedRun.far h1 h2 (CountedRun.nil _ _))⟩
      | equal =>
          exact ⟨j+1,by omega,by simpa using counted_append hc (CountedRun.reset (Reset.equal _) (CountedRun.nil _ _))⟩
      | middleEven d h1 h2 hp =>
          exact ⟨j+1,by omega,by simpa using counted_append hc (CountedRun.reset (Reset.middleEven _ _ h1 h2 hp) (CountedRun.nil _ _))⟩
      | middleOdd d h1 h2 hp =>
          exact ⟨j+1,by omega,by simpa using counted_append hc (CountedRun.reset (Reset.middleOdd _ _ h1 h2 hp) (CountedRun.nil _ _))⟩

theorem word_counted {w a d A D} (hw : WordRun w a d A D) :
    CountedRun 0 w.length a d A D := by
  induction hw with
  | nil => exact CountedRun.nil _ _
  | high hg _ ih => exact CountedRun.high hg ih
  | far h1 h2 _ ih => exact CountedRun.far h1 h2 ih

/-- Split before the first reset, retaining exact H/F word and step count. -/
theorem first_reset_split {j n a d A D} (hc : CountedRun j n a d A D) :
    (j=0 ∧ ∃ w, w.length=n ∧ WordRun w a d A D) ∨
    ∃ i m w U e B E b, j=i+1 ∧ n=w.length+1+m ∧
      WordRun w a d B E ∧ Reset b B E U e ∧ CountedRun i m U e A D := by
  induction hc with
  | nil => exact Or.inl ⟨rfl,[],rfl,WordRun.nil _ _⟩
  | high hg _ ih =>
      rcases ih with ⟨hj,w,hw,hr⟩ | ⟨i,m,w,U,e,B,E,b,hj,hn,hw,hrs,ht⟩
      · exact Or.inl ⟨hj,.high::w,by simp [hw],WordRun.high hg hr⟩
      · exact Or.inr ⟨i,m,.high::w,U,e,B,E,b,hj,by simp; omega,WordRun.high hg hw,hrs,ht⟩
  | far h1 h2 _ ih =>
      rcases ih with ⟨hj,w,hw,hr⟩ | ⟨i,m,w,U,e,B,E,b,hj,hn,hw,hrs,ht⟩
      · exact Or.inl ⟨hj,.far::w,by simp [hw],WordRun.far h1 h2 hr⟩
      · exact Or.inr ⟨i,m,.far::w,U,e,B,E,b,hj,by simp; omega,WordRun.far h1 h2 hw,hrs,ht⟩
  | @reset j n a d U e A D b hr ht ih =>
      exact Or.inr ⟨j,n,[],U,e,a,d,b,rfl,by simp; omega,WordRun.nil _ _,hr,ht⟩

/-- The recursively defined basin is precisely the small-second source
    halting basin with the indicated reset budget. -/
theorem counted_basin {j i n R c t} (hc : c=1∨c=2) (hi : i≤j)
    (hr : CountedRun i n R c (t+1) t) : Basin j R c := by
  induction j generalizing i n R c t with
  | zero =>
      rcases first_reset_split hr with ⟨_,w,_,hw⟩ | ⟨q,m,w,U,e,B,E,b,he,hn,hw,hrs,ht⟩
      · exact (dangerous_iff_word hc).mpr ⟨w,t,hw⟩
      · omega
  | succ j ih =>
      rcases first_reset_split hr with ⟨_,w,_,hw⟩ | ⟨q,m,w,U,e,B,E,b,he,hn,hw,hrs,ht⟩
      · exact Or.inl ((dangerous_iff_word hc).mpr ⟨w,t,hw⟩)
      · exact Or.inr ⟨hc,U,e,⟨w,B,E,b,hw,hrs⟩,ih (reset_output_small hrs) (by omega) ht⟩

theorem basin_counted {j R c} (hb : Basin j R c) :
    ∃ i≤j, ∃ n t, CountedRun i n R c (t+1) t := by
  induction j generalizing R c with
  | zero =>
      rcases (dangerous_iff_word hb.1).mp hb with ⟨w,t,hw⟩
      exact ⟨0,by omega,w.length,t,word_counted hw⟩
  | succ j ih =>
      change DangerousAnchor R c ∨ (c=1∨c=2) ∧ ∃ U e, Epoch R c U e ∧ Basin j U e at hb
      rcases hb with hd | ⟨hc,U,e,⟨w,a,d,b,hw,hr⟩,hb⟩
      · rcases (dangerous_iff_word hd.1).mp hd with ⟨w,t,hw⟩
        exact ⟨0,by omega,w.length,t,word_counted hw⟩
      · rcases ih hb with ⟨i,hi,n,t,ht⟩
        exact ⟨i+1,by omega,w.length+(n+1),t,by
          simpa [Nat.add_comm 1] using counted_append (word_counted hw) (CountedRun.reset hr ht)⟩

theorem basin_iff_counted {j R c} (hc : c=1∨c=2) : Basin j R c ↔
    ∃ i≤j, ∃ n t, CountedRun i n R c (t+1) t := by
  constructor
  · exact basin_counted
  · rintro ⟨i,hi,n,t,hr⟩
    exact counted_basin hc hi hr

/-- All possible source halts belong to the increasing union of basins.
    The fixed-depth density estimate alone does not control this union. -/
theorem source_halt_iff_basin {R c} (hc : c=1∨c=2) :
    (∃ n t, CounterReach R c n (t+1) t) ↔ ∃ j, Basin j R c := by
  constructor
  · rintro ⟨n,t,hr⟩
    rcases source_counted hr with ⟨j,_,hc'⟩
    exact ⟨j,counted_basin hc (by omega) hc'⟩
  · rintro ⟨j,hb⟩
    rcases basin_counted hb with ⟨i,_,n,t,hr⟩
    exact ⟨n,t,counted_source hr⟩

theorem source_basin_count_bound (j k : Nat) (hk : 2≤k) (xs : List (Nat×Nat))
    (hnd : xs.Nodup) (hall : ∀ p∈xs, p.1≤2^k ∧ (p.2=1∨p.2=2) ∧
      ∃ i≤j, ∃ n t, CountedRun i n p.1 p.2 (t+1) t) :
    xs.length≤C j*scalePoly j k*2^(k-gap j k) := by
  apply basin_count_dyadic j k hk xs hnd
  intro p hp
  rcases hall p hp with ⟨hR,hc,i,hi,n,t,hr⟩
  exact ⟨hR,counted_basin hc hi hr⟩

#print axioms counted_append
#print axioms counted_source
#print axioms source_counted
#print axioms first_reset_split
#print axioms basin_iff_counted
#print axioms source_halt_iff_basin
#print axioms source_basin_count_bound
end BB6.Agent2F321BasinSource
