import FiniteSlopePacking
import CyclicPrimitiveFinite

namespace PeriodicMacro
open ValuationPacking
open FiniteCyclicValuation

def defaultLetter : Letter := ⟨1,true⟩

private theorem slope_step_cone {x : Letter} {K d e : Nat}
    (hj : 0<x.j) (heq : scale x*e=d+K)
    (hd : 0<d) (hcone : 3*d<K) :
    0<e ∧ 3*e<K := by
  have hs : 4≤scale x := scale_ge_four x hj
  have hepos : 0<e := by
    by_cases hz : e=0
    · subst e
      simp at heq
      omega
    · exact Nat.pos_of_ne_zero hz
  have h4 : 4*e≤d+K := by
    have hm := Nat.mul_le_mul_right e hs
    rw [heq] at hm
    simpa [Nat.mul_comm] using hm
  exact ⟨hepos,by omega⟩

theorem slopeWalkSources_length {K : Nat} {xs : List Letter} {ds : List Nat}
    {d f : Nat} (h : SlopeWalkSources K xs ds d f) : ds.length=xs.length := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem slopeWalkSources_j_pos_at {K : Nat} {xs : List Letter} {ds : List Nat}
    {d f : Nat} (h : SlopeWalkSources K xs ds d f)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (i : Nat) (hi : i<xs.length) :
    0 < (xs.getD i defaultLetter).j := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons x xs ds d e f heq tail ih =>
      cases i with
      | zero => simpa [defaultLetter] using hj x (by simp)
      | succ i =>
          rw [List.getD_cons_succ]
          apply ih
          · intro y hy
            exact hj y (by simp [hy])
          · simp at hi
            omega

theorem slopeWalkSources_good_at {K : Nat} {xs : List Letter} {ds : List Nat}
    {d f : Nat} (h : SlopeWalkSources K xs ds d f)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hd : 0<d) (hcone : 3*d<K)
    (i : Nat) (hi : i<ds.length) :
    0 < ds.getD i f ∧ 3*(ds.getD i f)<K := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons x xs ds d e f heq tail ih =>
      have hxj : 0<x.j := hj x (by simp)
      have hnext := slope_step_cone hxj heq hd hcone
      cases i with
      | zero => simpa using And.intro hd hcone
      | succ i =>
          rw [List.getD_cons_succ]
          apply ih
          · intro y hy
            exact hj y (by simp [hy])
          · exact hnext.1
          · exact hnext.2
          · simp at hi
            omega

theorem slopeWalkSources_head {K : Nat} {xs : List Letter} {ds : List Nat}
    {d f : Nat} (h : SlopeWalkSources K xs ds d f) : ds.getD 0 f=d := by
  cases h with
  | nil => simp
  | cons head tail => simp

theorem slopeWalkSources_step_at {K : Nat} {xs : List Letter} {ds : List Nat}
    {d f : Nat} (h : SlopeWalkSources K xs ds d f)
    (i : Nat) (hi : i<xs.length) :
    scale (xs.getD i defaultLetter) * ds.getD (i+1) f =
      ds.getD i f + K := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons x xs ds d e f heq tail ih =>
      cases i with
      | zero =>
          rw [List.getD_cons_zero, List.getD_cons_succ]
          rw [slopeWalkSources_head tail]
          exact heq
      | succ i =>
          rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
          apply ih
          simp at hi
          omega

def slopeSourceFun {n : Nat} (ds : List Nat) (d : Nat) (i : Fin n) : Nat :=
  ds.getD i.val d

def slopeExponentFun {n : Nat} (xs : List Letter) (i : Fin n) : Nat :=
  (xs.getD i.val defaultLetter).j

theorem closedSlope_cyclicWitness {K : Nat} {xs : List Letter} {ds : List Nat}
    {d : Nat} (h : SlopeWalkSources K xs ds d d)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hd : 0<d) (hcone : 3*d<K)
    (hn : 0<xs.length) :
    CyclicWitness K hn (slopeSourceFun ds d) (slopeExponentFun xs) := by
  intro i
  have hlen := slopeWalkSources_length h
  have hiXs : i.val<xs.length := i.isLt
  have hiDs : i.val<ds.length := by omega
  have hgood := slopeWalkSources_good_at h hj hd hcone i.val hiDs
  have hjp := slopeWalkSources_j_pos_at h hj i.val hiXs
  have hstep := slopeWalkSources_step_at h i.val hiXs
  constructor
  · exact hgood.1
  constructor
  · exact hgood.2
  constructor
  · exact hjp
  · unfold slopeSourceFun slopeExponentFun
    unfold FiniteCyclicValuation.succ
    split
    · simpa [scale] using hstep
    · rename_i hlast
      have hiLast : i.val+1=ds.length := by omega
      rw [hiLast] at hstep
      have hfall : ds.getD ds.length d=d := by simp [List.getD]
      rw [hfall] at hstep
      have hzero : ds.getD 0 d=d := slopeWalkSources_head h
      rw [hzero]
      simpa [scale] using hstep

private theorem nodup_map_inj_adapter {α β : Type} (f : α → β)
    (hinj : Function.Injective f) {l : List α} (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot,ht⟩ := List.nodup_cons.mp h
    simp only [List.map_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
      exact hnot ((hinj he.symm) ▸ hy)
    · exact ih ht

theorem closedSlope_sources_nodup {K : Nat} {xs : List Letter} {ds : List Nat}
    {d : Nat} (h : SlopeWalkSources K xs ds d d)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hd : 0<d) (hcone : 3*d<K)
    (hn : 0<xs.length)
    (hprim : CyclicPrimitive hn (slopeExponentFun xs)) : ds.Nodup := by
  have hw := closedSlope_cyclicWitness h hj hd hcone hn
  have hinj := FiniteCyclicValuation.source_injective K hn
    (slopeSourceFun ds d) (slopeExponentFun xs) hw hprim
  have hmapN : ((List.finRange xs.length).map (slopeSourceFun ds d)).Nodup :=
    nodup_map_inj_adapter (slopeSourceFun ds d) hinj (List.nodup_finRange xs.length)
  have hlen := slopeWalkSources_length h
  have hmap : (List.finRange xs.length).map (slopeSourceFun ds d)=ds := by
    rw [List.finRange, List.map_ofFn]
    change List.ofFn (fun i : Fin xs.length => ds.getD i.val d)=ds
    apply List.ext_get
    · simp [hlen]
    · intro i h1 h2
      simp only [List.length_ofFn] at h1
      have hiDs : i<ds.length := by omega
      simp [List.getD, hiDs]
  rwa [hmap] at hmapN

#print axioms closedSlope_cyclicWitness
#print axioms closedSlope_sources_nodup
end PeriodicMacro
