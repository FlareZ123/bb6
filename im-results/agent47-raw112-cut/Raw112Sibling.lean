import Raw112CarryRoot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112Sibling
open BB6Coverage BB6Coverage.Agent31Pump Raw112CarrySweeps Raw112CarryRoot

def sibling : PartialMachine := fun s =>
  if s = (5,true) then some (some ⟨true,true,1⟩) else table s

/-- The long F1/E0/A0 segment writes the same tape as the short F1 move. -/
theorem special (L R : List Bool) :
    run0 table 4 ⟨0,true::L,true::R⟩ = some ⟨1,R.headD false::true::false::L,R.tail⟩ ∧
    run0 sibling 2 ⟨0,true::L,true::R⟩ = some ⟨1,R.headD false::true::false::L,R.tail⟩ := by
  exact ⟨rfl,rfl⟩

theorem chunk (z : Z0) (hq : z.q ≠ 5)
    (h : ∃ y, run0 table 4 z = some y) :
    ∃ a b z', 0<a ∧ a≤4 ∧ 0<b ∧ run0 table a z = some z' ∧
      run0 sibling b z = some z' ∧ z'.q ≠ 5 := by
  rcases z with ⟨q,l,r⟩
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 := by
    have hqv : q.val < 6 := q.isLt
    have hn : q.val ≠ 5 := by
      intro he
      apply hq
      exact Fin.ext he
    omega
  rcases hq' with hq'|hq'|hq'|hq'|hq' <;> subst q
  · cases l with
    | nil => exact ⟨1,1,_,by decide,by decide,by decide,rfl,rfl,by simp [move0]⟩
    | cons b L =>
      cases b with
      | false => exact ⟨1,1,_,by decide,by decide,by decide,rfl,rfl,by simp [move0]⟩
      | true =>
        cases r with
        | nil =>
          obtain ⟨y,hy⟩ := h
          have hn : run0 table 2 ⟨0,true::L,[]⟩ = none := rfl
          rw [show 4=2+2 by decide,run0_add,hn] at hy
          contradiction
        | cons b R =>
          cases b with
          | false =>
            obtain ⟨y,hy⟩ := h
            have hn : run0 table 2 ⟨0,true::L,false::R⟩ = none := rfl
            rw [show 4=2+2 by decide,run0_add,hn] at hy
            contradiction
          | true =>
            exact ⟨4,2,_,by decide,by decide,by decide,(special L R).1,(special L R).2,by simp⟩
  all_goals
    cases l with
    | nil => exact ⟨1,1,_,by decide,by decide,by decide,rfl,rfl,by simp [move0]⟩
    | cons b L => cases b <;> exact ⟨1,1,_,by decide,by decide,by decide,rfl,rfl,by simp [move0]⟩

/-- Successful original prefixes of length 4*n yield successful sibling prefixes
    of length at least n, starting from any non-F state. -/
theorem transfer (n : Nat) (z : Z0) (hq : z.q ≠ 5)
    (h : ∃ t y, 4*n≤t ∧ run0 table t z = some y) :
    ∃ t y, n≤t ∧ run0 sibling t z = some y := by
  induction n generalizing z with
  | zero => exact ⟨0,z,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨t,y,ht,hr⟩ := h
    have h4 : ∃ y, run0 table 4 z = some y := by
      have hr' := hr
      rw [show t=4+(t-4) by omega,run0_add] at hr'
      cases he : run0 table 4 z with
      | none => simp [he] at hr'
      | some a => exact ⟨a,rfl⟩
    obtain ⟨a,b,z',ha,ha4,hb,hA,hB,hq'⟩ := chunk z hq h4
    rw [show t=a+(t-a) by omega,run0_add,hA] at hr
    have hr' : run0 table (t-a) z' = some y := hr
    obtain ⟨u,v,hu,hv⟩ := ih z' hq' ⟨t-a,y,by omega,hr'⟩
    exact ⟨b+u,v,by omega,join0 hB hv⟩

theorem sibling_unbounded (N : Nat) : ∃ t z, N≤t ∧ run0 sibling t ⟨0,[],[]⟩ = some z := by
  obtain ⟨t,n,ht,hr⟩ := unbounded_live (4*N)
  exact transfer N ⟨0,[],[]⟩ (by decide) ⟨t,family n,ht,hr⟩

#print axioms special
#print axioms transfer
#print axioms sibling_unbounded
end BB6Coverage.Agent31Pump.Raw112Sibling
