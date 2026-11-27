import SweepPumping
namespace BB6.Agent38Raw43Pair
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨v,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some (if v then ⟨false,true,3⟩ else ⟨false,false,1⟩))
  | _,_ => none

def Live (p : PartialMachine) (z : Z0) : Prop := ∀ n, ∃ d, run0 p n z = some d

def synced (z : Z0) : Prop := z.q ≠ 5

theorem safe_macro (v : Bool) (L R : List Bool) :
    run0 (table v) (if v then 2 else 4) ⟨4,false::L,false::R⟩ =
    some ⟨3,R.headD false::false::true::L,R.tail⟩ := by cases v <;> rfl

theorem safe_blank (v : Bool) (L : List Bool) :
    run0 (table v) (if v then 2 else 4) ⟨4,false::L,[]⟩ =
    some ⟨3,false::false::true::L,[]⟩ := by cases v <;> rfl

theorem bad_macro (v : Bool) (L R : List Bool) :
    run0 (table v) 2 ⟨4,false::L,true::R⟩ = none := by cases v <;> rfl

def next (z : Z0) := (run0 (table false) 1 z).getD z

private theorem common_step (z : Z0) (h : synced z)
    (he : z.q ≠ 4 ∨ z.l.headD false = true) :
    synced (next z) ∧ ∀ v, run0 (table v) 1 z = some (next z) := by
  rcases z with ⟨q,l,r⟩
  have hq : q.val < 6 := q.isLt
  have hf : q.val ≠ 5 := by
    intro hh
    apply h
    exact Fin.ext hh
  rcases he with he | he
  · have h4 : q.val ≠ 4 := by
      intro hh
      apply he
      exact Fin.ext hh
    have hh : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 ∨ q.val = 3 := by omega
    rcases hh with hh|hh|hh|hh <;> (
      first | have hq' : q = (0 : Fin 6) := Fin.ext hh | have hq' : q = (1 : Fin 6) := Fin.ext hh | have hq' : q = (2 : Fin 6) := Fin.ext hh | have hq' : q = (3 : Fin 6) := Fin.ext hh
      subst q
      cases l with
      | nil => exact ⟨by (first | change (0 : Fin 6) ≠ 5; decide | change (1 : Fin 6) ≠ 5; decide | change (2 : Fin 6) ≠ 5; decide | change (3 : Fin 6) ≠ 5; decide | change (4 : Fin 6) ≠ 5; decide),fun v => by cases v <;> rfl⟩
      | cons b L => cases b <;> exact ⟨by (first | change (0 : Fin 6) ≠ 5; decide | change (1 : Fin 6) ≠ 5; decide | change (2 : Fin 6) ≠ 5; decide | change (3 : Fin 6) ≠ 5; decide | change (4 : Fin 6) ≠ 5; decide),fun v => by cases v <;> rfl⟩)
  · have hh : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4 := by omega
    rcases hh with hh|hh|hh|hh|hh <;> (
      first | have hq' : q = (0 : Fin 6) := Fin.ext hh | have hq' : q = (1 : Fin 6) := Fin.ext hh | have hq' : q = (2 : Fin 6) := Fin.ext hh | have hq' : q = (3 : Fin 6) := Fin.ext hh | have hq' : q = (4 : Fin 6) := Fin.ext hh
      subst q
      cases l with
      | nil => contradiction
      | cons b L => cases b <;> first | contradiction | exact ⟨by (first | change (0 : Fin 6) ≠ 5; decide | change (1 : Fin 6) ≠ 5; decide | change (2 : Fin 6) ≠ 5; decide | change (3 : Fin 6) ≠ 5; decide | change (4 : Fin 6) ≠ 5; decide),fun v => by cases v <;> rfl⟩)

private theorem advance (z : Z0) (h : synced z) :
    (∃ d, synced d ∧ ∀ v, ∃ k, 0 < k ∧ run0 (table v) k z = some d) ∨
    (∀ v, run0 (table v) 2 z = none) := by
  by_cases he : z.q = 4
  · by_cases hb : z.l.headD false = true
    · obtain ⟨hs,hr⟩ := common_step z h (Or.inr hb)
      exact Or.inl ⟨next z,hs,fun v => ⟨1,by decide,hr v⟩⟩
    · rcases z with ⟨q,l,r⟩
      change q = 4 at he
      subst q
      cases l with
      | nil =>
        cases r with
        | nil => exact Or.inl ⟨⟨3,[false,false,true],[]⟩,by (change (3 : Fin 6) ≠ 5; decide),fun v => ⟨if v then 2 else 4,by cases v <;> decide,by cases v <;> rfl⟩⟩
        | cons b R =>
          cases b with
          | false => exact Or.inl ⟨⟨3,R.headD false::false::true::[],R.tail⟩,by (change (3 : Fin 6) ≠ 5; decide),fun v => ⟨if v then 2 else 4,by cases v <;> decide,by cases v <;> rfl⟩⟩
          | true => exact Or.inr (fun v => by cases v <;> rfl)
      | cons b L =>
        cases b with
        | true => exact False.elim (hb rfl)
        | false =>
          cases r with
          | nil => exact Or.inl ⟨⟨3,false::false::true::L,[]⟩,by (change (3 : Fin 6) ≠ 5; decide),fun v => ⟨if v then 2 else 4,by cases v <;> decide,safe_blank v L⟩⟩
          | cons b R =>
            cases b with
            | false => exact Or.inl ⟨⟨3,R.headD false::false::true::L,R.tail⟩,by (change (3 : Fin 6) ≠ 5; decide),fun v => ⟨if v then 2 else 4,by cases v <;> decide,safe_macro v L R⟩⟩
            | true => exact Or.inr (fun v => bad_macro v L R)
  · obtain ⟨hs,hr⟩ := common_step z h (Or.inl he)
    exact Or.inl ⟨next z,hs,fun v => ⟨1,by decide,hr v⟩⟩

private theorem live_after {p : PartialMachine} {z d : Z0} {k : Nat}
    (h : run0 p k z = some d) (hl : Live p z) : Live p d := by
  intro n
  obtain ⟨e,he⟩ := hl (k+n)
  rw [run0_add,h] at he
  exact ⟨e,he⟩

private theorem live_prefix {p : PartialMachine} {z d : Z0} {k n : Nat}
    (h : run0 p k z = some d) (hn : n ≤ k) : ∃ e, run0 p n z = some e := by
  rw [show k=n+(k-n) by omega,run0_add] at h
  cases he : run0 p n z with
  | none => simp [he] at h
  | some e => exact ⟨e,rfl⟩

theorem transfer (v w : Bool) (z : Z0) (hs : synced z) (hl : Live (table v) z) : Live (table w) z := by
  have arb : ∀ n, ∃ k d, n≤k ∧ run0 (table w) k z=some d ∧ synced d ∧ Live (table v) d := by
    intro n
    induction n with
    | zero => exact ⟨0,z,by omega,rfl,hs,hl⟩
    | succ n ih =>
      obtain ⟨k,d,hk,hr,hds,hdl⟩ := ih
      rcases advance d hds with hgood|hbad
      · obtain ⟨e,hes,hall⟩ := hgood
        obtain ⟨a,ha,haeq⟩ := hall v
        obtain ⟨b,hb,hbeq⟩ := hall w
        exact ⟨k+b,e,by omega,join0 hr hbeq,hes,live_after haeq hdl⟩
      · obtain ⟨e,he⟩ := hdl 2
        rw [hbad v] at he
        contradiction
  intro n
  obtain ⟨k,d,hk,hr,_,_⟩ := arb n
  exact live_prefix hr hk

theorem blank_iff : Live (table false) ⟨0,[],[]⟩ ↔ Live (table true) ⟨0,[],[]⟩ :=
  ⟨transfer false true _ (by (change (0 : Fin 6) ≠ 5; decide)),transfer true false _ (by (change (0 : Fin 6) ≠ 5; decide))⟩

#print axioms blank_iff
end BB6.Agent38Raw43Pair
