import SweepPumping
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39Hard194

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

abbrev O (n : Nat) := rep [true] n
abbrev Z (n : Nat) := rep [false] n

inductive LI : List Bool → Prop
  | tail (k : Nat) (hk : k%3 ≠ 1) : LI (O k)
  | gap (k : Nat) (hk : k%3 ≠ 1) (r : List Bool) (hr : LI r) : LI (O k ++ false::r)
inductive LG : List Bool → Prop
  | tail (k : Nat) (hk : k%3 ≠ 2) : LG (O k)
  | gap (k : Nat) (hk : k%3 ≠ 2) (r : List Bool) (hr : LI r) : LG (O k ++ false::r)
inductive RI : List Bool → Prop
  | tail (k : Nat) : RI (Z k)
  | gap (k : Nat) (hk : 2 ≤ k) (hm : k%3 ≠ 1) (r : List Bool) (hr : RI r) : RI (Z k ++ true::r)
inductive RG : List Bool → Prop
  | tail (k : Nat) : RG (Z k)
  | gap (k : Nat) (hk : 1 ≤ k) (hm : k%3 ≠ 0) (r : List Bool) (hr : RI r) : RG (Z k ++ true::r)

theorem leftPush3 {l} (h : LG l) : LG (true::true::true::l) := by
  cases h with
  | tail k hk => exact LG.tail (k+3) (by omega)
  | gap k hk r hr => exact LG.gap (k+3) (by omega) r hr

theorem leftPush2 {l} (h : LG l) : LG (false::false::true::true::l) := by
  apply LG.gap 0 (by decide)
  apply LI.gap 0 (by decide)
  cases h with
  | tail k hk => exact LI.tail (k+2) (by omega)
  | gap k hk r hr => exact LI.gap (k+2) (by omega) r hr

theorem leftPop {l} (h : LI l) : LG (true::l) := by
  cases h with
  | tail k hk => exact LG.tail (k+1) (by omega)
  | gap k hk r hr => exact LG.gap (k+1) (by omega) r hr

theorem rightInnerPop {r} (h : RI r) : r.headD false = false ∧ RG r.tail := by
  cases h with
  | tail k =>
    cases k with
    | zero => exact ⟨rfl,RG.tail 0⟩
    | succ k => exact ⟨rfl,RG.tail k⟩
  | gap k hk hm r hr =>
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    exact ⟨rfl,RG.gap j (by omega) (by omega) r hr⟩

theorem rightFromGood {r} (h : RG r) : RI (false::r) := by
  cases h with
  | tail k => exact RI.tail (k+1)
  | gap k hk hm r hr => exact RI.gap (k+1) (by omega) (by omega) r hr

-- Complementary modulo-three run grammars, invariant at every A return.
inductive Inv : Z0 → Prop
  | a0 (l r : List Bool) (hl : LG l) (hr : RG r) : Inv ⟨0,false::l,r⟩
  | a1 (l r : List Bool) (hl : LG l) (hr : RG r) : Inv ⟨0,true::false::true::l,true::r⟩

theorem a0_case1 (l r : List Bool) : run0 table 5 ⟨0,false::l,false::true::r⟩ = some ⟨0,r.headD false::true::true::true::l,r.tail⟩ := by rfl

theorem a0_case2 (l r : List Bool) : run0 table 4 ⟨0,false::l,false::false::true::r⟩ = some ⟨0,r.headD false::false::false::true::true::l,r.tail⟩ := by rfl

theorem a0_case3 (l r : List Bool) : run0 table 6 ⟨0,false::l,false::false::false::r⟩ = some ⟨0,true::false::true::l,true::r⟩ := by rfl

theorem a0_zeros (l : List Bool) (n : Nat) : run0 table 6 ⟨0,false::l,Z n⟩ = some ⟨0,true::false::true::l,true::Z (n-3)⟩ := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => exact a0_case3 l (Z n)

theorem a1_init (l r : List Bool) : run0 table 7 ⟨0,true::false::true::l,true::r⟩ = some ⟨4,l,false::false::true::false::r⟩ := by rfl

theorem Fblock (L R : List Bool) : run0 table 1 ⟨4,[true]++L,R⟩ = some ⟨4,L,[false]++R⟩ := by rfl

theorem a1_epoch (k : Nat) (l r : List Bool) :
    run0 table (7+k) ⟨0,true::false::true::(O k ++ l),true::r⟩ = some ⟨4,l,Z k ++ false::false::true::false::r⟩ := by
  have h1 := a1_init (O k ++ l) r
  have h2 := sweepL table 4 [] [] [true] [false] 1 Fblock k l (false::false::true::false::r)
  simp only [List.nil_append,Nat.one_mul] at h2
  exact join0 h1 h2

theorem zeroShift (k : Nat) (r : List Bool) : Z k ++ false::false::r = Z (k+2) ++ r := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (List.cons false) ih

theorem a1_finish (k : Nat) (l r : List Bool) : run0 table 1 ⟨4,false::l,Z k ++ false::false::true::false::r⟩ = some ⟨0,false::true::l,Z (k+1) ++ true::false::r⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    change some (⟨0,false::true::l,Z k ++ false::false::true::false::r⟩ : Z0) = some (⟨0,false::true::l,Z (k+2) ++ true::false::r⟩ : Z0)
    rw [zeroShift]

theorem a1_finish_empty (k : Nat) (r : List Bool) : run0 table 1 ⟨4,[],Z k ++ false::false::true::false::r⟩ = some ⟨0,false::true::[],Z (k+1) ++ true::false::r⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
    change some (⟨0,[false,true],Z k ++ false::false::true::false::r⟩ : Z0) = some (⟨0,[false,true],Z (k+2) ++ true::false::r⟩ : Z0)
    rw [zeroShift]

theorem advance {c : Z0} (h : Inv c) : ∃ n d, 0<n ∧ run0 table n c = some d ∧ Inv d := by
  cases h with
  | a0 l r hl hr =>
    cases hr with
    | tail k => exact ⟨6,_,by decide,a0_zeros l k,Inv.a1 l (Z (k-3)) hl (RG.tail _)⟩
    | gap k hk hm r hr =>
      by_cases h1 : k=1
      · subst k
        obtain ⟨hh,ht⟩ := rightInnerPop hr
        refine ⟨5,_,by decide,a0_case1 l r,?_⟩
        rw [hh]
        exact Inv.a0 _ _ (leftPush3 hl) ht
      by_cases h2 : k=2
      · subst k
        obtain ⟨hh,ht⟩ := rightInnerPop hr
        refine ⟨4,_,by decide,a0_case2 l r,?_⟩
        rw [hh]
        exact Inv.a0 _ _ (leftPush2 hl) ht
      have h4 : 4≤k := by omega
      obtain ⟨j,rfl⟩ : ∃ j, k=j+3 := ⟨k-3,by omega⟩
      exact ⟨6,_,by decide,a0_case3 l (Z j++true::r),Inv.a1 l _ hl (RG.gap j (by omega) (by omega) r hr)⟩
  | a1 l r hl hr =>
    cases hl with
    | tail k hk =>
      have h1 := a1_epoch k [] r
      simp only [List.append_nil] at h1
      have h2 := a1_finish_empty k r
      exact ⟨7+k+1,_,by omega,join0 h1 h2,Inv.a0 _ _ (LG.tail 1 (by decide)) (RG.gap (k+1) (by omega) (by omega) _ (rightFromGood hr))⟩
    | gap k hk l hl =>
      have h1 := a1_epoch k (false::l) r
      have h2 := a1_finish k l r
      exact ⟨7+k+1,_,by omega,join0 h1 h2,Inv.a0 _ _ (leftPop hl) (RG.gap (k+1) (by omega) (by omega) _ (rightFromGood hr))⟩

theorem entry : run0 table 6 ⟨0,[],[]⟩ = some ⟨0,[true,false,true],[true]⟩ := by rfl

theorem initial : Inv ⟨0,[true,false,true],[true]⟩ := Inv.a1 [] [] (LG.tail 0 (by decide)) (RG.tail 0)

theorem unbounded : ∀ k, ∃ t c, k≤t ∧ run0 table t ⟨0,[],[]⟩ = some c ∧ Inv c := by
  intro k
  induction k with
  | zero => exact ⟨6,_,by decide,entry,initial⟩
  | succ k ih =>
    obtain ⟨t,c,ht,hc,hi⟩ := ih
    obtain ⟨n,d,hn,hd,hdi⟩ := advance hi
    exact ⟨t+n,d,by omega,join0 hc hd,hdi⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,c,ht,hr,_⟩ := unbounded n
  have hz : (zrun table t start).map project = some c :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms advance
#print axioms unbounded
#print axioms never
end BB6.Agent11Raw39Hard194
