import BlockPump
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF1LE1393
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨false,true,0⟩),some (some ⟨true,true,2⟩),none,some (some ⟨false,true,3⟩),some (some ⟨false,false,3⟩),some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),some (some ⟨true,true,0⟩),some (some ⟨true,false,5⟩),some (some ⟨true,false,4⟩),some (some ⟨false,false,5⟩)] : List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none
private def pairs : List Bool → List Bool
  | [] => []
  | b::bs => b::b::pairs bs
private inductive L : List Bool → Prop where
  | nil : L []
  | z {l} : L l → L (false::false::l)
  | m {l} : L l → L (false::true::l)
  | o {l} : L l → L (true::true::l)
private def sec (l : List Bool) (x : List Bool) : HZ := ⟨5,l,pairs x⟩
private def a1 (l x : List Bool) : HZ := ⟨0,true::l,pairs x⟩
private def a0 (l x : List Bool) : HZ := ⟨0,false::false::l,false::pairs x⟩
private theorem skip (l x : List Bool) : hrun table 2 (a1 l (true::x)) = some (a1 (false::false::l) x) := by rfl
private theorem a1zero (l x : List Bool) : hrun table 1 (a1 l (false::x)) = some (a0 l x) := by rfl
private theorem a0one (l x : List Bool) : hrun table 5 (a0 l (true::x)) = some (a1 (true::true::true::false::l) x) := by rfl
private theorem a0zero (l x : List Bool) : hrun table 7 (a0 l (false::x)) = some (sec (true::true::false::l) (true::x)) := by rfl
private theorem a0nil (l : List Bool) : hrun table 7 (a0 l []) = some (sec (true::true::false::l) [true]) := by rfl
private theorem a1nil (l : List Bool) : hrun table 8 (a1 l []) = some (sec (true::true::false::l) [true]) := by rfl
private theorem scan (x l : List Bool) (hl : L (false::l)) : ∃ t l' y, 0<t ∧ L l' ∧ hrun table t (a1 l x) = some (sec l' y) := by
  cases x with
  | nil => exact ⟨8,_,_,by decide,.o hl,a1nil l⟩
  | cons b x =>
    cases b with
    | true =>
      obtain ⟨t,l',y,ht,hL,hr⟩ := scan x (false::false::l) (.z hl)
      exact ⟨2+t,l',y,by omega,hL,hjoin (skip l x) hr⟩
    | false =>
      cases x with
      | nil => exact ⟨8,_,_,by decide,.o hl,hjoin (a1zero l []) (a0nil l)⟩
      | cons b x =>
        cases b with
        | false => exact ⟨8,_,_,by decide,.o hl,hjoin (a1zero l (false::x)) (a0zero l x)⟩
        | true =>
          obtain ⟨t,l',y,ht,hL,hr⟩ := scan x (true::true::true::false::l) (.m (.o hl))
          exact ⟨1+5+t,l',y,by omega,hL,hjoin (hjoin (a1zero l (true::x)) (a0one l x)) hr⟩
termination_by x.length
private theorem enter (l x : List Bool) : hrun table 2 (sec (false::false::l) x) = some (a1 (true::l) x) := by rfl
private theorem enterNil (x : List Bool) : hrun table 2 (sec [] x) = some (a1 [true] x) := by rfl
private theorem pop11 (l x : List Bool) : hrun table 2 (sec (true::true::l) x) = some (sec l (false::x)) := by rfl
private theorem pop01 (l x : List Bool) : hrun table 2 (sec (false::true::l) x) = some (sec l (true::x)) := by rfl
private theorem next {l} (hl : L l) (x : List Bool) : ∃ t l' y, 0<t ∧ L l' ∧ hrun table t (sec l x) = some (sec l' y) := by
  cases hl with
  | nil =>
    obtain ⟨t,l',y,ht,hL,hr⟩ := scan x [true] (.m .nil)
    exact ⟨2+t,l',y,by omega,hL,hjoin (enterNil x) hr⟩
  | @z l hl =>
    obtain ⟨t,l',y,ht,hL,hr⟩ := scan x (true::l) (.m hl)
    exact ⟨2+t,l',y,by omega,hL,hjoin (enter l x) hr⟩
  | @m l hl => exact ⟨2,l,true::x,by decide,hl,pop01 l x⟩
  | @o l hl => exact ⟨2,l,false::x,by decide,hl,pop11 l x⟩
private theorem root : hrun table 9 ⟨0,[],[]⟩ = some (sec [] [false,true]) := by rfl
private theorem arbitraryLive (n : Nat) : ∃ t l x, n≤t ∧ L l ∧ hrun table t ⟨0,[],[]⟩ = some (sec l x) := by
  induction n with
  | zero => exact ⟨9,[],[false,true],by decide,.nil,root⟩
  | succ n ih =>
    obtain ⟨t,l,x,ht,hl,hr⟩ := ih
    obtain ⟨s,l',y,hs,hL,hh⟩ := next hl x
    exact ⟨t+s,l',y,by omega,hL,hjoin hr hh⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,l,x,hk,hl,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
end BB6.Agent2Raw124ZeroLF1LE1393
