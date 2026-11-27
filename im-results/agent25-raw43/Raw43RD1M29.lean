import Raw43RD1Growth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RD1M29
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent25Raw43RD1Growth (rep_add)

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def Z : List Bool := [false,false]
def encode : List Bool → List Bool
  | [] => []
  | b::bs => [false,b]++encode bs
def inc : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::inc bs
def sect (bs : List Bool) : Z0 :=
  ⟨5,[true],[false,false,false]++encode bs⟩
def stage (n : Nat) (bs : List Bool) : Z0 :=
  ⟨4,[true]++rep Z n++[false,false,true],encode bs⟩
def target (n : Nat) (bs : List Bool) : Z0 :=
  ⟨5,[true],[false,false,false]++rep Z n++encode (inc bs)⟩

private theorem entryStage (R : List Bool) :
    run0 table 7 ⟨5,[true],[false,false,false]++R⟩ =
    some ⟨4,[true,false,false,true],R⟩ := by rfl
private theorem carryOne (L R : List Bool) :
    run0 table 4 ⟨4,[true]++L,[false,true]++R⟩ =
      some ⟨4,[true]++Z++L,R⟩ := by rfl
private theorem carryZero (L R : List Bool) :
    run0 table 5 ⟨4,[true]++L,Z++R⟩ =
      some ⟨5,Z++L,[true]++R⟩ := by rfl
private theorem carryBlank (L : List Bool) :
    run0 table 5 ⟨4,[true]++L,[]⟩ =
      some ⟨5,Z++L,[true]⟩ := by rfl
private theorem returnOne (L R : List Bool) :
    run0 table 2 ⟨5,[]++Z++L,[]++R⟩ =
      some ⟨5,[]++L,[]++Z++R⟩ := by rfl

private theorem returnZeros (n : Nat) (R : List Bool) :
    run0 table (2*(n+2)) ⟨5,Z++rep Z n++[false,false,true],[true]++R⟩ =
      some ⟨5,[true],[false,false,false]++rep Z n++[false,true]++R⟩ := by
  have he : rep Z (n+2) = Z++rep Z n++Z := by
    change Z++rep Z (n+1) = Z++rep Z n++Z
    rw [show rep Z (n+1)=rep Z n++Z from (rep_snoc Z n).symm]
    simp only [List.append_assoc]
  have hr : rep Z (n+2)++([true]++R) =
      [false,false,false]++rep Z n++[false,true]++R := by
    rw [he]
    have hz := rotate false [false] n
    change [false]++rep Z n=rep Z n++[false] at hz
    have hh := congrArg (fun a => Z++a++[false,true]++R) hz
    simpa only [Z,List.append_assoc,List.cons_append,List.nil_append] using hh.symm
  have h := sweepL table 5 [] [] Z Z 2 returnOne (n+2) [true] ([true]++R)
  simp only [List.nil_append] at h
  rw [hr,he] at h
  simpa only [Z,List.append_assoc,List.cons_append,List.nil_append] using h

theorem carry (n : Nat) (bs : List Bool) :
    ∃ t, run0 table t (stage n bs) = some (target n bs) := by
  induction bs generalizing n with
  | nil =>
    have h1 : run0 table 5 (stage n []) =
        some ⟨5,Z++rep Z n++[false,false,true],[true]++([] : List Bool)⟩ := by
      simpa only [stage,encode,List.append_assoc,List.append_nil] using carryBlank (rep Z n++[false,false,true])
    have h := join0 h1 (returnZeros n [])
    exact ⟨_,by simpa only [target,inc,encode,List.append_nil,List.append_assoc] using h⟩
  | cons b bs ih =>
    cases b
    · have h1 : run0 table 5 (stage n (false::bs)) =
          some ⟨5,Z++rep Z n++[false,false,true],[true]++encode bs⟩ := by
        simpa only [stage,encode,Z,List.append_assoc] using carryZero (rep Z n++[false,false,true]) (encode bs)
      have h := join0 h1 (returnZeros n (encode bs))
      exact ⟨_,by simpa only [target,inc,encode,List.append_assoc] using h⟩
    · have h1 := carryOne (rep Z n++[false,false,true]) (encode bs)
      have h1' : run0 table 4 (stage n (true::bs)) = some (stage (n+1) bs) := by
        simpa only [stage,encode,rep,List.append_assoc] using h1
      obtain ⟨t,ht⟩ := ih (n+1)
      have he : target (n+1) bs = target n (true::bs) := by
        simp only [target,inc,encode]
        rw [show rep Z (n+1)=rep Z n++Z from (rep_snoc Z n).symm]
        simp only [Z,List.append_assoc]
      rw [he] at ht
      exact ⟨4+t,join0 h1' ht⟩

theorem epoch (bs : List Bool) :
    ∃ t, 0<t ∧ run0 table t (sect bs) = some (sect (inc bs)) := by
  have h1 : run0 table 7 (sect bs) = some (stage 0 bs) := entryStage (encode bs)
  obtain ⟨t,ht⟩ := carry 0 bs
  have h := join0 h1 ht
  exact ⟨7+t,by omega,by simpa only [target,sect,rep,List.append_assoc,List.nil_append] using h⟩

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => inc (orbit n)
def family (n : Nat) : Z0 := sect (orbit n)
noncomputable def cost (n : Nat) : Nat := Classical.choose (epoch (orbit n))
theorem entry : run0 table 16 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 16 cost entry
    (fun n => (Classical.choose_spec (epoch (orbit n))).1)
    (fun n => (Classical.choose_spec (epoch (orbit n))).2) m hm

#print axioms epoch
#print axioms never
end BB6.Agent25Raw43RD1M29
