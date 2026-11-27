import Raw13BinarySiblings

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13EvenPairSweep
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (rep_add)

inductive Variant where | b1 | f1
  deriving DecidableEq

def p : Variant → PartialMachine
  | .b1 => FAR.fromCodes [7,14,11,10,2,19,22,0,6,13,9,24]
  | .f1 => FAR.fromCodes [7,14,11,24,2,19,22,0,22,13,9,10]

def W : List Bool := [true,true]
def LP : List Bool := [false,true]
def RP : List Bool := [true,false]
def frame : List Bool := [false,true,true,true]
def three : List Bool := [true,true,true]
def four : List Bool := [true,true,true,true]

def E (m j : Nat) : Z0 := ⟨4,rep W (m+2)++rep RP j,[]⟩

theorem prefix (v : Variant) (L : List Bool) :
    run0 (p v) 7 ⟨4,true::L,[]⟩ = some ⟨0,L,three⟩ := by cases v <;> rfl

theorem pairL (v : Variant) (L R : List Bool) :
    run0 (p v) 2 ⟨0,[]++W++L,[]++R⟩ =
      some ⟨0,[]++L,[]++LP++R⟩ := by cases v <;> rfl

theorem drain (v : Variant) (k : Nat) (L R : List Bool) :
    run0 (p v) (2*k) ⟨0,rep W k++L,R⟩ =
      some ⟨0,L,rep LP k++R⟩ := by
  simpa only [List.nil_append] using sweepL (p v) 0 [] [] W LP 2 (pairL v) k L R

theorem rotateW (k : Nat) : true::rep W k = rep W k++[true] :=
  rotate true [true] k

theorem start (v : Variant) (m j : Nat) :
    run0 (p v) 7 (E m j) =
      some ⟨0,rep W (m+1)++true::rep RP j,three⟩ := by
  have h := prefix v (true::(rep W (m+1)++rep RP j))
  change run0 (p v) 7 (E m j) = _ at h
  have he : true::(rep W (m+1)++rep RP j) =
      rep W (m+1)++true::rep RP j := by
    simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using
      congrArg (fun x => x++rep RP j) (rotateW (m+1))
  rw [he] at h
  exact h

theorem turn (v : Variant) (R : List Bool) :
    run0 (p v) 4 ⟨0,[true],R⟩ = some ⟨4,[true,true,false],R⟩ := by
  cases v <;> rfl

theorem pairR0 (v : Variant) (L R : List Bool) :
    run0 (p v) 4 ⟨4,[true]++L,[]++LP++R⟩ =
      some ⟨4,[true]++RP++L,[]++R⟩ := by cases v <;> rfl

theorem end3 (v : Variant) (L : List Bool) :
    run0 (p v) 5 ⟨4,true::L,three⟩ =
      some ⟨4,four++L,[]⟩ := by cases v <;> rfl

theorem reset (v : Variant) (m : Nat) :
    ∃ c, 0<c ∧ run0 (p v) c (E m 0) = some (E 0 (m+2)) := by
  have h1 := start v m 0
  have h1' : run0 (p v) 7 (E m 0) = some ⟨0,rep W (m+1)++[true],three⟩ := by
    simpa only [rep] using h1
  have h2 := drain v (m+1) [true] three
  have h3 := turn v (rep LP (m+1)++three)
  have h4 := sweepR (p v) 4 [true] [] LP RP 4 (pairR0 v) (m+1) RP three
  have h4' : run0 (p v) (4*(m+1)) ⟨4,[true,true,false],rep LP (m+1)++three⟩ =
      some ⟨4,true::rep RP (m+2),three⟩ := by
    have hr : rep RP (m+1)++RP = rep RP (m+2) := rep_snoc RP (m+1)
    simpa only [RP,List.nil_append,List.singleton_append,List.cons_append,List.append_assoc,
      show rep RP (m+1)++[true,false]=rep RP (m+2) from hr] using h4
  have h5 := end3 v (rep RP (m+2))
  refine ⟨7+2*(m+1)+4+4*(m+1)+5,by omega,?_⟩
  exact join0 (join0 (join0 (join0 h1' h2) h3) h4') h5

theorem aStart (v : Variant) (L R : List Bool) :
    run0 (p v) 3 ⟨0,false::L,[false,true,false]++R⟩ =
      some ⟨4,frame++L,R⟩ := by cases v <;> rfl

theorem ePair (v : Variant) (L R : List Bool) :
    run0 (p v) 8 ⟨4,frame++L,[]++RP++R⟩ =
      some ⟨4,frame++W++L,[]++R⟩ := by cases v <;> rfl

theorem eSweep (v : Variant) (k : Nat) (L R : List Bool) :
    run0 (p v) (8*k) ⟨4,frame++L,rep RP k++R⟩ =
      some ⟨4,frame++rep W k++L,R⟩ := by
  simpa only [List.nil_append] using sweepR (p v) 4 frame [] RP W 8 (ePair v) k L R

theorem end4 (v : Variant) (L : List Bool) :
    run0 (p v) 21 ⟨4,frame++L,four⟩ =
      some ⟨0,rep W 4++true::L,[true]⟩ := by cases v <;> rfl

theorem end2 (v : Variant) (L : List Bool) :
    run0 (p v) 8 ⟨4,frame++L,W⟩ =
      some ⟨4,rep W 3++L,[]⟩ := by cases v <;> rfl

theorem alternatingTail (k : Nat) (R : List Bool) :
    rep LP (k+2)++R = [false,true,false]++rep RP k++true::R := by
  have h := congrArg (fun x => [false,true,false]++x++R) (rotate true [false] k)
  simpa only [LP,RP,rep,List.cons_append,List.nil_append,List.append_assoc] using h

theorem reduce (v : Variant) (m j : Nat) :
    ∃ c, 0<c ∧ run0 (p v) c (E m (j+2)) = some (E (m+4) j) := by
  let L := rep RP j
  have h1 := start v m (j+2)
  have h1' : run0 (p v) 7 (E m (j+2)) =
      some ⟨0,rep W (m+2)++[false,true,false]++L,three⟩ := by
    have he : rep W (m+1)++W = rep W (m+2) := rep_snoc W (m+1)
    simpa only [L,RP,rep,List.cons_append,List.nil_append,List.append_assoc] using h1
  have h2 := drain v (m+2) ([false,true,false]++L) three
  have h2' : run0 (p v) (2*(m+2)) ⟨0,rep W (m+2)++[false,true,false]++L,three⟩ =
      some ⟨0,[false,true,false]++L,rep LP (m+2)++three⟩ := by
    simpa only [List.append_assoc] using h2
  have h3 := aStart v ([true,false]++L) (rep RP m++four)
  have h3' : run0 (p v) 3 ⟨0,[false,true,false]++L,rep LP (m+2)++three⟩ =
      some ⟨4,frame++[true,false]++L,rep RP m++four⟩ := by
    simpa only [alternatingTail,three,four,List.cons_append,List.nil_append,List.append_assoc] using h3
  have h4 := eSweep v m ([true,false]++L) four
  have h4' : run0 (p v) (8*m) ⟨4,frame++[true,false]++L,rep RP m++four⟩ =
      some ⟨4,frame++(rep W m++[true,false]++L),four⟩ := by
    simpa only [List.append_assoc] using h4
  have h5 := end4 v (rep W m++[true,false]++L)
  have he : true::(rep W m++[true,false]++L) = rep W (m+1)++false::L := by
    have h := congrArg (fun x => x++true::false::L) (rotateW m)
    have hs : rep W m++W=rep W (m+1) := rep_snoc W m
    calc
      _ = rep W m++W++false::L := by
        simpa only [W,List.cons_append,List.nil_append,List.append_assoc] using h
      _ = _ := by rw [hs]
  rw [he] at h5
  have h5' : run0 (p v) 21 ⟨4,frame++(rep W m++[true,false]++L),four⟩ =
      some ⟨0,rep W (m+5)++false::L,[true]⟩ := by
    simpa only [← List.append_assoc,rep_add,show 4+(m+1)=m+5 by omega] using h5
  have h6 := drain v (m+5) (false::L) [true]
  have h7 := aStart v L (rep RP (m+3)++W)
  have h7' : run0 (p v) 3 ⟨0,false::L,rep LP (m+5)++[true]⟩ =
      some ⟨4,frame++L,rep RP (m+3)++W⟩ := by
    simpa only [show m+5=(m+3)+2 by omega,alternatingTail,W,
      List.cons_append,List.nil_append,List.append_assoc] using h7
  have h8 := eSweep v (m+3) L W
  have h9 := end2 v (rep W (m+3)++L)
  have h9' : run0 (p v) 8 ⟨4,frame++rep W (m+3)++L,W⟩ =
      some (E (m+4) j) := by
    simpa only [E,L,List.append_assoc,← List.append_assoc (rep W 3) (rep W (m+3)),
      rep_add,show 3+(m+3)=m+4+2 by omega] using h9
  refine ⟨7+2*(m+2)+3+8*m+21+2*(m+5)+3+8*(m+3)+8,by omega,?_⟩
  exact join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h1' h2') h3') h4') h5') h6) h7') h8) h9'

def Allowed (z : Z0) : Prop := ∃ m j, m%2=0 ∧ j%2=0 ∧ z=E m j

theorem progress (v : Variant) (z : Z0) (h : Allowed z) :
    ∃ c z', 0<c ∧ run0 (p v) c z = some z' ∧ Allowed z' := by
  obtain ⟨m,j,hm,hj,rfl⟩ := h
  by_cases h : j=0
  · subst j
    obtain ⟨c,hc,hr⟩ := reset v m
    exact ⟨c,E 0 (m+2),hc,hr,0,m+2,by decide,by omega,rfl⟩
  · let j' := j-2
    have he : j=j'+2 := by dsimp [j']; omega
    rw [he]
    obtain ⟨c,hc,hr⟩ := reduce v m j'
    exact ⟨c,E (m+4) j',hc,hr,m+4,j',by omega,by omega,rfl⟩

theorem first (v : Variant) : run0 (p v) 8 ⟨0,[],[]⟩ = some (E 0 0) := by
  cases v <;> decide

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m :=
  BB6.Agent46Raw13BinarySiblings.never_of_return (p v) Allowed 8 (E 0 0)
    (first v) ⟨0,0,by decide,by decide,rfl⟩ (progress v) m hm

#print axioms reset
#print axioms reduce
#print axioms never
end BB6.Agent46Raw13EvenPairSweep
