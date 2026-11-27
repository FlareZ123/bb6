import Agent5Pair143

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Region143
open BB6Coverage Agent31Pump Pair143 BB6.Agent13BlankDelay

theorem unaryBlock (a j : Nat) : rep (U a) j = U (a*j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, Nat.add_comm (a*j) a, Uadd]
    simp only [rep,ih]

theorem five (j : Nat) : rep [true,true,true,true,true] j = U (5*j) :=
  unaryBlock 5 j
theorem three (j : Nat) : rep [true,true,true] j = U (3*j) :=
  unaryBlock 3 j

def Iblock (h : Nat) := rep [true,true,true,true,false] h
def IIIblock (h : Nat) := rep [true,true,false] h

theorem codeI (h k : Nat) : Code (Iblock h ++ true::V k) (h+1) (3*h+2*k) := by
  induction h with
  | zero => simpa [Iblock,rep] using codeUnary k
  | succ h ih =>
    have q := Code.dup (Code.dup (Code.dup (Code.pop ih)))
    have hb : 3*h+2*k+1+1+1=3*(h+1)+2*k := by omega
    rw [hb] at q
    simpa [Iblock,rep,List.append_assoc] using q

theorem codeI3 (h k : Nat) :
    Code ([true,true,true,false] ++ Iblock h ++ true::V k) (h+2) (3*h+2*k+2) := by
  have q := Code.dup (Code.dup (Code.pop (codeI h k)))
  have ha : h+1+1=h+2 := by omega
  have hb : 3*h+2*k+1+1=3*h+2*k+2 := by omega
  rw [ha,hb] at q
  simpa [List.append_assoc] using q

theorem codeIII (h k : Nat) : Code (IIIblock h ++ true::V k) (h+1) (h+2*k) := by
  induction h with
  | zero => simpa [IIIblock,rep] using codeUnary k
  | succ h ih =>
    have q := Code.dup (Code.pop ih)
    have hb : h+2*k+1=(h+1)+2*k := by omega
    rw [hb] at q
    simpa [IIIblock,rep,List.append_assoc] using q

theorem codeIII1 (h k : Nat) :
    Code ([true,false] ++ IIIblock h ++ true::V k) (h+2) (h+2*k) := by
  have q := Code.pop (codeIII h k)
  simpa using q

theorem IIIturnWord (j : Nat) (X : List Bool) :
    [true,false,true,true,false,true] ++ rep [true,false,true] j ++ X =
    [true,false] ++ IIIblock (j+1) ++ true::X := by
  have q := Agent31Pump.rotate true [true,false] j
  simp only [List.cons_append,List.nil_append] at q
  simp only [IIIblock,rep,List.append_assoc,List.cons_append,List.nil_append]
  exact congrArg (fun w : List Bool => [true,false,true,true,false] ++ w ++ X) q

structure RightI (p : PartialMachine) where
  right0 : ∀ k j, Reach p (A (true::true::V k) (false::U (5*(j+1))))
    (P (Iblock (j+1) ++ true::V k) 0 1)
  right3 : ∀ k j, Reach p (A (true::true::V k) (false::U (5*j+3)))
    (P ([true,true,true,false] ++ Iblock j ++ true::V k) 0 1)

structure RightIII (p : PartialMachine) where
  right0 : ∀ k j, Reach p (A (true::true::V k) (false::U (3*(j+1))))
    (P (IIIblock (j+1) ++ true::V k) 0 1)
  right1 : ∀ k j, Reach p (A (true::true::V k) (false::U (3*(j+1)+1)))
    (P ([true,false] ++ IIIblock (j+1) ++ true::V k) 0 1)

theorem I0 {p} (L : LeftRules p) (R : RightI p) (k j : Nat) :
    PosReach p (S k (5*(j+1))) (S (j+2) (1+3*(j+1)+2*k)) := by
  have a := L.init k (U (5*(j+1)))
  have b := R.right0 k j
  have c := leftScan L (codeI (j+1) k) 0 1
  simp only [Nat.zero_add] at c
  have he : 1+(3*(j+1)+2*k)=1+3*(j+1)+2*k := by omega
  rw [he] at c
  exact (a.trans b).trans c

theorem I3 {p} (L : LeftRules p) (R : RightI p) (k j : Nat) :
    PosReach p (S k (5*j+3)) (S (j+2) (3+3*j+2*k)) := by
  have a := L.init k (U (5*j+3))
  have b := R.right3 k j
  have c := leftScan L (codeI3 j k) 0 1
  simp only [Nat.zero_add] at c
  have he : 1+(3*j+2*k+2)=3+3*j+2*k := by omega
  rw [he] at c
  exact (a.trans b).trans c

theorem III0 {p} (L : LeftRules p) (R : RightIII p) (k j : Nat) :
    PosReach p (S k (3*(j+1))) (S (j+2) (j+1+2*k+1)) := by
  have a := L.init k (U (3*(j+1)))
  have b := R.right0 k j
  have c := leftScan L (codeIII (j+1) k) 0 1
  simp only [Nat.zero_add] at c
  have he : 1+(j+1+2*k)=j+1+2*k+1 := by omega
  rw [he] at c
  exact (a.trans b).trans c

theorem III1 {p} (L : LeftRules p) (R : RightIII p) (k j : Nat) :
    PosReach p (S k (3*(j+1)+1)) (S (j+3) (j+1+2*k+1)) := by
  have a := L.init k (U (3*(j+1)+1))
  have b := R.right1 k j
  have c := leftScan L (codeIII1 (j+1) k) 0 1
  simp only [Nat.zero_add] at c
  have he : 1+(j+1+2*k)=j+1+2*k+1 := by omega
  rw [he] at c
  exact (a.trans b).trans c

def EI (j : Nat) := S (j+2) (5*(j+1))
def OI (j : Nat) := S (j+2) (5*(j+1)+3)
def regionI (s : Z0) := (∃ j, s=EI j) ∨ (∃ j, s=OI j)

theorem neverI {p} (L : LeftRules p) (R : RightI p) (entry : Nat)
    (seed : run0 p entry ⟨0,[],[]⟩ = some (EI 1)) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  apply Multi.never_of_region p regionI entry (EI 1) seed (Or.inl ⟨1,rfl⟩) _ m hm
  intro s hs
  rcases hs with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · have q := I0 L R (j+2) j
    rw [show 1+3*(j+1)+2*(j+2)=5*(j+1)+3 by omega] at q
    obtain ⟨k,hk,hr⟩ := q
    exact ⟨k,OI j,hk,Or.inr ⟨j,rfl⟩,hr⟩
  · have q := I3 L R (j+2) (j+1)
    rw [show 3+3*(j+1)+2*(j+2)=5*(j+1+1) by omega] at q
    obtain ⟨k,hk,hr⟩ := q
    exact ⟨k,EI (j+1),hk,Or.inl ⟨j+1,rfl⟩,hr⟩

def EIII (j : Nat) := S (j+1) (3*(j+1))
def OIII (j : Nat) := S (j+2) (3*(j+1)+1)
def PIII (j : Nat) := S (j+3) (3*(j+2))
def regionIII (s : Z0) := (∃ j, s=EIII j) ∨ (∃ j, s=OIII j) ∨ (∃ j, s=PIII j)

theorem neverIII {p} (L : LeftRules p) (R : RightIII p) (entry : Nat)
    (seed : run0 p entry ⟨0,[],[]⟩ = some (EIII 1)) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  apply Multi.never_of_region p regionIII entry (EIII 1) seed (Or.inl ⟨1,rfl⟩) _ m hm
  intro s hs
  rcases hs with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
  · have q := III0 L R (j+1) j
    rw [show j+1+2*(j+1)+1=3*(j+1)+1 by omega] at q
    obtain ⟨k,hk,hr⟩ := q
    exact ⟨k,OIII j,hk,Or.inr (Or.inl ⟨j,rfl⟩),hr⟩
  · have q := III1 L R (j+2) j
    rw [show j+1+2*(j+2)+1=3*(j+2) by omega] at q
    obtain ⟨k,hk,hr⟩ := q
    exact ⟨k,PIII j,hk,Or.inr (Or.inr ⟨j,rfl⟩),hr⟩
  · have q := III0 L R (j+3) (j+1)
    rw [show j+1+1+2*(j+3)+1=3*(j+2+1) by omega] at q
    obtain ⟨k,hk,hr⟩ := q
    exact ⟨k,EIII (j+2),hk,Or.inl ⟨j+2,rfl⟩,hr⟩

#print axioms neverI
#print axioms neverIII
end BB6Coverage.Agent31Pump.Region143
