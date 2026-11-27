import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Pair143
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def U (n : Nat) := rep [true] n
def V (n : Nat) := rep [true,true] n
def Z (n : Nat) := rep [false,true] n
def B (n : Nat) := rep [true,false,true,true,false] n
def C (n : Nat) := rep [false,true,true,false,true] n
def P (L : List Bool) (k m : Nat) : Z0 :=
  A L (Z k ++ [false,false] ++ U m)
def S (k m : Nat) := P [] k m

def Reach (p : PartialMachine) (s t : Z0) : Prop :=
  ∃ k, run0 p k s = some t
def PosReach (p : PartialMachine) (s t : Z0) : Prop :=
  ∃ k, 0 < k ∧ run0 p k s = some t
theorem Reach.trans {p s t u} (a : Reach p s t) (b : Reach p t u) : Reach p s u := by
  obtain ⟨n,hn⟩ := a
  obtain ⟨m,hm⟩ := b
  exact ⟨n+m,join0 hn hm⟩
theorem PosReach.trans {p s t u} (a : PosReach p s t) (b : Reach p t u) :
    PosReach p s u := by
  obtain ⟨n,hp,hn⟩ := a
  obtain ⟨m,hm⟩ := b
  exact ⟨n+m,by omega,join0 hn hm⟩

theorem Uadd (a b : Nat) : U (a+b) = U a ++ U b := by
  exact (Auto.rep_add _ _ _).symm
theorem Bsnoc (n : Nat) : B (n+1) = B n ++ [true,false,true,true,false] := by
  simpa [B,rep] using (rep_snoc [true,false,true,true,false] n).symm
theorem Csnoc (n : Nat) : C (n+1) = C n ++ [false,true,true,false,true] := by
  simpa [C,rep] using (rep_snoc [false,true,true,false,true] n).symm
theorem rotate (j : Nat) (X : List Bool) :
    true :: (C j ++ X) = B j ++ true :: X := by
  induction j with
  | zero => rfl
  | succ j ih => simp [B,C,rep,List.append_assoc] at ih ⊢
                 exact ih

structure LeftRules (p : PartialMachine) where
  pop10 : ∀ X Y, Reach p (A (true::false::X) Y) (A X (false::true::Y))
  pop1 : ∀ Y, Reach p (A [true] Y) (A [] (false::true::Y))
  pop11 : ∀ n X Y, Reach p (A (true::true::X) (Z n ++ [false,false] ++ Y))
    (A (true::X) (Z n ++ [false,false,true] ++ Y))
  init : ∀ n Y, PosReach p (A [] (Z n ++ [false,false] ++ Y))
    (A (true::true::V n) (false::Y))

inductive Code : List Bool → Nat → Nat → Prop
  | nil : Code [] 0 0
  | last : Code [true] 1 0
  | pop {X a b} : Code X a b → Code (true::false::X) (a+1) b
  | dup {X a b} : Code (true::X) a b → Code (true::true::X) a (b+1)

theorem leftScan {p : PartialMachine} (h : LeftRules p)
    {L a b} (c : Code L a b) (k m : Nat) :
    Reach p (P L k m) (S (k+a) (m+b)) := by
  induction c generalizing k m with
  | nil => exact ⟨0,rfl⟩
  | last =>
    simpa [P,S,Z,rep,List.append_assoc] using h.pop1 (Z k ++ [false,false] ++ U m)
  | @pop X a b c ih =>
    have hs : Reach p (P (true::false::X) k m) (P X (k+1) m) := by
      simpa [P,Z,rep,List.append_assoc] using h.pop10 X (Z k ++ [false,false] ++ U m)
    have ht := ih (k+1) m
    have he : k+1+a = k+(a+1) := by omega
    rw [he] at ht
    exact hs.trans ht
  | @dup X a b c ih =>
    have hs : Reach p (P (true::true::X) k m) (P (true::X) k (m+1)) := by
      simpa [P,U,rep,List.append_assoc] using h.pop11 k X (U m)
    have ht := ih k (m+1)
    have he : m+1+b = m+(b+1) := by omega
    rw [he] at ht
    exact hs.trans ht

theorem codeUnary (k : Nat) : Code (true::V k) 1 (2*k) := by
  induction k with
  | zero => exact .last
  | succ k ih =>
    have h := Code.dup (Code.dup ih)
    have he : 2*k+1+1 = 2*(k+1) := by omega
    rw [he] at h
    exact h

theorem codeBlock {X a b} (h : Code X a b) :
    Code ([true,false,true,true,false] ++ X) (a+2) (b+1) := by
  exact .pop (.dup (.pop h))

theorem codeBlocks (j k : Nat) :
    Code (B j ++ true::V k) (2*j+1) (j+2*k) := by
  induction j with
  | zero => simpa [B,rep] using codeUnary k
  | succ j ih =>
    have h := codeBlock ih
    have ha : 2*j+1+2 = 2*(j+1)+1 := by omega
    have hb : j+2*k+1 = (j+1)+2*k := by omega
    rw [hb,ha] at h
    exact h

def EndWord (j k : Nat) := [true,true,true,false] ++ B j ++ true::V k
theorem codeEnd (j k : Nat) :
    Code (EndWord j k) (2*j+2) (j+2*k+2) := by
  exact .dup (.dup (.pop (codeBlocks j k)))

structure RightRules (p : PartialMachine) where
  right2 : ∀ k j, Reach p (A (true::true::V k) (false::U (5*j+2))) (P (EndWord j k) 0 1)
  right3 : ∀ k j, Reach p (A (true::true::V k) (false::U (5*j+3))) (P (EndWord j k) 0 1)

theorem section2 {p} (L : LeftRules p) (R : RightRules p) (k j : Nat) :
    PosReach p (S k (5*j+2)) (S (2*j+2) (3+j+2*k)) := by
  have a := L.init k (U (5*j+2))
  have b := R.right2 k j
  have c := leftScan L (codeEnd j k) 0 1
  have he : 1+(j+2*k+2) = 3+j+2*k := by omega
  rw [he] at c
  simp only [Nat.zero_add] at c
  exact (a.trans b).trans c

theorem section3 {p} (L : LeftRules p) (R : RightRules p) (k j : Nat) :
    PosReach p (S k (5*j+3)) (S (2*j+2) (3+j+2*k)) := by
  have a := L.init k (U (5*j+3))
  have b := R.right3 k j
  have c := leftScan L (codeEnd j k) 0 1
  have he : 1+(j+2*k+2) = 3+j+2*k := by omega
  rw [he] at c
  simp only [Nat.zero_add] at c
  exact (a.trans b).trans c

def E (n : Nat) := S (2*n) (5*n+2)
def O (n : Nat) := S (2*n+2) (5*n+3)
def region (s : Z0) : Prop := (∃ n, s = E n) ∨ (∃ n, s = O n)

theorem E_to_O {p} (L : LeftRules p) (R : RightRules p) (n : Nat) :
    PosReach p (E n) (O n) := by
  have h := section2 L R (2*n) n
  have he : 3+n+2*(2*n) = 5*n+3 := by omega
  rw [he] at h
  exact h

theorem O_to_E {p} (L : LeftRules p) (R : RightRules p) (n : Nat) :
    PosReach p (O n) (E (n+1)) := by
  have h := section3 L R (2*n+2) n
  have ha : 2*n+2 = 2*(n+1) := by omega
  have hb : 3+n+2*(2*(n+1)) = 5*(n+1)+2 := by omega
  rw [ha,hb] at h
  exact h

theorem never {p} (L : LeftRules p) (R : RightRules p)
    (entry : run0 p 70 ⟨0,[],[]⟩ = some (O 0)) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  apply Multi.never_of_region p region 70 (O 0) entry (Or.inr ⟨0,rfl⟩) _ m hm
  intro s hs
  rcases hs with ⟨n,rfl⟩ | ⟨n,rfl⟩
  · obtain ⟨k,hk,hr⟩ := E_to_O L R n
    exact ⟨k,O n,hk,Or.inr ⟨n,rfl⟩,hr⟩
  · obtain ⟨k,hk,hr⟩ := O_to_E L R n
    exact ⟨k,E (n+1),hk,Or.inl ⟨n+1,rfl⟩,hr⟩
#print axioms never
end BB6Coverage.Agent31Pump.Pair143
