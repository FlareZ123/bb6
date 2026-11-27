import OneLCNat
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
structure Fast where
  q : Nat
  l : Nat
  r : Nat
  deriving DecidableEq

def encodeFast (z:N0) : Fast := ⟨z.q.val,z.l,z.r⟩
def lookup (a : Nat) (q b : Nat) : Nat := (a >>> (5 * (2*q+b))) % 32
-- 24 is the undefined transition; the 24 ordinary moves use q*4+write*2+right.
def codeMove (v : Move) : Nat := 4*v.next.val+2*v.write.toNat+v.right.toNat
def tableCode (p:PartialMachine) (a:Nat) : Prop := ∀ (q : Fin 6) (b : Bool), lookup a q.val b.toNat = (((p (q,b)).bind id).map codeMove).getD 24

def moveF (v : Nat) (z : Fast) : Fast :=
  if v%2==1 then ⟨v/4,(z.r%2)+2*((v/2)%2)+4*(z.l/2),z.r/2⟩
  else ⟨v/4,z.l/2,((v/2)%2)+2*z.r⟩
def stepF (a:Nat) (z:Fast) : Option Fast :=
  let v:=lookup a z.q (z.l%2)
  if v==24 then none else some (moveF v z)
def runF (a:Nat) : Nat → Fast → Option Fast
  | 0,z => some z
  | n+1,z => match stepF a z with | none => none | some z' => runF a n z'

theorem codeMove_lt (mv:Move) : codeMove mv < 24 := by
  rcases mv with ⟨w,r,q⟩
  have h:=q.isLt
  cases w <;> cases r <;> simp [codeMove,Bool.toNat] <;> omega

theorem codeMove_q (mv:Move) : codeMove mv / 4 = mv.next.val := by
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r <;> simp [codeMove,Bool.toNat] <;> omega

theorem codeMove_w (mv:Move) : (codeMove mv / 2)%2 = mv.write.toNat := by
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r <;> simp [codeMove,Bool.toNat] <;> omega

theorem codeMove_r (mv:Move) : (codeMove mv)%2 = mv.right.toNat := by
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r <;> simp [codeMove,Bool.toNat] <;> omega

theorem head_nat (x:Nat) : (head x).toNat = x%2 := by
  unfold head
  have h:x%2<2 := Nat.mod_lt _ (by decide)
  by_cases he : x%2=1
  · simp [he]
  · have hz:x%2=0:=by omega
    simp [hz]

theorem moveF_encode (mv:Move) (z:N0) : moveF (codeMove mv) (encodeFast z) = encodeFast (moveN mv z) := by
  unfold moveF moveN
  rw [codeMove_q,codeMove_w,codeMove_r]
  simp only [encodeFast,push,head_nat]
  cases hd : mv.right <;> simp [hd,Bool.toNat] <;> omega

theorem stepF_encode (p:PartialMachine) (a:Nat) (ha:tableCode p a) (z:N0) : stepF a (encodeFast z) = (stepN p z).map encodeFast := by
  unfold stepF stepN
  have h := ha z.q (head z.l)
  rw [head_nat] at h
  change lookup a z.q.val (z.l%2) = _ at h
  simp only [encodeFast]
  simp only [h]
  cases hm : (p (z.q,head z.l)).bind id with
  | none => rfl
  | some mv =>
    have hn : ¬codeMove mv=24 := by have hlt:=codeMove_lt mv;omega
    simp only [Option.map,Option.getD,beq_iff_eq,hn,if_false]
    exact congrArg some (moveF_encode mv z)

theorem runF_encode (p:PartialMachine) (a:Nat) (ha:tableCode p a) (n:Nat) (z:N0) : runF a n (encodeFast z) = (runN p n z).map encodeFast := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change (match stepF a (encodeFast z) with | none=>none | some z' => runF a n z') = ((stepN p z).bind (runN p n)).map encodeFast
    rw [stepF_encode p a ha z]
    cases hs:stepN p z with
    | none=>rfl
    | some t=>exact ih t

theorem runF_join {a:Nat} {n k:Nat} {x y z:Fast} (h:runF a n x=some y) (g:runF a k y=some z) : runF a (n+k) x=some z := by
  induction n generalizing x with
  | zero => have h':x=y:=Option.some.inj h;subst x;simpa using g
  | succ n ih =>
    rw [runF] at h
    rw [Nat.succ_add,runF]
    cases hs:stepF a x with
    | none=>simp [hs] at h
    | some t=>exact ih (by simpa [hs] using h)

theorem read_of_runF {p:PartialMachine} {a n:Nat} {v:Fast} (ha:tableCode p a) (h:runF a n ⟨0,0,0⟩ = some v) :
  (knownRun p n).map readSlot = some (⟨v.q % 6,Nat.mod_lt _ (by decide)⟩,head v.l) := by
  have hh := (runF_encode p a ha n ⟨0,0,0⟩).symm.trans h
  cases hz : runN p n ⟨0,0,0⟩ with
  | none=>simp [hz] at hh
  | some z=>
    have he:encodeFast z=v:=by simpa [hz] using hh
    subst v
    rw [read_of_runN hz]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt z.q.isLt).symm
#print axioms read_of_runF
#print axioms runF_join
end BB6.Agent4E0OneLCLate
