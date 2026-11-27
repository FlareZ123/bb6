import F421ZeroGuard

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open Regular (P Q Z R repAdd rotateP rotateQ)
open F421TertiaryGuard (drain QBudget)

def scell (c : TC) : List Bool := (if c.f then Z else [])++rep Q c.z++rep P c.r
def stail (xs : List TC) (U : List Bool) : List Bool := xs.flatMap scell++U
def sbody (a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool) : List Bool :=
  rep P a++rep Q b++pw false cs++rep P x++Z++rep P y++stail xs U

def sshiftCell (c : TC) : List Bool := Z++(if c.f then Z else [])++rep P (c.z-1)++R++rep Q (c.r-1)
def sshift (xs : List TC) : List Bool := xs.flatMap sshiftCell
def svalid (xs : List TC) : Prop := ∀ c∈xs, 1≤c.z ∧ 1≤c.r

theorem halfSec (c : TC) (hz : 1≤c.z) (hr : 1≤c.r) : [false]++scell c=sshiftCell c++[false] := by
  have hz' : rep Q c.z=Q++rep Q (c.z-1) := by
    change rep Q c.z=rep Q 1++rep Q (c.z-1)
    rw [←repAdd]; congr 1; omega
  have hr' : rep P c.r=P++rep P (c.r-1) := by
    change rep P c.r=rep P 1++rep P (c.r-1)
    rw [←repAdd]; congr 1; omega
  have hcore : [true]++rep Q (c.z-1)++P++rep P (c.r-1)=rep P (c.z-1)++R++rep Q (c.r-1)++[false] := by
    rw [rotateP]; simp only [List.append_assoc]
    have h : [true]++P=R++[false] := rfl
    rw [←List.append_assoc [true],h]; simp only [List.append_assoc]
    rw [rotateQ]
  unfold scell sshiftCell
  rw [hz',hr']
  cases hf : c.f
  · simp only [hf,Bool.false_eq_true,ite_false,List.nil_append,List.append_assoc]
    have h := congrArg (Z++·) hcore
    simp only [List.append_assoc] at h
    exact h
  · simp only [hf,ite_true,List.append_assoc]
    have h := congrArg (Z++Z++·) hcore
    simp only [List.append_assoc] at h
    exact h

theorem shiftSec (xs : List TC) (U : List Bool) (hv : svalid xs) : [false]++stail xs U=sshift xs++[false]++U := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have h := hv c (by simp)
    have hi := ih (fun z hz => hv z (by simp [hz]))
    have h₁ : stail (c::cs) U=scell c++stail cs U := by simp [stail,List.append_assoc]
    have h₂ : sshift (c::cs)=sshiftCell c++sshift cs := by simp [sshift]
    rw [h₁,h₂]
    rw [←List.append_assoc,halfSec c h.1 h.2,List.append_assoc,hi]; simp [List.append_assoc]

theorem sFirst (a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hb : 2≤b) (hx : 1≤x) (hv : valid cs) :
    reaches 1 (sbody a b x y cs xs U)
      (rep P (a+2)++rep Q (b+1)++pw true (dec cs)++rep P (x-1)++Q++rep P y++stail xs U) := by
  have h := carryNear a b x cs.reverse (rep P y++stail xs U) hb hx (validRev cs hv)
  rw [nearRev,decRev,nearRev] at h
  simpa only [sbody,List.append_assoc] using h

theorem sSecond (a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hb : 2≤b) (hx : 2≤x) (hy : 1≤y) (hv : valid cs) (hs : svalid xs) :
    reaches 1 (rep P a++rep Q b++pw false cs++rep P (x-1)++Q++rep P y++stail xs U)
      (P++rep Q (a+1)++pw true (crossFar b (x-1) cs)++P++rep Q (y-1)++sshift xs++[false]++U) := by
  have h := oddECross a b (x-1) cs ([false]++rep P (y-1)++stail xs U) hb (by omega) hv
  have hi : Q++rep P y++stail xs U=Regular.E++([false]++rep P (y-1)++stail xs U) := by
    rw [show y=1+(y-1) by omega,repAdd]; simp [P,Q,Regular.E,rep,List.append_assoc]
  have ho : [false]++rep P (y-1)++stail xs U=rep Q (y-1)++sshift xs++[false]++U := by
    rw [rotateQ,List.append_assoc,shiftSec xs U hs]; simp [List.append_assoc]
  simp only [List.append_assoc] at h hi ho ⊢
  rw [hi,ho]; rw [ho] at h; exact h

def sTouch (xs : List TC) : List TC := xs.map fun c => ⟨c.z,c.r-1,true⟩
def sTarget (c : TC) : TC := ⟨c.z+1,c.r,false⟩
def sSegs (xs : List TC) : List Regular.Seg := xs.map fun c => (c.z-2,c.r-1)

theorem sshiftAppend (xs ys : List TC) : sshift (xs++ys)=sshift xs++sshift ys := by simp [sshift]
theorem stailAppend (xs ys : List TC) (U : List Bool) : stail (xs++ys) U=stail xs (stail ys U) := by simp [stail,List.append_assoc]

theorem twistSec (xs : List TC) (hc : clear xs) (hz : ∀ c∈xs, 2≤c.z) :
    sshift xs++[false]=[false]++Regular.twistInputs (sSegs xs) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have h := hz c (by simp)
    have hcl := hc c (by simp)
    have hi := ih (fun z hz => hc z (by simp [hz])) (fun z h => hz z (by simp [h]))
    change (sshiftCell c++sshift cs)++[false]=[false]++(Regular.twistInputOne (c.z-2,c.r-1)++Regular.twistInputs (sSegs cs))
    rw [List.append_assoc,hi]
    simp [sshiftCell,hcl,Regular.twistInputOne,Z,show c.z-2+1=c.z-1 by omega,List.append_assoc]

theorem secOutputs (xs : List TC) (hz : ∀ c∈xs, 2≤c.z) :
    Regular.outputs (sSegs xs)=stail (sTouch xs) [] := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have h := hz c (by simp)
    have hi := ih (fun z hz' => hz z (by simp [hz']))
    simp only [sSegs,List.map_cons,Regular.outputs,List.flatMap_cons] at hi ⊢
    have he : stail (sTouch (c::cs)) []=scell ⟨c.z,c.r-1,true⟩++stail (sTouch cs) [] := by simp [stail,sTouch]
    rw [he]
    rw [hi]; simp [Regular.segOutput,scell,show c.z-2+2=c.z by omega]

theorem sThird (a b y : Nat) (cB : PC) (cs : List PC) (lo hi : List TC) (c : TC) (U : List Bool)
    (hb : 2≤b) (hy : 2≤y) (hv : valid (cB::cs)) (hlo : clear lo) (hz : ∀ t∈lo, 2≤t.z)
    (hc : c.f=true) (hcz : 1≤c.z) (hcr : 1≤c.r) (hhi : svalid hi) :
    reaches 1 (rep P a++rep Q b++pw false (cB::cs)++P++rep Q (y-1)++sshift (lo++c::hi)++[false]++U)
      (P++rep Q (a+1)++pw true (crossFar b cB.p cs)++rep P cB.q++Z++rep P (y-1)++stail (sTouch lo++sTarget c::hi) U) := by
  have h := oddDCross a b 1 (y-1) (cB::cs) (sSegs lo)
    ([false]++rep P (c.z-1)++R++rep Q (c.r-1)++[false]++stail hi U) hb (by omega) (by omega) hv
  have hin : sshift (lo++c::hi)++[false]++U = [false]++Regular.twistInputs (sSegs lo)++Z++([false]++rep P (c.z-1)++R++rep Q (c.r-1)++[false]++stail hi U) := by
    rw [sshiftAppend]
    change (sshift lo++(sshiftCell c++sshift hi))++[false]++U=_
    rw [show sshiftCell c= [false]++[false]++Z++rep P (c.z-1)++R++rep Q (c.r-1) by simp [sshiftCell,hc,Z,List.append_assoc]]
    have he := twistSec lo hlo hz
    have hf := shiftSec hi U hhi
    simp only [List.append_assoc] at he hf ⊢
    rw [←hf]
    rw [←List.append_assoc (sshift lo), he]; simp [List.append_assoc,Z]
  have hout : Q++([false]++rep P (c.z-1)++R++rep Q (c.r-1)++[false]++stail hi U) = scell (sTarget c)++stail hi U := by
    have hq : Q++rep Q (c.z-1)++Q=rep Q (c.z+1) := by
      change rep Q 1++rep Q (c.z-1)++rep Q 1=_
      rw [←repAdd,←repAdd]; congr 1; omega
    have hp : rep P (c.r-1)++P=rep P c.r := by change rep P (c.r-1)++rep P 1=_; rw [←repAdd]; congr 1; omega
    have hcore : Q++([false]++rep P (c.z-1)++R++rep Q (c.r-1)++[false])=rep Q (c.z+1)++rep P c.r := by
      rw [rotateQ]; simp only [List.append_assoc]
      have h : [false]++R=Q++[true] := rfl
      rw [←List.append_assoc [false],h]; simp only [List.append_assoc]
      rw [←List.append_assoc [true],rotateP]; simp only [List.append_assoc]
      rw [show [true]++[false]=P by rfl,hp]
      rw [←List.append_assoc (rep Q (c.z-1)),←List.append_assoc Q,←List.append_assoc Q,hq]
    have h := congrArg (·++stail hi U) hcore
    simpa [scell,sTarget,List.append_assoc] using h
  have hw : pw true (crossFar b 1 (cB::cs))=pw true (crossFar b cB.p cs)++rep P cB.q++Z := by
    rw [crossFarEq,crossDirect,wordCons,←crossFarEq]; simp [rep]
  rw [hw,secOutputs lo hz] at h
  simp only [List.append_assoc,rep,List.nil_append] at h hin hout ⊢
  rw [hin]
  -- Align the unchanged suffix after the twisted tail.
  have he : stail (sTouch lo++sTarget c::hi) U=stail (sTouch lo) []++scell (sTarget c)++stail hi U := by simp [stail, List.append_assoc]
  rw [he]
  rw [hout] at h
  simpa only [List.append_assoc] using h

#print axioms sFirst
#print axioms sSecond
#print axioms sThird
end BB6Coverage.Agent41F421.EpochWords
