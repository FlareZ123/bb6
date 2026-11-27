import F421Epoch

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open Regular (P Q Z R repAdd rotateP rotateQ)
open F421TertiaryGuard (drain QBudget Marked8 Survives8)

def secCells (xs : List TC) : List Bool := xs.flatMap fun c => Z++rep Q c.z++rep P (c.r+1)
def zeroSuffix (z r v : Nat) (V : List Bool) : List Bool := rep Q z++Z++rep P r++Z++rep P v++R++V

def secBody (a b x y z r v : Nat) (cs : List PC) (xs : List TC) (V : List Bool) : List Bool :=
  rep P a++rep Q b++pw false cs++rep P x++Z++rep P y++secCells xs++Z++rep Q z++rep P r++Q++rep P v++R++V

theorem crossNearAppend (b x : Nat) (ns ts : List PC) (c : PC) :
    crossNear b x (ns++c::ts)=crossNear b c.p ns++crossNear c.q x ts := by
  induction ns generalizing b with
  | nil => rfl
  | cons d ds ih => simp [crossNear,ih]

theorem nearCons (m : Bool) (c : PC) (cs : List PC) :
    near m (c::cs)=rep P c.p++(if m then Z else [])++rep Q c.q++near m cs := by
  simp [near,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.nearWord,GeneralDrain.rowWord,List.append_assoc]

theorem secCross (y z : Nat) (xs : List TC) :
    near true (crossNear y (z+1) (lowRegs xs))=rep P y++secCells xs++Z++rep Q z := by
  induction xs generalizing y with
  | nil => simp [lowRegs,crossNear,nearSingleton,secCells]
  | cons c cs ih =>
    change near true (⟨y,c.z+1-1⟩::crossNear (c.r+1) (z+1) (lowRegs cs))=_
    rw [nearCons,ih]
    simp [secCells,List.append_assoc]

theorem shiftZeroSuffix (z r v : Nat) (V : List Bool) :
    [true]++zeroSuffix z r v V = rep P (z+1)++rep Q r++[false]++Z++rep P v++R++V := by
  unfold zeroSuffix
  rw [← List.append_assoc [true],← List.append_assoc [true],← List.append_assoc [true],← List.append_assoc [true],← List.append_assoc [true],← List.append_assoc [true],rotateP]
  simp only [List.append_assoc]
  rw [← List.append_assoc [true]]
  have hZ : [true]++Z=P++[false] := rfl
  rw [hZ,repAdd]
  simp only [rep,List.append_assoc]
  rw [← List.append_assoc [false],rotateQ]
  simp [List.append_assoc]

/-- The zero tail is crossed in one odd-d return, before the final primary drain.
    Its extra far row has Q length zero and becomes the new tail separator. -/
theorem zeroSecondCross (a b y z r v : Nat) (c : PC) (cs : List PC) (xs : List TC) (V : List Bool)
    (hb : 2≤b) (hy : 2≤y) (hr : 1≤r) (hv : valid (c::cs)) (hxs : tailValid xs) (hcl : clear xs) :
    reaches 1
      (rep P a++rep Q b++pw false (c::cs)++P++rep Q y++shifted xs++[true]++zeroSuffix z r v V)
      (P++rep Q (a+1)++pw true (crossFar b c.p cs)++rep P c.q++Z++rep P y++secCells xs++Z++rep Q z++rep P r++Q++rep P v++R++V) := by
  let sep : PC := ⟨1,y⟩
  let ns := (c::cs).reverse++[sep]++lowRegs xs
  let fs := ns.reverse
  have hn : valid ns := by
    intro t ht
    simp only [ns,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with (ht|rfl)|ht
    · exact hv t (List.mem_reverse.mp ht)
    · exact ⟨Nat.le_refl _,hy⟩
    · exact lowRegsValid xs hxs t ht
  have h := oddDCross a b (z+1) r fs [] (rep P v++R++V) hb (by omega) hr (validRev ns hn)
  have hin : pw false fs=pw false (c::cs)++P++rep Q y++shifted xs := by
    rw [show pw false fs=near false ns by simp [fs,←nearRev]]
    unfold ns
    rw [nearAppend,nearAppend,nearRev,nearSingleton,←lowShift xs hcl]
    simp [sep,rep,List.append_assoc]
  have hout : pw true (crossFar b (z+1) fs)=pw true (crossFar b c.p cs)++rep P c.q++Z++rep P y++secCells xs++Z++rep Q z := by
    unfold crossFar
    simp only [fs,List.reverse_reverse]
    rw [←nearRev,List.reverse_reverse]
    unfold ns
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    change near true (crossNear b (z+1) (cs.reverse++c::sep::lowRegs xs))=_ 
    rw [crossNearAppend b (z+1) cs.reverse (sep::lowRegs xs) c,nearAppend]
    rw [show near true (crossNear b c.p cs.reverse)=pw true (crossFar b c.p cs) by rw [←nearRev]; simp only [crossFar,List.reverse_reverse]]
    rw [show crossNear c.q (z+1) (sep::lowRegs xs)=⟨c.q,0⟩::crossNear y (z+1) (lowRegs xs) by rfl,nearCons,secCross]
    simp [rep,List.append_assoc]; rfl
  rw [hin,hout] at h
  have he := shiftZeroSuffix z r v V
  simp only [Regular.twistInputs,Regular.outputs,List.flatMap_nil,List.nil_append,List.append_nil,List.append_assoc] at h he ⊢
  rw [he]
  exact h

theorem zeroCycleSource (a b x y z r v : Nat) (cs bs ds : List PC) (cA : PC)
    (xs : List TC) (V : List Bool) (A C rA rC : Nat)
    (ha : 1≤a) (hb : 2≤b) (hx : 1≤x) (hy : 2≤y) (hr : 1≤r) (hv : valid cs)
    (hxs : tailValid xs) (hcl : clear xs)
    (gA : guarded 0 (crossFar b x cs))
    (eA : drain 0 0 (crossFar b x cs)=(cA::bs,A,rA)) (vA : valid (cA::bs))
    (gC : guarded 0 (crossFar (a+1+A+rA) cA.p bs))
    (eC : drain 0 0 (crossFar (a+1+A+rA) cA.p bs)=(ds,C,rC)) :
    reaches (1+A+1+C) (body a b x y cs xs (zeroSuffix z r v V))
      (secBody (1+2*C) (1+2*A+1+C+rC) cA.q y z r v ds xs V) := by
  have h1 := firstCross a b x y cs xs (zeroSuffix z r v V) hb hx (by omega) hv
  have h2 := drainReach 1 (a+1) (crossFar b x cs) (cA::bs) A rA
    (P++rep Q y++shifted xs++[true]++zeroSuffix z r v V) (by omega) gA eA
  have h3 := zeroSecondCross (1+2*A) (a+1+A+rA) y z r v cA bs xs V (by omega) hy hr vA hxs hcl
  have h4 := drainReach 1 (1+2*A+1) _ ds C rC
    (rep P cA.q++Z++rep P y++secCells xs++Z++rep Q z++rep P r++Q++rep P v++R++V) (by omega) gC eC
  simp only [rep,List.append_nil,List.append_assoc] at h1 h2 h3 h4
  unfold body at h1
  unfold body secBody
  simp only [List.append_assoc] at h1 ⊢
  exact reachesTrans (reachesTrans (reachesTrans h1 h2) h3) h4

#print axioms zeroSecondCross
#print axioms zeroCycleSource
end BB6Coverage.Agent41F421.EpochWords
