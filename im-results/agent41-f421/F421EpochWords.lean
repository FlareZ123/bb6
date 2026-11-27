import F421Odd
import F421MergedDrain

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open Regular (P Q Z R Seg repAdd rotateP rotateQ)
abbrev PC := F421TertiaryGuard.Cell
abbrev WC := F421DrainPlan.Row

def reaches (k : Nat) (u v : List Bool) : Prop :=
  ∃ n, k≤n ∧ run0 table n (frontier u) = some (frontier v)

theorem reachesTrans {k l : Nat} {u v w : List Bool}
    (h : reaches k u v) (g : reaches l v w) : reaches (k+l) u w := by
  obtain ⟨n,hn,hr⟩ := h
  obtain ⟨m,hm,hs⟩ := g
  exact ⟨n+m,by omega,join0 hr hs⟩

theorem reachesWeak {k l : Nat} {u v : List Bool} (hkl : k≤l) (h : reaches l u v) : reaches k u v := by
  obtain ⟨n,hn,hr⟩ := h
  exact ⟨n,by omega,hr⟩

def reg (c : PC) : Regular.Cell := ⟨c.p,c.q⟩
def regs (cs : List PC) : List Regular.Cell := cs.map reg
abbrev pw := MergedDrain.word

def near (m : Bool) (cs : List PC) : List Bool := GeneralDrain.nearWord (MergedDrain.rows m cs)

theorem nearEq (m : Bool) (cs : List PC) : Regular.nearWord m (regs cs)=near m cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [regs,reg,near,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.nearWord,GeneralDrain.rowWord,Regular.nearWord,Regular.cellWord] at ih ⊢
    rw [ih]

theorem wordEq (m : Bool) (cs : List PC) : Regular.farWord m (regs cs)=pw m cs := by
  rw [Regular.farWord,show (regs cs).reverse=regs cs.reverse by simp [regs,List.map_reverse],nearEq]
  simp [near,MergedDrain.word,GeneralDrain.farWord,MergedDrain.rows,List.map_reverse]

theorem nearRev (m : Bool) (cs : List PC) : near m cs.reverse=pw m cs := by
  simp [near,MergedDrain.word,GeneralDrain.farWord,MergedDrain.rows,List.map_reverse]

theorem wordCons (m : Bool) (c : PC) (cs : List PC) :
    pw m (c::cs)=pw m cs++rep P c.p++(if m then Z else [])++rep Q c.q := by
  simp [MergedDrain.word,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.farCons,GeneralDrain.rowWord,List.append_assoc]

def valid (cs : List PC) : Prop := ∀ c∈cs, 1≤c.p ∧ 2≤c.q

theorem validRegs (cs : List PC) (h : valid cs) : Regular.valid (regs cs) := by
  intro c hc
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
  exact h x hx

def crossNear (b x : Nat) : List PC → List PC
  | [] => [⟨b,x-1⟩]
  | c::cs => ⟨b,c.p-1⟩::crossNear c.q x cs

def crossFar (b x : Nat) (cs : List PC) : List PC := (crossNear b x cs.reverse).reverse

theorem oddOut (b x : Nat) (cs : List PC) (hb : 2≤b) (hv : valid cs) :
    Regular.oddOutputs (Regular.segs b (regs cs) x)=near true (crossNear b x cs) := by
  induction cs generalizing b with
  | nil => simp [Regular.oddOutputs,Regular.segs,Regular.oddOutputOne,regs,near,crossNear,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.nearWord,GeneralDrain.rowWord,show b-2+2=b by omega]
  | cons c cs ih =>
    have hc := hv c (by simp)
    have ht : valid cs := fun x hx => hv x (by simp [hx])
    change Regular.oddOutputOne (b-2,c.p-1)++Regular.oddOutputs (Regular.segs c.q (regs cs) x)=_
    rw [ih c.q hc.2 ht]
    simp [Regular.oddOutputOne,near,crossNear,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.nearWord,GeneralDrain.rowWord,show b-2+2=b by omega]

theorem validRev (cs : List PC) (h : valid cs) : valid cs.reverse := by
  intro c hc; exact h c (List.mem_reverse.mp hc)

theorem oddECross (a b x : Nat) (cs : List PC) (U : List Bool)
    (hb : 2≤b) (hx : 1≤x) (hv : valid cs) :
    reaches 1 (rep P a++rep Q b++pw false cs++rep P x++Regular.E++U)
      (P++rep Q (a+1)++pw true (crossFar b x cs)++P++U) := by
  let ss := Regular.segs b (regs cs.reverse) x
  have hi := Regular.inputSegs b (regs cs.reverse) x hb hx (validRegs _ (validRev cs hv))
  rw [nearEq,nearRev] at hi
  have ho := oddOut b x cs.reverse hb (validRev cs hv)
  have he : Regular.oddOutputs ss=pw true (crossFar b x cs) := by
    simpa [ss,crossFar,near,MergedDrain.word,GeneralDrain.farWord,MergedDrain.rows,List.map_reverse] using ho
  have h := Regular.principalOddE a ss U
  rw [show Regular.inputs ss=rep Q b++pw false cs++rep P x from hi,he] at h
  exact ⟨8*a+Regular.oddCosts ss+13,by omega,by simpa only [List.append_assoc] using h⟩

theorem oddDCross (a b x q : Nat) (cs : List PC) (ts : List Seg) (U : List Bool)
    (hb : 2≤b) (hx : 1≤x) (hq : 1≤q) (hv : valid cs) :
    reaches 1
      (rep P a++rep Q b++pw false cs++rep P x++rep Q q++[false]++Regular.twistInputs ts++Z++U)
      (P++rep Q (a+1)++pw true (crossFar b x cs)++rep P q++Regular.outputs ts++Q++U) := by
  let ss := Regular.segs b (regs cs.reverse) x
  have hi := Regular.inputSegs b (regs cs.reverse) x hb hx (validRegs _ (validRev cs hv))
  rw [nearEq,nearRev] at hi
  have ho := oddOut b x cs.reverse hb (validRev cs hv)
  have he : Regular.oddOutputs ss=pw true (crossFar b x cs) := by
    simpa [ss,crossFar,near,MergedDrain.word,GeneralDrain.farWord,MergedDrain.rows,List.map_reverse] using ho
  have h := Regular.principalOddD a ss (q-1) ts U
  rw [show Regular.inputs ss=rep Q b++pw false cs++rep P x from hi,he,show q-1+1=q by omega] at h
  exact ⟨8*a+Regular.oddCosts ss+4*q+Regular.costs ts+13,by omega,by simpa only [List.append_assoc] using h⟩

def dec (cs : List PC) : List PC := cs.map fun c => ⟨c.p-1,c.q⟩

theorem decRegs (cs : List PC) : Regular.dec (regs cs)=regs (dec cs) := by
  simp [Regular.dec,regs,reg,dec,List.map_map,Function.comp_def]

theorem decRev (cs : List PC) : dec cs.reverse=(dec cs).reverse := by simp [dec,List.map_reverse]

theorem nearAppend (m : Bool) (xs ys : List PC) : near m (xs++ys)=near m xs++near m ys := by
  simp [near,MergedDrain.rows,GeneralDrain.nearAppend]

theorem carryNear (a b p : Nat) (cs : List PC) (U : List Bool)
    (hb : 2≤b) (hp : 1≤p) (hv : valid cs) :
    reaches 1
      (rep P a++rep Q b++near false cs++rep P p++Z++U)
      (rep P (a+2)++rep Q (b+1)++near true (dec cs)++rep P (p-1)++Q++U) := by
  have h := Regular.carryAcross a b (regs cs) p U hb hp (validRegs _ hv)
  rw [nearEq,decRegs,nearEq] at h
  exact ⟨_,by omega,h⟩

structure TC where
  z : Nat
  r : Nat
  f : Bool
  deriving Repr, DecidableEq

def bit (f : Bool) : Nat := if f then 1 else 0

def tailCell (c : TC) : List Bool := rep Q c.z++rep Z (1+bit c.f)++rep P c.r++R

def tail (xs : List TC) (U : List Bool) : List Bool := xs.flatMap tailCell++U

def shiftRow (c : TC) : WC := ⟨c.z+1,c.r+1,c.f⟩
def shifted (xs : List TC) : List Bool := GeneralDrain.nearWord (xs.map shiftRow)

theorem shiftedAppend (xs ys : List TC) : shifted (xs++ys)=shifted xs++shifted ys := by
  simp [shifted,GeneralDrain.nearAppend]

theorem tailAppend (xs ys : List TC) (U : List Bool) : tail (xs++ys) U=tail xs (tail ys U) := by
  simp [tail,List.append_assoc]

theorem halfZ (f : Bool) : [true]++rep Z (1+bit f)=P++(if f then Z else [])++[false] := by cases f <;> rfl

theorem halfR (r : Nat) : [false]++rep P r++R=rep Q (r+1)++[true] := by
  rw [rotateQ,show r+1=r+1 from rfl,repAdd]
  simp [rep,R,Q,List.append_assoc]

theorem shiftOne (c : TC) : [true]++tailCell c=GeneralDrain.rowWord (shiftRow c)++[true] := by
  unfold tailCell shiftRow GeneralDrain.rowWord
  rw [← List.append_assoc [true],← List.append_assoc [true],← List.append_assoc [true],rotateP]
  simp only [List.append_assoc]
  rw [← List.append_assoc [true],halfZ]
  simp only [List.append_assoc]
  rw [← List.append_assoc [false],halfR]
  rw [show c.z+1=c.z+1 from rfl,repAdd]
  have hp : rep P c.z++P=P++rep P c.z := by
    change rep P c.z++rep P 1=rep P 1++rep P c.z
    rw [← repAdd,← repAdd,Nat.add_comm c.z 1]
  rw [← List.append_assoc (rep P c.z),hp]
  simp [rep,List.append_assoc]

theorem shiftTail (xs : List TC) (U : List Bool) :
    [true]++tail xs U=shifted xs++[true]++U := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have ht : tail (c::cs) U=tailCell c++tail cs U := by simp [tail,List.append_assoc]
    have hs : shifted (c::cs)=GeneralDrain.rowWord (shiftRow c)++shifted cs := by simp [shifted,GeneralDrain.nearWord]
    rw [ht,hs,← List.append_assoc [true],shiftOne,List.append_assoc,ih]
    simp [List.append_assoc]

def body (a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool) : List Bool :=
  rep P a++rep Q b++pw false cs++rep P x++Q++rep P y++R++tail xs U

theorem firstCross (a b x y : Nat) (cs : List PC) (xs : List TC) (U : List Bool)
    (hb : 2≤b) (hx : 1≤x) (hy : 1≤y) (hv : valid cs) :
    reaches 1 (body a b x y cs xs U)
      (P++rep Q (a+1)++pw true (crossFar b x cs)++P++rep Q y++shifted xs++[true]++U) := by
  have h := oddECross a b x cs ([false]++rep P (y-1)++R++tail xs U) hb hx hv
  have hin : Q++rep P y++R++tail xs U=Regular.E++([false]++rep P (y-1)++R++tail xs U) := by
    rw [show y=1+(y-1) by omega,repAdd]
    simp [P,Q,Regular.E,rep,List.append_assoc]
  have hout : [false]++rep P (y-1)++R++tail xs U=rep Q y++shifted xs++[true]++U := by
    rw [halfR,show y-1+1=y by omega,List.append_assoc,shiftTail]
    simp [List.append_assoc]
  simp only [body,List.append_assoc] at hin hout h ⊢
  rw [hin,hout]
  rw [hout] at h
  exact h

def lowRegs (xs : List TC) : List PC := xs.map fun c => ⟨c.z+1,c.r+1⟩
def touch (xs : List TC) : List TC := xs.map fun c => ⟨c.z-1,c.r,true⟩
def target (c : TC) : TC := ⟨c.z-1,c.r+1,false⟩
def clear (xs : List TC) : Prop := ∀ c∈xs, c.f=false
def tailValid (xs : List TC) : Prop := ∀ c∈xs, 1≤c.z ∧ 1≤c.r

theorem lowRegsValid (xs : List TC) (h : tailValid xs) : valid (lowRegs xs) := by
  intro c hc
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
  have hx' := h x hx
  change 1≤x.z+1 ∧ 2≤x.r+1
  omega

theorem lowShift (xs : List TC) (hc : clear xs) : shifted xs=near false (lowRegs xs) := by
  unfold shifted near lowRegs MergedDrain.rows
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [shiftRow,MergedDrain.toRow,Function.comp_def,hc x hx]

theorem lowTouch (xs : List TC) (hv : tailValid xs) : shifted (touch xs)=near true (dec (lowRegs xs)) := by
  unfold shifted touch near dec lowRegs MergedDrain.rows
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  have h := hv x hx
  simp [shiftRow,MergedDrain.toRow,Function.comp_def,show x.z-1+1=x.z by omega]

theorem nearSingleton (m : Bool) (c : PC) : near m [c]=rep P c.p++(if m then Z else [])++rep Q c.q := by
  simp [near,MergedDrain.rows,MergedDrain.toRow,GeneralDrain.nearWord,GeneralDrain.rowWord]

theorem shiftedCons (c : TC) (cs : List TC) : shifted (c::cs)=rep P (c.z+1)++(if c.f then Z else [])++rep Q (c.r+1)++shifted cs := by
  simp [shifted,shiftRow,GeneralDrain.nearWord,GeneralDrain.rowWord,List.append_assoc]

theorem carryTertiary (a b y : Nat) (cs : List PC) (lo hi : List TC) (c : TC) (U : List Bool)
    (hb : 2≤b) (hy : 2≤y) (hv : valid cs) (hlo : tailValid lo) (hclear : clear lo)
    (hc : c.f=true) (hz : 1≤c.z) :
    reaches 1
      (rep P a++rep Q b++pw false cs++P++rep Q y++shifted (lo++c::hi)++[true]++U)
      (rep P (a+2)++rep Q (b+1)++pw true (dec cs)++Z++rep Q y++shifted (touch lo++target c::hi)++[true]++U) := by
  let ws := cs.reverse++[⟨1,y⟩]++lowRegs lo
  have hw : valid ws := by
    intro x hx
    simp only [ws,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (hx|rfl)|hx
    · exact hv x (List.mem_reverse.mp hx)
    · exact ⟨Nat.le_refl _,hy⟩
    · exact lowRegsValid lo hlo x hx
  have h := carryNear a b (c.z+1) ws (rep Q (c.r+1)++shifted hi++[true]++U) hb (by omega) hw
  have hin : near false ws=pw false cs++P++rep Q y++shifted lo := by
    unfold ws
    rw [nearAppend,nearAppend,nearRev,nearSingleton,← lowShift lo hclear]
    simp [rep,List.append_assoc]
  have hout : near true (dec ws)=pw true (dec cs)++Z++rep Q y++shifted (touch lo) := by
    simp only [ws,dec,List.map_append,List.map_cons,List.map_nil]
    change near true (dec cs.reverse++[⟨1-1,y⟩]++dec (lowRegs lo))=_
    rw [nearAppend,nearAppend,decRev,nearRev,nearSingleton,← lowTouch lo hlo]
    simp [rep,List.append_assoc,dec]
  rw [hin,hout] at h
  simp only [shiftedAppend,shiftedCons,hc,ite_true,target,Bool.false_eq_true,ite_false,List.append_nil,show c.z-1+1=c.z by omega,List.append_assoc] at h ⊢
  have hq : Q++rep Q (c.r+1)=rep Q (c.r+1+1) := by
    change rep Q 1++rep Q (c.r+1)=rep Q (c.r+1+1)
    rw [← repAdd,Nat.add_comm]
  simp only [← List.append_assoc Q,hq,List.append_assoc,Nat.add_sub_cancel] at h
  exact h

theorem thirdCross (a b y : Nat) (c : PC) (cs : List PC) (xs : List TC) (U : List Bool)
    (hb : 2≤b) (hy : 1≤y) (hp : 1≤c.p) (hq : 1≤c.q) (hv : valid cs) :
    reaches 1
      (rep P a++rep Q b++pw false (c::cs)++Z++rep Q y++shifted xs++[true]++U)
      (P++rep Q (a+1)++pw true (crossFar b c.p cs)++rep P c.q++Q++rep P (y-1)++R++tail xs U) := by
  have h := oddDCross a b c.p c.q cs [] ([true]++rep Q (y-1)++shifted xs++[true]++U) hb hp hq hv
  have hi : Z++rep Q y=[false]++Z++[true]++rep Q (y-1) := by
    rw [show y=1+(y-1) by omega,repAdd]
    simp [Z,Q,rep,List.append_assoc]
  have ho : [true]++rep Q (y-1)++shifted xs++[true]++U=rep P (y-1)++R++tail xs U := by
    rw [rotateP]
    simp only [List.append_assoc]
    have hsh := shiftTail xs U
    simp only [List.append_assoc] at hsh
    rw [← hsh]
    rfl
  have hi' := congrArg (· ++ shifted xs++[true]++U) hi
  simp only [wordCons,Bool.false_eq_true,ite_false,List.append_nil,Regular.twistInputs,Regular.outputs,List.flatMap_nil,List.nil_append,List.append_assoc] at h ⊢
  simp only [List.append_assoc] at hi' ho
  rw [hi']
  rw [ho] at h ⊢
  exact h

#print axioms firstCross
#print axioms carryTertiary
#print axioms thirdCross
end BB6Coverage.Agent41F421.EpochWords
