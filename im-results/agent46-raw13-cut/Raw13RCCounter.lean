import Raw13RCCounterMacro
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13RCCounter
open BB6Coverage BB6Coverage.Agent31Pump
inductive Digit | a0 | a1 | a2 | a3 | b0 | b1 | b2 | b3 | max
  deriving DecidableEq
inductive Term | t011 | t0100 | t01011 | t01001 | t11 | t01
  deriving DecidableEq
abbrev digit : Digit → List Bool
 | .a0 => [false,true,false,true,false,true]
 | .a1 => [false,true,false,false,false,true]
 | .a2 => [false,true,false,true,true,true]
 | .a3 => [false,true,false,false,true,true]
 | .b0 => [true,false,true,false,true,false]
 | .b1 => [false,false,true,false,true,false]
 | .b2 => [true,true,true,false,true,false]
 | .b3 => [false,true,true,false,true,false]
 | .max => [false,true,false,false,true,false]
abbrev term : Term → List Bool
 | .t011 => [false,true,true]
 | .t0100 => [false,true,false,false]
 | .t01011 => [false,true,false,true,true]
 | .t01001 => [false,true,false,false,true]
 | .t11 => [true,true]
 | .t01 => [false,true]
def enc : List Digit → Term → List Bool
 | [],t => term t
 | d::ds,t => digit d ++ enc ds t
def isA : Digit → Bool
 | .a0 | .a1 | .a2 | .a3 => true
 | _ => false
def valid : List Digit → Term → Prop
 | [],_ => True
 | d::ds,t => valid ds t ∧ (isA d=true → (enc ds t).headD false=false)
theorem enc_nonempty (ds : List Digit) (t : Term) : enc ds t ≠ [] := by
  cases ds with
  | nil => cases t <;> decide
  | cons d ds => cases d <;> simp [enc,digit]
theorem enc_head (ds : List Digit) (t : Term) (h : (enc ds t).headD false=false) : ∃ R, enc ds t = false::R := by
  cases he : enc ds t with
  | nil => exact False.elim (enc_nonempty ds t he)
  | cons b r => rw [he] at h; simp at h; subst b; exact ⟨r,rfl⟩
theorem enc_prepend (n : Nat) (d : Digit) (ds : List Digit) (t : Term) : enc (List.replicate n d ++ ds) t = rep (digit d) n ++ enc ds t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih,List.append_assoc]
theorem validA (n : Nat) (ds : List Digit) (t : Term) (h : valid ds t) (hz : (enc ds t).headD false=false) : valid (List.replicate n Digit.a0 ++ ds) t := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,valid,isA]
    refine ⟨ih,?_⟩
    intro _
    cases n with
    | zero => exact hz
    | succ n => rfl
theorem validB (n : Nat) (ds : List Digit) (t : Term) (h : valid ds t) : valid (List.replicate n Digit.b0 ++ ds) t := by
  induction n with
  | zero => exact h
  | succ n ih => exact ⟨ih,by intro h; contradiction⟩
abbrev root (k : Nat) (ds : List Digit) (t : Term) : Z0 := ⟨0,[false,false,false],digit .max ++ rep (digit .max) k ++ enc ds t⟩
def Result (k : Nat) (ds : List Digit) (t : Term) : Prop := ∃ us u c, 0<c ∧ valid us u ∧ run0 p c (root k ds t) = some (root 0 us u)
theorem finishA {k : Nat} {ds us : List Digit} {t u : Term} {c : Nat} (hc : 0<c)
    (hv : valid us u) (hz : (enc us u).headD false=false)
    (hr : run0 p c (root k ds t) = some (⟨0,[false,false,false],digit .max ++ rep (digit .a0) k ++ enc us u⟩ : Z0)) : Result k ds t := by
  refine ⟨List.replicate k .a0 ++ us,u,c,hc,validA k us u hv hz,?_⟩
  simpa only [root,rep,List.nil_append,List.append_nil,enc_prepend,List.append_assoc] using hr
theorem finishB {k : Nat} {ds us : List Digit} {t u : Term} {c : Nat} (hc : 0<c)
    (hv : valid us u)
    (hr : run0 p c (root k ds t) = some (⟨0,[false,false,false],digit .max ++ rep (digit .b0) k ++ enc us u⟩ : Z0)) : Result k ds t := by
  refine ⟨List.replicate k .b0 ++ us,u,c,hc,validB k us u hv,?_⟩
  simpa only [root,rep,List.nil_append,List.append_nil,enc_prepend,List.append_assoc] using hr
theorem advance (ds : List Digit) (t : Term) (hv : valid ds t) (k : Nat) : Result k ds t := by
  induction ds generalizing k with
  | nil =>
    cases t with
    | t011 => exact finishA (by omega : 0<144+12*k) (us:=[]) (u:=.t0100) trivial rfl (t011.step k)
    | t0100 => exact finishA (by omega : 0<144+12*k) (us:=[]) (u:=.t01011) trivial rfl (t0100.step k)
    | t01011 => exact finishA (by omega : 0<142+12*k) (us:=[]) (u:=.t01001) trivial rfl (t01011.step k)
    | t01001 => exact finishB (by omega : 0<104+12*k) (us:=[.b0]) (u:=.t11) ⟨trivial,by decide⟩ (t01001.step k)
    | t11 => exact finishB (by omega : 0<90+12*k) (us:=[]) (u:=.t01) trivial (t11.step k)
    | t01 => exact finishA (by omega : 0<144+12*k) (us:=[]) (u:=.t01011) trivial rfl (t01.step k)
  | cons d ds ih =>
    have htail := hv.1
    cases d with
    | max =>
      obtain ⟨us,u,c,hc,hu,hr⟩ := ih htail (k+1)
      refine ⟨us,u,c,hc,hu,?_⟩
      have e : rep (digit .max) (k+1)=rep (digit .max) k ++ digit .max := by rw [rep_snoc]; rfl
      simpa only [root,enc,e,List.append_assoc] using hr
    | a0 => exact finishA (by omega : 0<142+12*k) (us:=.a1::ds) (u:=t) ⟨htail,hv.2⟩ rfl (by simpa only [root,enc,List.append_assoc] using a0.step k (enc ds t))
    | a1 => exact finishA (by omega : 0<144+12*k) (us:=.a2::ds) (u:=t) ⟨htail,hv.2⟩ rfl (by simpa only [root,enc,List.append_assoc] using a1.step k (enc ds t))
    | a2 => exact finishA (by omega : 0<142+12*k) (us:=.a3::ds) (u:=t) ⟨htail,hv.2⟩ rfl (by simpa only [root,enc,List.append_assoc] using a2.step k (enc ds t))
    | a3 =>
      obtain ⟨R,hR⟩ := enc_head ds t (hv.2 rfl)
      exact finishB (by omega : 0<104+12*k) (us:=.b0::ds) (u:=t) ⟨htail,by intro he; contradiction⟩ (by simpa only [root,enc,hR,List.append_assoc,List.cons_append,List.nil_append] using a3.step k R)
    | b0 => exact finishB (by omega : 0<90+12*k) (us:=.b1::ds) (u:=t) ⟨htail,by intro he; contradiction⟩ (by simpa only [root,enc,List.append_assoc] using b0.step k (enc ds t))
    | b1 => exact finishB (by omega : 0<92+12*k) (us:=.b2::ds) (u:=t) ⟨htail,by intro he; contradiction⟩ (by simpa only [root,enc,List.append_assoc] using b1.step k (enc ds t))
    | b2 => exact finishB (by omega : 0<90+12*k) (us:=.b3::ds) (u:=t) ⟨htail,by intro he; contradiction⟩ (by simpa only [root,enc,List.append_assoc] using b2.step k (enc ds t))
    | b3 => exact finishA (by omega : 0<144+12*k) (us:=.max::ds) (u:=t) ⟨htail,by intro he; contradiction⟩ rfl (by simpa only [root,enc,List.append_assoc] using b3.step k (enc ds t))
def GoodRoot := { x : List Digit × Term // valid x.1 x.2 }
noncomputable def next (x : GoodRoot) : GoodRoot :=
  let h:=advance x.val.1 x.val.2 x.property 0
  ⟨(Classical.choose h,Classical.choose (Classical.choose_spec h)),(Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.1⟩
noncomputable def seq : Nat → GoodRoot
 | 0 => ⟨([.a1],.t011),⟨trivial,by decide⟩⟩
 | n+1 => next (seq n)
noncomputable def family (n : Nat) := root 0 (seq n).val.1 (seq n).val.2
theorem seed : run0 p 280 (⟨0,[],[]⟩ : Z0) = some (family 0) := by rfl
theorem growth (n : Nat) : ∃ c, 0<c ∧ run0 p c (family n)=some (family (n+1)) := by
  let h:=advance (seq n).val.1 (seq n).val.2 (seq n).property 0
  let hs:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  exact ⟨_,hs.1,hs.2.2⟩
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth n)
  exact never_of_growth p family 280 cost seed (fun n => (Classical.choose_spec (growth n)).1) (fun n => (Classical.choose_spec (growth n)).2) m hm
#print axioms advance
#print axioms never
end BB6.Agent46Raw13RCCounter
