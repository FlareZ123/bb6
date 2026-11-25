import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LF1200
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
def Y := bits "1101"
def V := bits "0110"
def Z := bits "1011"
def frame (L W : List Bool) : Z0 := ⟨1,W.headD false::L,W.tail⟩
def sect (k : Nat) (W : List Bool) := frame (rep Y k) W

theorem oneL (L R : List Bool) : run0 table 4 ⟨1,[true]++Y++L,R⟩ =
    some ⟨1,[true]++L,V++R⟩ := by rfl

theorem oneR (L R : List Bool) : run0 table 4 ⟨1,[false]++L,V++R⟩ =
    some ⟨1,[false]++Y++L,R⟩ := by rfl

theorem turn (R : List Bool) : run0 table 12 ⟨1,[true],R⟩ =
    some ⟨1,[],V++R⟩ := by rfl

theorem firstR (R : List Bool) : run0 table 4 ⟨1,[],V++R⟩ =
    some ⟨1,false::Y,R⟩ := by rfl

theorem reset (j : Nat) (R : List Bool) :
    run0 table (8*j+16) ⟨1,true::rep Y j,R⟩ = some (sect (j+1) (false::R)) := by
  have h1 : run0 table (4*j) ⟨1,true::rep Y j,R⟩ =
      some ⟨1,[true],rep V j++R⟩ := by
    simpa only [List.append_nil,List.nil_append,List.singleton_append] using
      sweepL table 1 [true] [] Y V 4 oneL j [] R
  have h2 := turn (rep V j++R)
  have h3 := firstR (rep V j++R)
  have h4 : run0 table (4*j) ⟨1,false::Y,rep V j++R⟩ =
      some (sect (j+1) (false::R)) := by
    have H := sweepR table 1 [false] [] V Y 4 oneR j Y R
    simp only [List.append_assoc] at H
    rw [rep_snoc Y j] at H
    simpa only [List.singleton_append,List.nil_append,sect,frame,rep,
      List.headD_cons,List.tail_cons] using H
  have H := join0 (join0 (join0 h1 h2) h3) h4
  simpa only [show 4*j+12+4+4*j=8*j+16 by omega] using H

theorem cross (k : Nat) (R : List Bool) :
    run0 table 4 (sect (k+1) (bits "00111"++R)) =
    some ⟨1,true::rep Y (k+2),R⟩ := by rfl

theorem finish (k : Nat) (R : List Bool) :
    ∃ t, 0<t ∧ run0 table t ⟨1,true::rep Y k,bits "0111"++R⟩ =
      some (sect (k+3) (false::R)) := by
  have h1 := reset k (bits "0111"++R)
  have h2 := cross k R
  have h3 := reset (k+2) R
  exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

inductive Term where
  | one | z | mid | short | deepA | deepB
  deriving DecidableEq, Repr

def inp : Term → List Bool
  | .one => bits "1"
  | .z => bits "000"
  | .mid => bits "0101"
  | .short => bits "010000"
  | .deepA => bits "0100011000"
  | .deepB => bits "011110000"

def out0 : Term → List Bool
  | .one => []
  | .z => bits "10"
  | .mid => bits "110"
  | .short => bits "11110"
  | .deepA => bits "110011110"
  | .deepB => bits "00001100"

def cost0 : Term → Nat
  | .one => 0
  | .z => 12
  | .mid => 10
  | .short => 18
  | .deepA => 26
  | .deepB => 32

def outN : Term → List Bool
  | .one => bits "010"
  | .z => bits "01110"
  | .mid => bits "011110"
  | .short => bits "01111110"
  | .deepA => bits "011110011110"
  | .deepB => bits "01100001100"

def costN : Term → Nat
  | .one => 3
  | .z => 11
  | .mid => 9
  | .short => 17
  | .deepA => 25
  | .deepB => 31

theorem localBase (t : Term) (ht : t ≠ .one) (L R : List Bool) :
    run0 table (cost0 t) (frame (Y++L) (inp t++R)) =
      some ⟨1,true::L,bits "0111"++out0 t++R⟩ := by
  cases t <;> first | contradiction | rfl

theorem localDeep (t : Term) (L R : List Bool) :
    run0 table (costN t) (frame (Z++L) (inp t++R)) =
      some ⟨1,true::true::L,outN t++R⟩ := by cases t <;> rfl

theorem scanOne (L W : List Bool) : run0 table 4 (frame L (V++W)) =
    some (frame (Z++L) W) := by rfl

theorem scan (n : Nat) (L W : List Bool) :
    run0 table (4*n) (frame L (rep V n++W)) = some (frame (rep Z n++L) W) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (scanOne L (rep V n++W)) (ih (Z++L))
    rw [show 4+4*n=4*(n+1) by omega] at H
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Z n) Z L,rep_snoc Z n] using H

theorem zReturn (L R : List Bool) : run0 table 4 ⟨1,[true,true]++Z++L,R⟩ =
    some ⟨1,[true,true]++L,V++R⟩ := by rfl

theorem yReturn (L R : List Bool) : run0 table 5 ⟨1,[true,true]++Y++L,R⟩ =
    some ⟨1,true::L,bits "01110"++R⟩ := by rfl

theorem base (k : Nat) (t : Term) (ht : t ≠ .one) (R : List Bool) :
    ∃ n, 0<n ∧ run0 table n (sect (k+1) (inp t++R)) =
      some (sect (k+3) (false::(out0 t++R))) := by
  have h1 := localBase t ht (rep Y k) R
  obtain ⟨n,hn,h2⟩ := finish k (out0 t++R)
  rw [← List.append_assoc] at h2
  exact ⟨_,by omega,join0 h1 h2⟩

theorem deep (k j : Nat) (t : Term) (R : List Bool) :
    ∃ n, 0<n ∧ run0 table n (sect (k+1) (rep V (j+1)++inp t++R)) =
      some (sect (k+3) (false::false::(rep V j++outN t++R))) := by
  have h1 := scan (j+1) (Y++rep Y k) (inp t++R)
  have h2 := localDeep t (rep Z j++Y++rep Y k) R
  have h12 : run0 table (4*(j+1)+costN t)
      (sect (k+1) (rep V (j+1)++inp t++R)) =
      some ⟨1,[true,true]++rep Z j++Y++rep Y k,outN t++R⟩ := by
    have h1' : run0 table (4*(j+1)) (sect (k+1) (rep V (j+1)++inp t++R)) =
      some (frame (Z++(rep Z j++Y++rep Y k)) (inp t++R)) := by
      simpa only [sect,rep,List.append_assoc] using h1
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using join0 h1' h2
  have h3 := sweepL table 1 [true,true] [] Z V 4 zReturn j (Y++rep Y k) (outN t++R)
  have h3' : run0 table (4*j) ⟨1,[true,true]++rep Z j++Y++rep Y k,outN t++R⟩ =
      some ⟨1,[true,true]++Y++rep Y k,rep V j++outN t++R⟩ := by
    simpa only [List.append_assoc,List.nil_append] using h3
  have h4 := yReturn (rep Y k) (rep V j++outN t++R)
  obtain ⟨n,hn,h5⟩ := finish k (false::(rep V j++outN t++R))
  exact ⟨_,by omega,join0 (join0 (join0 h12 h3') h4) h5⟩

theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (sect 2 [false,false]) := by rfl

abbrev DState := Fin 22
def rows : Array (DState × DState) := #[
  (1,2),(3,4),(2,2),(5,2),(5,6),(7,8),(9,10),(11,2),(12,12),(13,12),(2,14),
  (14,10),(15,16),(15,17),(14,2),(18,2),(18,19),(18,6),(20,8),(9,2),(21,2),(2,10)]
def delta (s : DState) (b : Bool) : DState :=
  if b then rows[s.val]!.2 else rows[s.val]!.1
def accepting (s : DState) : Bool := [0,1,3,4,5,7,11,14].contains s
def read (s : DState) : List Bool → DState
  | [] => s
  | b::w => read (delta s b) w
def Safe (w : List Bool) : Prop := accepting (read 0 w) = true

theorem read_append (s : DState) (u v : List Bool) :
    read s (u++v) = read (read s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => exact ih (delta s b)

theorem zero_pad : ∀ s : DState, accepting s = accepting (delta s false) := by decide

theorem dead_read (w : List Bool) : read 2 w = 2 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact ih

def masks : Array Nat := #[1,2,4194303,24,16,32,64,128,768,512,1026,2048,12290,8194,
  18619,229400,196624,131088,262176,524352,1048704,2099264]
def incl (a b : DState) : Bool := masks[a.val]!.testBit b.val

theorem incl_acc : ∀ a b : DState, incl a b = true → accepting a = true → accepting b = true := by decide

theorem incl_delta : ∀ (a b : DState) (c : Bool), incl a b = true → incl (delta a c) (delta b c) = true := by decide

theorem incl_sound (a b : DState) (w : List Bool) (h : incl a b = true)
    (ha : accepting (read a w) = true) : accepting (read b w) = true := by
  induction w generalizing a b with
  | nil => exact incl_acc a b h ha
  | cons c w ih => exact ih _ _ (incl_delta a b c h) ha

theorem incl_base (t : Term) (h : t ≠ .one) : incl (read 0 (inp t)) (read 0 (false::out0 t)) = true := by
  cases t <;> first | contradiction | decide

theorem incl_deep0 (t : Term) : incl (read 9 (inp t)) (read 3 (outN t)) = true := by cases t <;> decide

theorem incl_deep1 (t : Term) : incl (read 9 (inp t)) (read 15 (outN t)) = true := by cases t <;> decide

theorem read_V9 (n : Nat) : read 9 (rep V n) = 9 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,read_append,show read 9 V=9 by decide,ih]

theorem read_V0 (n : Nat) : read 0 (rep V (n+1)) = 9 := by
  rw [rep,read_append,show read 0 V=9 by decide,read_V9]

theorem read_V15 (n : Nat) : read 15 (rep V n) = 15 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,read_append,show read 15 V=15 by decide,ih]

theorem read_V3 (n : Nat) : read 3 (rep V (n+1)) = 15 := by
  rw [rep,read_append,show read 3 V=15 by decide,read_V15]

theorem safe_base (t : Term) (ht : t ≠ .one) (R : List Bool)
    (h : Safe (inp t++R)) : Safe (false::(out0 t++R)) := by
  unfold Safe at *
  rw [read_append] at h
  change accepting (read 0 ((false::out0 t)++R)) = true
  rw [read_append]
  exact incl_sound _ _ R (incl_base t ht) h

theorem safe_deep (j : Nat) (t : Term) (R : List Bool)
    (h : Safe (rep V (j+1)++inp t++R)) : Safe (false::false::(rep V j++outN t++R)) := by
  unfold Safe at *
  rw [List.append_assoc,read_append,read_V0,read_append] at h
  change accepting (read 3 (rep V j++outN t++R)) = true
  rw [List.append_assoc,read_append,read_append]
  cases j with
  | zero => exact incl_sound _ _ R (incl_deep0 t) h
  | succ j => rw [read_V3]; exact incl_sound _ _ R (incl_deep1 t) h

-- Prefix recognition permits implicit zero padding, retaining the actual remaining suffix.
inductive PPad : List Bool → List Bool → List Bool → Prop where
  | nil (w : List Bool) : PPad [] w w
  | cons {b : Bool} {p w r : List Bool} : w.headD false = b → PPad p w.tail r → PPad (b::p) w r

theorem ppad_append {p q w r s : List Bool} (h : PPad p w r) (g : PPad q r s) : PPad (p++q) w s := by
  induction h with
  | nil => exact g
  | cons hb hp ih => exact PPad.cons hb (ih g)

theorem ppad_len {p w r : List Bool} (h : PPad p w r) : r.length = w.length-p.length := by
  induction h with
  | nil => simp
  | cons hb hp ih => rw [ih,List.length_tail,List.length_cons]; omega

theorem accept_head (s : DState) (w : List Bool) :
    accepting (read s w) = accepting (read (delta s (w.headD false)) w.tail) := by
  cases w with
  | nil => exact zero_pad s
  | cons b w => rfl

theorem ppad_accept {p w r : List Bool} (h : PPad p w r) (s : DState) :
    accepting (read s w) = accepting (read (read s p) r) := by
  induction h generalizing s with
  | nil => rfl
  | cons hb hp ih => rw [accept_head s _,hb,ih]; rfl

def WEq (w v : List Bool) : Prop := ∀ i : Nat, w.getD i false = v.getD i false

theorem head_get (w : List Bool) : w.headD false = w.getD 0 false := by cases w <;> rfl

theorem tail_get (w : List Bool) (i : Nat) : w.tail.getD i false = w.getD (i+1) false := by cases w <;> rfl

theorem ppad_eq {p w r : List Bool} (h : PPad p w r) : WEq w (p++r) := by
  induction h with
  | nil => intro i; rfl
  | cons hb hp ih =>
    intro i
    cases i with
    | zero => rw [← head_get]; exact hb
    | succ i => rw [← tail_get]; exact ih i

theorem ppad_V_lt {w r : List Bool} (h : PPad V w r) : r.length < w.length := by
  have hl := ppad_len h
  have hw : w ≠ [] := by
    intro he
    have H := ppad_eq h 1
    rw [he] at H
    contradiction
  have hw' : 0 < w.length := by cases w <;> simp_all
  have hv : V.length=4 := by decide
  omega

def strip (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | []::ps => strip b ps
  | (c::p)::ps => if b=c then p::strip b ps else strip b ps

theorem mem_strip (b : Bool) (ps : List (List Bool)) (p : List Bool)
    (h : p ∈ strip b ps) : b::p ∈ ps := by
  induction ps with
  | nil => simp [strip] at h
  | cons x xs ih =>
    cases x with
    | nil => exact List.mem_cons_of_mem _ (ih h)
    | cons c y =>
      by_cases he : b=c
      · subst c
        have hh : p ∈ y::strip b xs := by simpa [strip] using h
        rcases List.mem_cons.mp hh with rfl|h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
      · exact List.mem_cons_of_mem _ (ih (by simpa only [strip,if_neg he] using h))

def coverCheck (s : DState) (ps : List (List Bool)) : Nat → Bool
  | 0 => s == 2 || ps.contains []
  | n+1 => s == 2 || ps.contains [] ||
      (coverCheck (delta s false) (strip false ps) n && coverCheck (delta s true) (strip true ps) n)

theorem cover_sound (n : Nat) (s : DState) (ps : List (List Bool)) (w : List Bool)
    (hc : coverCheck s ps n = true) (ha : accepting (read s w) = true) :
    ∃ p ∈ ps, ∃ r, PPad p w r := by
  induction n generalizing s ps w with
  | zero =>
    simp only [coverCheck,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at hc
    rcases hc with hs|hp
    · subst s; rw [dead_read] at ha; contradiction
    · exact ⟨[],hp,w,PPad.nil w⟩
  | succ n ih =>
    by_cases hs : s=2
    · subst s; rw [dead_read] at ha; contradiction
    by_cases hp : [] ∈ ps
    · exact ⟨[],hp,w,PPad.nil w⟩
    have hh : coverCheck (delta s false) (strip false ps) n = true ∧
        coverCheck (delta s true) (strip true ps) n = true := by
      simpa [coverCheck,hs,hp] using hc
    have ha' := (accept_head s w).symm.trans ha
    cases hb : w.headD false with
    | false =>
      rw [hb] at ha'
      obtain ⟨p,hp,r,hr⟩ := ih _ _ _ hh.1 ha'
      exact ⟨false::p,mem_strip _ _ _ hp,r,PPad.cons hb hr⟩
    | true =>
      rw [hb] at ha'
      obtain ⟨p,hp,r,hr⟩ := ih _ _ _ hh.2 ha'
      exact ⟨true::p,mem_strip _ _ _ hp,r,PPad.cons hb hr⟩

def ts0 : List Term := [.z,.mid,.short,.deepA,.deepB]
def tsN : List Term := [.one,.z,.mid,.short,.deepA,.deepB]
def ps0 : List (List Bool) := V::ts0.map inp
def psN : List (List Bool) := V::tsN.map inp

theorem cover0 : coverCheck 0 ps0 10 = true := by decide

theorem coverN : coverCheck 9 psN 10 = true := by decide

theorem parseN (w : List Bool) (hw : accepting (read 9 w) = true) :
    ∃ j : Nat, ∃ t : Term, ∃ r, PPad (rep V j++inp t) w r := by
  obtain ⟨p,hp,r,hr⟩ := cover_sound 10 9 psN w coverN hw
  rcases List.mem_cons.mp hp with hV|ht
  · subst p
    have ha := ppad_accept hr 9
    rw [show read 9 V=9 by decide,hw] at ha
    have hlt := ppad_V_lt hr
    obtain ⟨j,t,s,hs⟩ := parseN r ha.symm
    exact ⟨j+1,t,s,by simpa only [rep,List.append_assoc] using ppad_append hr hs⟩
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht
    exact ⟨0,t,r,hr⟩
termination_by w.length

theorem parse (w : List Bool) (hw : Safe w) :
    (∃ t : Term, t ≠ .one ∧ ∃ r, PPad (inp t) w r) ∨
    (∃ j : Nat, ∃ t : Term, ∃ r, PPad (rep V (j+1)++inp t) w r) := by
  obtain ⟨p,hp,r,hr⟩ := cover_sound 10 0 ps0 w cover0 hw
  rcases List.mem_cons.mp hp with hV|ht
  · subst p
    have ha := ppad_accept hr 0
    rw [show read 0 V=9 by decide,show accepting (read 0 w)=true from hw] at ha
    obtain ⟨j,t,s,hs⟩ := parseN r ha.symm
    exact Or.inr ⟨j,t,s,by simpa only [rep,List.append_assoc] using ppad_append hr hs⟩
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht
    have hne : t ≠ .one := by intro h; subst t; contradiction
    exact Or.inl ⟨t,hne,r,hr⟩

def ZEq (a b : Z0) : Prop := a.q=b.q ∧ WEq a.l b.l ∧ WEq a.r b.r

theorem weq_head {a b : List Bool} (h : WEq a b) : a.headD false = b.headD false := by
  rw [head_get,head_get]; exact h 0

theorem weq_tail {a b : List Bool} (h : WEq a b) : WEq a.tail b.tail := by
  intro i; rw [tail_get,tail_get]; exact h (i+1)

theorem weq_cons (x : Bool) {a b : List Bool} (h : WEq a b) : WEq (x::a) (x::b) := by
  intro i; cases i with
  | zero => rfl
  | succ i => exact h i

theorem zeq_refl (z : Z0) : ZEq z z := ⟨rfl,fun _ => rfl,fun _ => rfl⟩
theorem zeq_trans {a b c : Z0} (h : ZEq a b) (g : ZEq b c) : ZEq a c :=
  ⟨h.1.trans g.1,fun i => (h.2.1 i).trans (g.2.1 i),fun i => (h.2.2 i).trans (g.2.2 i)⟩

theorem sect_eq (k : Nat) {w v : List Bool} (h : WEq w v) : ZEq (sect k w) (sect k v) := by
  refine ⟨rfl,?_,weq_tail h⟩
  change WEq (w.headD false::rep Y k) (v.headD false::rep Y k)
  rw [weq_head h]; intro i; rfl

theorem move_eq (mv : Move) {a b : Z0} (h : ZEq a b) : ZEq (move0 mv a) (move0 mv b) := by
  rcases h with ⟨hq,hl,hr⟩
  cases hh : mv.right with
  | false =>
    simp only [move0,hh,Bool.false_eq_true,if_false]
    exact ⟨rfl,weq_tail hl,weq_cons mv.write hr⟩
  | true =>
    simp only [move0,hh,if_true]
    refine ⟨rfl,?_,weq_tail hr⟩
    rw [weq_head hr]
    exact weq_cons _ (weq_cons _ (weq_tail hl))

theorem step_eq (p : PartialMachine) {a b c : Z0} (hab : ZEq a b) (h : step0 p b = some c) :
    ∃ d, step0 p a = some d ∧ ZEq d c := by
  have he : (a.q,a.l.headD false) = (b.q,b.l.headD false) := by rw [hab.1,weq_head hab.2.1]
  unfold step0 at *
  rw [he]
  change ((p (b.q,b.l.headD false)).bind id).map (fun mv => move0 mv b) = some c at h
  cases hm : (p (b.q,b.l.headD false)).bind id with
  | none => rw [hm] at h; contradiction
  | some mv =>
    rw [hm] at h
    simp only [Option.map_some,Option.some.injEq] at h
    subst c
    exact ⟨_,rfl,move_eq mv hab⟩

theorem run_eq (p : PartialMachine) (n : Nat) {a b c : Z0} (hab : ZEq a b)
    (hr : run0 p n b = some c) : ∃ d, run0 p n a = some d ∧ ZEq d c := by
  induction n generalizing a b c with
  | zero => simp [run0] at hr; subst c; exact ⟨a,rfl,hab⟩
  | succ n ih =>
    simp only [run0] at hr ⊢
    cases hs : step0 p b with
    | none => simp [hs] at hr
    | some x =>
      obtain ⟨y,hy,he⟩ := step_eq p hab hs
      rw [hs] at hr
      obtain ⟨d,hd,hde⟩ := ih he hr
      exact ⟨d,by simp [hy,hd],hde⟩

theorem progress (k : Nat) (w : List Bool) (hw : Safe w) (z : Z0) (hz : ZEq z (sect (k+1) w)) :
    ∃ n z' w', 0<n ∧ run0 table n z = some z' ∧ Safe w' ∧ ZEq z' (sect (k+3) w') := by
  rcases parse w hw with ⟨t,ht,R,h⟩|⟨j,t,R,h⟩
  · have hp : Safe (inp t++R) := by
      unfold Safe; rw [read_append]; exact (ppad_accept h 0).symm.trans hw
    obtain ⟨n,hn,hr⟩ := base k t ht R
    obtain ⟨z',hz',he⟩ := run_eq table n (zeq_trans hz (sect_eq _ (ppad_eq h))) hr
    exact ⟨n,z',_,hn,hz',safe_base t ht R hp,he⟩
  · have hp : Safe (rep V (j+1)++inp t++R) := by
      unfold Safe; rw [read_append]; exact (ppad_accept h 0).symm.trans hw
    obtain ⟨n,hn,hr⟩ := deep k j t R
    obtain ⟨z',hz',he⟩ := run_eq table n (zeq_trans hz (sect_eq _ (ppad_eq h))) hr
    exact ⟨n,z',_,hn,hz',safe_deep j t R hp,he⟩

theorem arbitrary (n : Nat) : ∃ t z, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have H : ∀ m : Nat, ∃ t z k w, m≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Safe w ∧ ZEq z (sect (k+1) w) := by
    intro m; induction m with
    | zero => exact ⟨40,sect 2 [false,false],1,[false,false],by omega,entry,by unfold Safe; decide,zeq_refl _⟩
    | succ m ih =>
      obtain ⟨t,z,k,w,ht,hr,hw,hz⟩ := ih
      obtain ⟨u,z',w',hu,hs,hSafe,he⟩ := progress k w hw z hz
      exact ⟨t+u,z',k+2,w',by omega,join0 hr hs,hSafe,he⟩
  obtain ⟨t,z,k,w,ht,hr,_,_⟩ := H n
  exact ⟨t,z,ht,hr⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
#print axioms arbitrary
#print axioms base
#print axioms deep
#print axioms parse
#print axioms safe_base
#print axioms safe_deep
end BB6Coverage.Agent4Raw109LF1200
