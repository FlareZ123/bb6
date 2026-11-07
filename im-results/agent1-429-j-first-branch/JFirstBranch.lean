import JF0Prefix
import BCFuture
import Lean.Elab.Tactic.Omega

namespace BB429JFirstBranch
open BB6Coverage BB6Bubble BB6BCFuture BB429PhysicalFrontier BB429JPhysical

def D : Fin 6 := ⟨3, by decide⟩
def E : Fin 6 := ⟨4, by decide⟩

def writeAt (t : Int → Bool) (x : Int) (b : Bool) : Int → Bool :=
  fun y => if y = x then b else t y

theorem config_ext {a b : Config}
    (hs : a.state=b.state) (hh : a.head=b.head)
    (ht : a.tape=b.tape) : a=b := by
  cases a
  cases b
  simp_all


def baseTape (u w : Nat) : Int → Bool :=
  zeroPaint (negFill (jTape u w) u) (2*(u:Int)) (2*u+3)

def f0Tape (u w : Nat) : Int → Bool :=
  writeAt (baseTape u w) (-2*(u:Int)-6) false

def setupTape (t : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if h-2 ≤ x ∧ x ≤ h+3 then true else t x

def jTapeAt (u w : Nat) (head : Int) : Int → Bool :=
  fun x => jTape u w (x-head)

def cbPaint (t : Int → Bool) (h : Int) : Nat → Int → Bool
  | 0 => t
  | Nat.succ k =>
      writeAt (writeAt (cbPaint t h k) (h+2*(k:Int)) false)
        (h+2*(k:Int)+1) true

theorem rawStep_of_read (m : Machine) (c : Config) (s : Fin 6) (b : Bool)
    (mv : Move) (hs : readSlot c = (s,b))
    (hm : m (s,b) = some mv) :
    rawStep m c = some (applyMove c mv) := by
  simp [rawStep, hs, hm]

theorem cbPaint_zero (t : Int → Bool) (h : Int) :
    cbPaint t h 0 = t := rfl

theorem cbPaint_left (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hx : x < h) : cbPaint t h k x = t x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h0 : x≠h+2*(k:Int) := by omega
      have h1 : x≠h+2*(k:Int)+1 := by omega
      simpa [cbPaint,writeAt,h0,h1] using ih

theorem cbPaint_right (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hx : h+2*(k:Int) ≤ x) : cbPaint t h k x = t x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h0 : x≠h+2*(k:Int) := by omega
      have h1 : x≠h+2*(k:Int)+1 := by omega
      have hx' : h+2*(k:Int)≤x := by omega
      simpa [cbPaint,writeAt,h0,h1] using ih hx'

theorem cbPaint_compose (t : Int → Bool) (h : Int) (k : Nat) :
    cbPaint (cbPaint t h 1) (h+2) k = cbPaint t h (Nat.succ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext x
      have hp : h+2+2*(k:Int)=h+2*((Nat.succ k):Int) := by omega
      change writeAt (writeAt (cbPaint (cbPaint t h 1) (h+2) k)
          (h+2+2*(k:Int)) false) (h+2+2*(k:Int)+1) true x =
        writeAt (writeAt (cbPaint t h (Nat.succ k))
          (h+2*((Nat.succ k):Int)) false)
          (h+2*((Nat.succ k):Int)+1) true x
      rw [ih]
      simp [writeAt,hp]

theorem cbPaint_compose_right (t : Int → Bool) (h : Int) (k : Nat) :
    cbPaint (cbPaint t h k) (h+2*(k:Int)) (Nat.succ 0) =
      cbPaint t h (Nat.succ k) := by
  funext x
  simp [cbPaint,writeAt]

theorem cbPaint_even (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hlo : h≤x) (hhi : x<h+2*(k:Int)) (heven : (x-h)%2=0) :
    cbPaint t h k x=false := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hx0 : x=h+2*(k:Int)
      · subst x
        simp [cbPaint,writeAt] <;> omega
      · by_cases hx1 : x=h+2*(k:Int)+1
        · subst x
          have hbad : (h+2*(k:Int)+1-h)%2=0 := heven
          omega
        · have hhi' : x<h+2*(k:Int) := by omega
          simpa [cbPaint,writeAt,hx0,hx1] using ih hhi'

theorem cbPaint_odd (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hlo : h≤x) (hhi : x<h+2*(k:Int)) (hodd : (x-h)%2=1) :
    cbPaint t h k x=true := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hx0 : x=h+2*(k:Int)
      · subst x
        have hbad : (h+2*(k:Int)-h)%2=1 := hodd
        omega
      · by_cases hx1 : x=h+2*(k:Int)+1
        · subst x
          simp [cbPaint,writeAt]
        · have hhi' : x<h+2*(k:Int) := by omega
          simpa [cbPaint,writeAt,hx0,hx1] using ih hhi'

/-- The two raw C/1, B/0 instructions paint one 01 pair and return to C. -/
theorem bc_two_full (m : Machine) (c : Config)
    (hC : m (C,true)=some ⟨false,true,B⟩)
    (hB : m (B,false)=some ⟨true,true,C⟩)
    (hs : c.state=C) (h0 : c.tape c.head=true)
    (h1 : c.tape (c.head+1)=false) :
    ∃ d, run m 2 c=some d ∧ d.state=C ∧ d.head=c.head+2 ∧
      d.tape=cbPaint c.tape c.head 1 := by
  let ca : Move := ⟨false,true,B⟩
  let ba : Move := ⟨true,true,C⟩
  let c1 := applyMove c ca
  let c2 := applyMove c1 ba
  have hcslot : readSlot c=(C,true) := by
    change (c.state,c.tape c.head)=(C,true)
    exact Prod.ext hs h0
  have hcraw : rawStep m c=some c1 := by
    simp [rawStep,hcslot,hC,c1,ca]
  have hdslot : readSlot c1=(B,false) := by
    change (c1.state,c1.tape c1.head)=(B,false)
    apply Prod.ext
    · rfl
    · change (if c.head+1 = c.head then false else c.tape (c.head+1)) = false
      have hn : c.head+1≠c.head := by omega
      simp [hn,h1]
  have hbraw : rawStep m c1=some c2 := by
    simp [rawStep,hdslot,hB,c2,ba]
  have hr : run m 2 c=some c2 := by
    simp [run,hcraw,hbraw]
  have htape : c2.tape=cbPaint c.tape c.head 1 := by
    funext x
    by_cases hx0 : x=c.head
    · subst x
      simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt]
    · by_cases hx1 : x=c.head+1
      · subst x
        simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt] <;> omega
      · simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt,hx0,hx1] <;> omega
  refine ⟨c2,hr,?_,?_,htape⟩
  · rfl
  · simp [c2,c1,applyMove,ca,ba]
    omega

/-- Arbitrary C/1, B/0 sweeps write 01 repeatedly and preserve the
    complete tape outside the swept interval. -/
theorem bc_sweep (m : Machine) (k : Nat) (c : Config)
    (hC : m (C,true)=some ⟨false,true,B⟩)
    (hB : m (B,false)=some ⟨true,true,C⟩)
    (hs : c.state=C)
    (hpair : ∀ i : Nat, i<k →
      c.tape (c.head+2*(i:Int))=true ∧
      c.tape (c.head+2*(i:Int)+1)=false) :
    ∃ d, run m (2*k) c=some d ∧ d.state=C ∧
      d.head=c.head+2*(k:Int) ∧ d.tape=cbPaint c.tape c.head k := by
  induction k generalizing c with
  | zero =>
      refine ⟨c,by simp [run],hs,by simp,?_⟩
      exact cbPaint_zero c.tape c.head
  | succ k ih =>
      have hp0 := hpair 0 (by omega)
      have hzero : c.tape c.head=true := by simpa using hp0.1
      have hone : c.tape (c.head+1)=false := by simpa using hp0.2
      obtain ⟨d1,hr1,hs1,hd1,ht1⟩ := bc_two_full m c hC hB hs hzero hone
      have hpair' : ∀ i : Nat, i<k →
          d1.tape (d1.head+2*(i:Int))=true ∧
          d1.tape (d1.head+2*(i:Int)+1)=false := by
        intro i hi
        have h0 : d1.tape (d1.head+2*(i:Int)) =
            c.tape (c.head+2*(i:Int)+2) := by
          rw [ht1,hd1]
          rw [show c.head+2+2*(i:Int)=c.head+2*(i:Int)+2 by omega]
          exact cbPaint_right c.tape c.head 1 (c.head+2*(i:Int)+2) (by omega)
        have h1 : d1.tape (d1.head+2*(i:Int)+1) =
            c.tape (c.head+2*(i:Int)+3) := by
          rw [ht1,hd1]
          rw [show c.head+2+2*(i:Int)+1=c.head+2*(i:Int)+3 by omega]
          exact cbPaint_right c.tape c.head 1 (c.head+2*(i:Int)+3) (by omega)
        have hp := hpair (i+1) (by omega)
        have hpos0 : c.head+2*(i:Int)+2=c.head+2*((i+1:Int)) := by omega
        have hpos1 : c.head+2*(i:Int)+3=c.head+2*((i+1:Int))+1 := by omega
        constructor
        · calc
            d1.tape (d1.head+2*(i:Int)) = c.tape (c.head+2*(i:Int)+2) := h0
            _ = c.tape (c.head+2*((i+1:Int))) := by rw [hpos0]
            _ = true := hp.1
        · calc
            d1.tape (d1.head+2*(i:Int)+1) = c.tape (c.head+2*(i:Int)+3) := h1
            _ = c.tape (c.head+2*((i+1:Int))+1) := by rw [hpos1]
            _ = false := hp.2
      obtain ⟨d,hr2,hs2,hd2,ht2⟩ := ih d1 hs1 hpair'
      have hrun : run m (2*(k+1)) c=some d := by
        have hlen : 2*(k+1)=2+2*k := by omega
        rw [hlen,run_add',hr1]
        simpa using hr2
      refine ⟨d,hrun,hs2,?_,?_⟩
      · rw [hd2,hd1]
        omega
      · calc
          d.tape = cbPaint d1.tape d1.head k := ht2
          _ = cbPaint (cbPaint c.tape c.head 1) (c.head+2) k := by rw [ht1,hd1]
          _ = cbPaint c.tape c.head (k+1) := by
            simpa using cbPaint_compose c.tape c.head k

/-- The final C/1, B/1 pair exits the right sweep into A. -/
theorem cb_exit (m : Machine) (c : Config)
    (hC : m (C,true)=some ⟨false,true,B⟩)
    (hB : m (B,true)=some ⟨true,true,A⟩)
    (hs : c.state=C) (h0 : c.tape c.head=true)
    (h1 : c.tape (c.head+1)=true) :
    ∃ d, run m 2 c=some d ∧ d.state=A ∧ d.head=c.head+2 ∧
      d.tape=cbPaint c.tape c.head 1 := by
  let ca : Move := ⟨false,true,B⟩
  let ba : Move := ⟨true,true,A⟩
  let c1 := applyMove c ca
  let c2 := applyMove c1 ba
  have hcslot : readSlot c=(C,true) := by
    change (c.state,c.tape c.head)=(C,true)
    exact Prod.ext hs h0
  have hcraw : rawStep m c=some c1 := by
    simp [rawStep,hcslot,hC,c1,ca]
  have hdslot : readSlot c1=(B,true) := by
    change (c1.state,c1.tape c1.head)=(B,true)
    apply Prod.ext
    · rfl
    · change (if c.head+1 = c.head then false else c.tape (c.head+1)) = true
      have hn : c.head+1≠c.head := by omega
      simp [hn,h1]
  have hbraw : rawStep m c1=some c2 := by
    simp [rawStep,hdslot,hB,c2,ba]
  have hr : run m 2 c=some c2 := by
    simp [run,hcraw,hbraw]
  have htape : c2.tape=cbPaint c.tape c.head 1 := by
    funext x
    by_cases hx0 : x=c.head
    · subst x
      simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt]
    · by_cases hx1 : x=c.head+1
      · subst x
        simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt] <;> omega
      · simp [c2,c1,applyMove,ca,ba,cbPaint,writeAt,hx0,hx1] <;> omega
  refine ⟨c2,hr,?_,?_,htape⟩
  · rfl
  · simp [c2,c1,applyMove,ca,ba]
    omega

theorem baseTape_atA (u w : Nat) :
    baseTape u w (-2*(u:Int)-6)=true := by
  have hz := zeroPaint_outside (negFill (jTape u w) u)
      (2*(u:Int)) (2*u+3) (-2*(u:Int)-6) (by omega)
  have hn := negFill_outside (jTape u w) u (-2*(u:Int)-6) (by omega)
  unfold baseTape
  rw [hz,hn]
  have hj : jTape u w (-2*(u:Int)-6)=true := by
    simp [jTape,jMark,jHole]
    omega
  exact hj

theorem baseTape_left_blank (u w : Nat) (x : Int)
    (hx : x < -2*(u:Int)-6) :
    baseTape u w x=false := by
  have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  have hn : ¬negFillTest u x := by
    unfold negFillTest
    omega
  have hj : jTape u w x=false := by
    simp [jTape,jMark,jHole]
    omega
  simp [baseTape,zeroPaint,hz,negFill,hn,hj]

theorem baseTape_odd (u w : Nat) (x : Int)
    (hlo : -2*(u:Int)-6≤x) (hhi : x≤(w:Int)+1)
    (hodd : x%2≠0) :
    baseTape u w x=true := by
  have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  have hn : ¬negFillTest u x := by
    unfold negFillTest
    omega
  have hj : jTape u w x=true := by
    simp [jTape,jMark,jHole]
    omega
  simp [baseTape,zeroPaint,hz,negFill,hn,hj]

theorem baseTape_even_zero (u w : Nat) (x : Int)
    (hlo : -2*(u:Int)-2≤x) (hhi : x≤2*(u:Int))
    (heven : x%2=0) :
    baseTape u w x=false := by
  have hz : zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  simp [baseTape,zeroPaint,hz]

theorem baseTape_right (u w : Nat) (x : Int)
    (hx : 2*(u:Int)+3≤x) :
    baseTape u w x=jTape u w x := by
  have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  have hn : ¬negFillTest u x := by
    unfold negFillTest
    omega
  simp [baseTape,zeroPaint,hz,negFill,hn]

theorem baseTape_right_one (u w : Nat) (hw : 2*u+3≤w)
    (x : Int) (hlo : 2*(u:Int)+1≤x) (hhi : x≤2*(u:Int)+2) :
    baseTape u w x=true := by
  have hb : baseTape u w x=jTape u w x := by
    have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
      unfold zeroTest
      omega
    have hn : ¬negFillTest u x := by
      unfold negFillTest
      omega
    simp [baseTape,zeroPaint,hz,negFill,hn]
  rw [hb]
  simp [jTape,jMark,jHole]
  omega

theorem f0_local (u w : Nat) :
    f0Tape u w (-2*(u:Int)-7)=false ∧
    f0Tape u w (-2*(u:Int)-6)=false ∧
    f0Tape u w (-2*(u:Int)-5)=true ∧
    f0Tape u w (-2*(u:Int)-4)=false ∧
    f0Tape u w (-2*(u:Int)-3)=true ∧
    f0Tape u w (-2*(u:Int)-8)=false ∧
    f0Tape u w (-2*(u:Int)-9)=false := by
  have hblank7 : baseTape u w (-2*(u:Int)-7)=false :=
    baseTape_left_blank u w _ (by omega)
  have hblank8 : baseTape u w (-2*(u:Int)-8)=false :=
    baseTape_left_blank u w _ (by omega)
  have hblank9 : baseTape u w (-2*(u:Int)-9)=false :=
    baseTape_left_blank u w _ (by omega)
  have hodd5 : baseTape u w (-2*(u:Int)-5)=true := by
    apply baseTape_odd u w _ <;> omega
  have heven4 : baseTape u w (-2*(u:Int)-4)=false := by
    have hz : zeroTest (2*(u:Int)) (-2*(u:Int)-4) (2*u+3) := by
      unfold zeroTest
      omega
    have hn : ¬negFillTest u (-2*(u:Int)-4) := by
      unfold negFillTest
      omega
    simp [baseTape,zeroPaint,hz,negFill,hn]
  have hodd3 : baseTape u w (-2*(u:Int)-3)=true := by
    apply baseTape_odd u w _ <;> omega
  unfold f0Tape
  simp [writeAt,hblank7,hblank8,hblank9,hodd5,heven4,hodd3]

theorem j_F0_exact (u w : Nat) (hw : 2*u≤w+1) :
    run target429 (4*u*u+6*u+7)
      {state:=A,head:=0,tape:=jTape u w} =
    some {state:=F,head:=-2*(u:Int)-7,tape:=f0Tape u w} := by
  have hp := j_left_sweep u w hw
  have hb := baseTape_atA u w
  have hprefix : prefix11 (A,true)=some (⟨false,false,F⟩ : Move) := by decide
  have hstep :
      rawStep target429
        {state:=A,head:=-2*(u:Int)-6,tape:=baseTape u w} =
      some {state:=F,head:=-2*(u:Int)-7,tape:=f0Tape u w} := by
    simp [rawStep,readSlot,target429,applyMove,f0Tape,writeAt,hb,hprefix]
  have htime : 4*u*u+6*u+7=(4*u*u+6*u+6)+1 := by omega
  rw [htime,run_add',hp]
  simpa [run,rawStep,readSlot,target429,applyMove,baseTape,f0Tape,writeAt,hb,hprefix] using hstep

/-- The exact fourteen-transition F/0-to-C/1 setup, independent of the
    surrounding tape once the seven queried cells have the displayed bits. -/
theorem f0_to_c1 (h : Int) (t : Int → Bool)
    (h0 : t h=false) (h1 : t (h+1)=false)
    (h2 : t (h+2)=true) (h3 : t (h+3)=false)
    (h4 : t (h+4)=true) (hm1 : t (h-1)=false)
    (hm2 : t (h-2)=false) :
    run target429 14 {state:=F,head:=h,tape:=t} =
      some {state:=C,head:=h+4,tape:=setupTape t h} := by
  let c0 : Config := {state:=F,head:=h,tape:=t}
  let c1 : Config := {state:=D,head:=h+1,tape:=writeAt t h true}
  let c2 : Config := {state:=E,head:=h,tape:=writeAt c1.tape (h+1) true}
  let c3 : Config := {state:=E,head:=h-1,tape:=writeAt c2.tape h true}
  let c4 : Config := {state:=A,head:=h-2,tape:=writeAt c3.tape (h-1) false}
  let c5 : Config := {state:=B,head:=h-1,tape:=writeAt c4.tape (h-2) true}
  let c6 : Config := {state:=C,head:=h,tape:=writeAt c5.tape (h-1) true}
  let c7 : Config := {state:=B,head:=h+1,tape:=writeAt c6.tape h false}
  let c8 : Config := {state:=A,head:=h+2,tape:=writeAt c7.tape (h+1) true}
  let c9 : Config := {state:=F,head:=h+1,tape:=writeAt c8.tape (h+2) false}
  let c10 : Config := {state:=A,head:=h,tape:=writeAt c9.tape (h+1) true}
  let c11 : Config := {state:=B,head:=h+1,tape:=writeAt c10.tape h true}
  let c12 : Config := {state:=A,head:=h+2,tape:=writeAt c11.tape (h+1) true}
  let c13 : Config := {state:=B,head:=h+3,tape:=writeAt c12.tape (h+2) true}
  let c14 : Config := {state:=C,head:=h+4,tape:=writeAt c13.tape (h+3) true}
  have hs0 : readSlot c0=(F,false) := by simp [readSlot,c0,h0]
  have hs1 : readSlot c1=(D,false) := by
    simp [readSlot,c1,writeAt,h1] <;> omega
  have hs2 : readSlot c2=(E,true) := by
    simp [readSlot,c2,c1,writeAt] <;> omega
  have hs3 : readSlot c3=(E,false) := by
    simp [readSlot,c3,c2,c1,writeAt,hm1] <;> omega
  have hs4 : readSlot c4=(A,false) := by
    simp [readSlot,c4,c3,c2,c1,writeAt,hm2] <;> omega
  have hs5 : readSlot c5=(B,false) := by
    simp [readSlot,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs6 : readSlot c6=(C,true) := by
    simp [readSlot,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs7 : readSlot c7=(B,true) := by
    simp [readSlot,c7,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs8 : readSlot c8=(A,true) := by
    simp [readSlot,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h2] <;> omega
  have hs9 : readSlot c9=(F,true) := by
    simp [readSlot,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs10 : readSlot c10=(A,false) := by
    simp [readSlot,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs11 : readSlot c11=(B,true) := by
    simp [readSlot,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs12 : readSlot c12=(A,false) := by
    simp [readSlot,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt] <;> omega
  have hs13 : readSlot c13=(B,false) := by
    simp [readSlot,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h3] <;> omega
  have hs14 : readSlot c14=(C,true) := by
    simp [readSlot,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h4] <;> omega
  have hrow0 : target429 (F,false)=some ⟨true,true,D⟩ := by decide
  have hrow1 : target429 (D,false)=some ⟨true,false,E⟩ := by decide
  have hrow2 : target429 (E,true)=some ⟨true,false,E⟩ := by decide
  have hrow3 : target429 (E,false)=some ⟨false,false,A⟩ := by decide
  have hrow4 : target429 (A,false)=some ⟨true,true,B⟩ := by decide
  have hrow5 : target429 (B,false)=some ⟨true,true,C⟩ := by decide
  have hrow6 : target429 (C,true)=some ⟨false,true,B⟩ := by decide
  have hrow7 : target429 (B,true)=some ⟨true,true,A⟩ := by decide
  have hrow8 : target429 (A,true)=some ⟨false,false,F⟩ := by decide
  have hrow9 : target429 (F,true)=some ⟨true,false,A⟩ := by decide
  have hrow10 : target429 (A,false)=some ⟨true,true,B⟩ := by decide
  have hrow11 : target429 (B,true)=some ⟨true,true,A⟩ := by decide
  have hrow12 : target429 (A,false)=some ⟨true,true,B⟩ := by decide
  have hrow13 : target429 (B,false)=some ⟨true,true,C⟩ := by decide
  have r0 : rawStep target429 c0=some c1 := by
    have hraw := rawStep_of_read target429 c0 F false _ hs0 hrow0
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c0,c1]
      · simp [applyMove,c0,c1] <;> omega
      · funext x
        simp [applyMove,c0,c1,writeAt])
  have r1 : rawStep target429 c1=some c2 := by
    have hraw := rawStep_of_read target429 c1 D false _ hs1 hrow1
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c1,c2]
      · simp [applyMove,c1,c2] <;> omega
      · funext x
        simp [applyMove,c1,c2,writeAt])
  have r2 : rawStep target429 c2=some c3 := by
    have hraw := rawStep_of_read target429 c2 E true _ hs2 hrow2
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c2,c3]
      · simp [applyMove,c2,c3] <;> omega
      · funext x
        simp [applyMove,c2,c3,writeAt])
  have r3 : rawStep target429 c3=some c4 := by
    have hraw := rawStep_of_read target429 c3 E false _ hs3 hrow3
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c3,c4]
      · simp [applyMove,c3,c4] <;> omega
      · funext x
        simp [applyMove,c3,c4,writeAt])
  have r4 : rawStep target429 c4=some c5 := by
    have hraw := rawStep_of_read target429 c4 A false _ hs4 hrow4
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c4,c5]
      · simp [applyMove,c4,c5] <;> omega
      · funext x
        simp [applyMove,c4,c5,writeAt])
  have r5 : rawStep target429 c5=some c6 := by
    have hraw := rawStep_of_read target429 c5 B false _ hs5 hrow5
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c5,c6]
      · simp [applyMove,c5,c6] <;> omega
      · funext x
        simp [applyMove,c5,c6,writeAt])
  have r6 : rawStep target429 c6=some c7 := by
    have hraw := rawStep_of_read target429 c6 C true _ hs6 hrow6
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c6,c7]
      · simp [applyMove,c6,c7] <;> omega
      · funext x
        simp [applyMove,c6,c7,writeAt])
  have r7 : rawStep target429 c7=some c8 := by
    have hraw := rawStep_of_read target429 c7 B true _ hs7 hrow7
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c7,c8]
      · simp [applyMove,c7,c8] <;> omega
      · funext x
        simp [applyMove,c7,c8,writeAt])
  have r8 : rawStep target429 c8=some c9 := by
    have hraw := rawStep_of_read target429 c8 A true _ hs8 hrow8
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c8,c9]
      · simp [applyMove,c8,c9] <;> omega
      · funext x
        simp [applyMove,c8,c9,writeAt])
  have r9 : rawStep target429 c9=some c10 := by
    have hraw := rawStep_of_read target429 c9 F true _ hs9 hrow9
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c9,c10]
      · simp [applyMove,c9,c10] <;> omega
      · funext x
        simp [applyMove,c9,c10,writeAt])
  have r10 : rawStep target429 c10=some c11 := by
    have hraw := rawStep_of_read target429 c10 A false _ hs10 hrow10
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c10,c11]
      · simp [applyMove,c10,c11] <;> omega
      · funext x
        simp [applyMove,c10,c11,writeAt])
  have r11 : rawStep target429 c11=some c12 := by
    have hraw := rawStep_of_read target429 c11 B true _ hs11 hrow11
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c11,c12]
      · simp [applyMove,c11,c12] <;> omega
      · funext x
        simp [applyMove,c11,c12,writeAt])
  have r12 : rawStep target429 c12=some c13 := by
    have hraw := rawStep_of_read target429 c12 A false _ hs12 hrow12
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c12,c13]
      · simp [applyMove,c12,c13] <;> omega
      · funext x
        simp [applyMove,c12,c13,writeAt])
  have r13 : rawStep target429 c13=some c14 := by
    have hraw := rawStep_of_read target429 c13 B false _ hs13 hrow13
    exact hraw.trans (by
      apply congrArg some
      apply config_ext
      · simp [applyMove,c13,c14]
      · simp [applyMove,c13,c14] <;> omega
      · funext x
        simp [applyMove,c13,c14,writeAt])
  have htape : c14.tape=setupTape t h := by
    funext x
    have hcases : x=h-2 ∨ x=h-1 ∨ x=h ∨ x=h+1 ∨ x=h+2 ∨ x=h+3 ∨
        x<h-2 ∨ h+3<x := by omega
    rcases hcases with h0x | h1x | h2x | h3x | h4x | h5x | hleft | hright
    · subst x
      have hinside : h-2≤h-2 ∧ h-2≤h+3 := by omega
      have hneq1 : h-2≠h-1 := by omega
      have hneq2 : h-2≠h := by omega
      have hneq3 : h-2≠h+1 := by omega
      have hneq4 : h-2≠h+2 := by omega
      have hneq5 : h-2≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside,hneq1,hneq2,hneq3,hneq4,hneq5]
    · subst x
      have hinside : h-2≤h-1 ∧ h-1≤h+3 := by omega
      have hneq2 : h-1≠h := by omega
      have hneq3 : h-1≠h+1 := by omega
      have hneq4 : h-1≠h+2 := by omega
      have hneq5 : h-1≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside,hneq2,hneq3,hneq4,hneq5]
    · subst x
      have hinside : h-2≤h ∧ h≤h+3 := by omega
      have hneq3 : h≠h+1 := by omega
      have hneq4 : h≠h+2 := by omega
      have hneq5 : h≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside,hneq3,hneq4,hneq5]
    · subst x
      have hinside : h-2≤h+1 ∧ h+1≤h+3 := by omega
      have hneq4 : h+1≠h+2 := by omega
      have hneq5 : h+1≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside,hneq4,hneq5]
    · subst x
      have hinside : h-2≤h+2 ∧ h+2≤h+3 := by omega
      have hneq5 : h+2≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside,hneq5]
    · subst x
      have hinside : h-2≤h+3 ∧ h+3≤h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hinside]
    · have hout : ¬(h-2≤x ∧ x≤h+3) := by omega
      have hneq0 : x≠h-2 := by omega
      have hneq1 : x≠h-1 := by omega
      have hneq2 : x≠h := by omega
      have hneq3 : x≠h+1 := by omega
      have hneq4 : x≠h+2 := by omega
      have hneq5 : x≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hout,hneq0,hneq1,hneq2,hneq3,hneq4,hneq5]
    · have hout : ¬(h-2≤x ∧ x≤h+3) := by omega
      have hneq0 : x≠h-2 := by omega
      have hneq1 : x≠h-1 := by omega
      have hneq2 : x≠h := by omega
      have hneq3 : x≠h+1 := by omega
      have hneq4 : x≠h+2 := by omega
      have hneq5 : x≠h+3 := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,
        writeAt,setupTape,hout,hneq0,hneq1,hneq2,hneq3,hneq4,hneq5]
  have hrun : run target429 14 c0=some c14 := by
    simp [run,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13]
  have hcfg : c14={state:=C,head:=h+4,tape:=setupTape t h} := by
    apply config_ext
    · rfl
    · rfl
    · exact htape
  simpa [c0] using hrun.trans (congrArg some hcfg)


theorem setupTape_below (t : Int → Bool) (h x : Int)
    (hx : x < h-2) : setupTape t h x = t x := by
  simp [setupTape]
  omega

theorem setupTape_above (t : Int → Bool) (h x : Int)
    (hx : h+3 < x) : setupTape t h x = t x := by
  simp [setupTape]
  omega

theorem f0Tape_neq (u w : Nat) (x : Int)
    (hx : x ≠ -2*(u:Int)-6) : f0Tape u w x = baseTape u w x := by
  simp [f0Tape,writeAt,hx]

/-- The C/B sweep followed by its final exit pair is exactly the translated
    J tape with the new bubble parameter. -/
theorem j_first_branch_tape (u w : Nat) (hw : 2*u+3 ≤ w) :
    cbPaint (setupTape (f0Tape u w) (-2*(u:Int)-7))
      (-2*(u:Int)-3) (2*u+3) =
    jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3) := by
  have hsub : ((w-(2*u+3):Nat):Int) =
      (w:Int) - (2*(u:Int)+3) := by
    rw [Int.ofNat_sub hw]
    omega
  funext x
  by_cases hleft : x < -2*(u:Int)-9
  · have hcb : x < -2*(u:Int)-3 := by omega
    rw [cbPaint_left _ _ _ _ hcb]
    rw [setupTape_below _ _ _ (by omega)]
    rw [f0Tape_neq u w x (by omega)]
    rw [baseTape_left_blank u w x (by omega)]
    have hmark :
        ¬jMark (2*u+3) (w-(2*u+3))
          (x-(2*(u:Int)+3)) := by
      unfold jMark
      intro hm
      rcases hm with ⟨hl,hu,hn⟩ | heq
      · omega
      · rw [hsub] at heq
        omega
    simp [jTapeAt,jTape,hmark]
  · by_cases hmid : x < -2*(u:Int)-3
    · have hcb : x < -2*(u:Int)-3 := hmid
      rw [cbPaint_left _ _ _ _ hcb]
      have hinside :
          -2*(u:Int)-9 ≤ x ∧ x ≤ -2*(u:Int)-4 := by omega
      have hsetup :
          setupTape (f0Tape u w) (-2*(u:Int)-7) x = true := by
        simp only [setupTape]
        have hcond : (-2*(u:Int)-7)-2 ≤ x ∧ x ≤ (-2*(u:Int)-7)+3 := by omega
        simp [hcond]
      rw [hsetup]
      have hnotHole :
          ¬jHole (2*u+3) (x-(2*(u:Int)+3)) := by
        intro hh
        unfold jHole at hh
        omega
      have hmark :
          jMark (2*u+3) (w-(2*u+3))
            (x-(2*(u:Int)+3)) := by
        unfold jMark
        left
        refine ⟨by omega, ?_, hnotHole⟩
        rw [hsub]
        omega
      simp [jTapeAt,jTape,hmark]
    · by_cases hright : x < 2*(u:Int)+3
      · have hlo : -2*(u:Int)-3 ≤ x := by omega
        have hhi : x < -2*(u:Int)-3 + 2*((2*u+3:Int)) := by omega
        have hpar :
            (x-(2*(u:Int)+3))%2 =
              (x-(-2*(u:Int)-3))%2 := by omega
        by_cases heven : (x-(-2*(u:Int)-3))%2=0
        · have hpaint :
              cbPaint (setupTape (f0Tape u w) (-2*(u:Int)-7))
                (-2*(u:Int)-3) (2*u+3) x = false :=
            cbPaint_even _ _ _ _ hlo hhi heven
          rw [hpaint]
          have hhole :
              jHole (2*u+3) (x-(2*(u:Int)+3)) := by
            unfold jHole
            refine ⟨by omega, by omega, ?_⟩
            rw [hpar]
            exact heven
          have hmark :
              ¬jMark (2*u+3) (w-(2*u+3))
                (x-(2*(u:Int)+3)) := by
            unfold jMark
            intro hm
            rcases hm with ⟨hl,hu,hn⟩ | heq
            · exact hn hhole
            · rw [hsub] at heq
              omega
          simp [jTapeAt,jTape,hmark]
        · have hodd : (x-(-2*(u:Int)-3))%2=1 := by omega
          have hpaint :
              cbPaint (setupTape (f0Tape u w) (-2*(u:Int)-7))
                (-2*(u:Int)-3) (2*u+3) x = true :=
            cbPaint_odd _ _ _ _ hlo hhi hodd
          rw [hpaint]
          have hnotHole :
              ¬jHole (2*u+3) (x-(2*(u:Int)+3)) := by
            intro hh
            unfold jHole at hh
            rcases hh with ⟨hl,hu,hp⟩
            rw [hpar] at hp
            omega
          have hmark :
              jMark (2*u+3) (w-(2*u+3))
                (x-(2*(u:Int)+3)) := by
            unfold jMark
            left
            refine ⟨by omega, ?_, hnotHole⟩
            rw [hsub]
            omega
          simp [jTapeAt,jTape,hmark]
      · have hright' : 2*(u:Int)+3 ≤ x := by omega
        have hpaint :
            cbPaint (setupTape (f0Tape u w) (-2*(u:Int)-7))
              (-2*(u:Int)-3) (2*u+3) x =
              setupTape (f0Tape u w) (-2*(u:Int)-7) x :=
          cbPaint_right _ _ _ _ (by
            have hk : (-2*(u:Int)-3)+2*((2*u+3:Int)) =
                2*(u:Int)+3 := by omega
            omega)
        rw [hpaint]
        rw [setupTape_above _ _ _ (by omega)]
        rw [f0Tape_neq u w x (by omega)]
        rw [baseTape_right u w x hright']
        have hholeOld : ¬jHole u x := by
          unfold jHole
          omega
        have hmarkOld :
            jMark u w x ↔ x≤(w:Int)+1 ∨ x=(w:Int)+3 := by
          unfold jMark
          constructor
          · intro hm
            rcases hm with ⟨hl,hu,hn⟩ | heq
            · exact Or.inl hu
            · exact Or.inr heq
          · intro hm
            rcases hm with hu | heq
            · exact Or.inl ⟨by omega,hu,hholeOld⟩
            · exact Or.inr heq
        have hholeNew :
            ¬jHole (2*u+3) (x-(2*(u:Int)+3)) := by
          unfold jHole
          omega
        have hmarkNew :
            jMark (2*u+3) (w-(2*u+3))
              (x-(2*(u:Int)+3)) ↔
              x≤(w:Int)+1 ∨ x=(w:Int)+3 := by
          unfold jMark
          constructor
          · intro hm
            rcases hm with ⟨hl,hu,hn⟩ | heq
            · left
              rw [hsub] at hu
              omega
            · right
              rw [hsub] at heq
              omega
          · intro hm
            rcases hm with hu | heq
            · left
              refine ⟨by omega, ?_, hholeNew⟩
              rw [hsub]
              omega
            · right
              rw [hsub]
              omega
        simp [jTapeAt,jTape,hmarkOld,hmarkNew]

/-- Exact original-source primitive-step realization of the first J branch. -/
theorem j_first_branch (u w : Nat) (hw : 2*u+3 ≤ w) :
    run target429 (4*u*u+10*u+27)
      {state:=A,head:=0,tape:=jTape u w} =
    some (Config.mk A (2*(u:Int)+3)
      (jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3))) := by
  have hprefix : 2*u ≤ w+1 := by omega
  rcases f0_local u w with ⟨h0,h1,h2,h3,h4,hm1,hm2⟩
  have hsetup := f0_to_c1 (-2*(u:Int)-7) (f0Tape u w)
    h0
    (by
      rw [show (-2*(u:Int)-7)+1 = -2*(u:Int)-6 by omega]
      exact h1)
    (by
      rw [show (-2*(u:Int)-7)+2 = -2*(u:Int)-5 by omega]
      exact h2)
    (by
      rw [show (-2*(u:Int)-7)+3 = -2*(u:Int)-4 by omega]
      exact h3)
    (by
      rw [show (-2*(u:Int)-7)+4 = -2*(u:Int)-3 by omega]
      exact h4)
    (by
      rw [show (-2*(u:Int)-7)-1 = -2*(u:Int)-8 by omega]
      exact hm1)
    (by
      rw [show (-2*(u:Int)-7)-2 = -2*(u:Int)-9 by omega]
      exact hm2)
  let c0 : Config := {state:=A,head:=0,tape:=jTape u w}
  let c1 : Config :=
    {state:=C,head:=-2*(u:Int)-3,
      tape:=setupTape (f0Tape u w) (-2*(u:Int)-7)}
  have hfirst :
      run target429 (4*u*u+6*u+7+14) c0 = some c1 := by
    rw [run_add', j_F0_exact u w hprefix]
    simp only [Option.bind_some]
    rw [show (-2*(u:Int)-7)+4 = -2*(u:Int)-3 by omega] at hsetup
    simpa [c1] using hsetup
  have hCrow : target429 (C,true)=some ⟨false,true,B⟩ := by decide
  have hBzero : target429 (B,false)=some ⟨true,true,C⟩ := by decide
  have hBone : target429 (B,true)=some ⟨true,true,A⟩ := by decide
  let k : Nat := 2*u+2
  have hpair : ∀ i : Nat, i<k →
      c1.tape (c1.head+2*(i:Int))=true ∧
      c1.tape (c1.head+2*(i:Int)+1)=false := by
    intro i hi
    have hx0 : -2*(u:Int)-3 ≤
        -2*(u:Int)-3+2*(i:Int) := by omega
    have hx0hi : -2*(u:Int)-3+2*(i:Int) ≤ 2*(u:Int)+1 := by
      dsimp [k] at hi
      omega
    have hx1 : -2*(u:Int)-2 ≤
        -2*(u:Int)-3+2*(i:Int)+1 := by omega
    have hx1hi : -2*(u:Int)-3+2*(i:Int)+1 ≤ 2*(u:Int) := by
      dsimp [k] at hi
      omega
    have h0' :
        setupTape (f0Tape u w) (-2*(u:Int)-7)
          (-2*(u:Int)-3+2*(i:Int)) = true := by
      rw [setupTape_above _ _ _ (by omega)]
      rw [f0Tape_neq u w _ (by omega)]
      exact baseTape_odd u w _ (by omega) (by omega) (by omega)
    have h1' :
        setupTape (f0Tape u w) (-2*(u:Int)-7)
          (-2*(u:Int)-3+2*(i:Int)+1) = false := by
      rw [setupTape_above _ _ _ (by omega)]
      rw [f0Tape_neq u w _ (by omega)]
      exact baseTape_even_zero u w _ (by omega) (by omega) (by omega)
    constructor
    · simpa [c1] using h0'
    · simpa [c1] using h1'
  obtain ⟨c2,hsweep,hs2,hh2,ht2⟩ :=
    bc_sweep target429 k c1 hCrow hBzero (by simp [c1]) hpair
  have hhead2 : c2.head=2*(u:Int)+1 := by
    have h := hh2
    dsimp [c1,k] at h
    omega
  have htail : ∀ x : Int, 2*(u:Int)+1≤x → x≤2*(u:Int)+2 →
      c1.tape x=true := by
    intro x hx0 hx1
    change setupTape (f0Tape u w) (-2*(u:Int)-7) x=true
    rw [setupTape_above _ _ _ (by omega)]
    rw [f0Tape_neq u w x (by omega)]
    exact baseTape_right_one u w hw x (by omega) (by omega)
  have hzeroAt : c2.tape c2.head=true := by
    rw [ht2,hh2]
    rw [cbPaint_right c1.tape c1.head k
      (c1.head+2*(k:Int)) (by omega)]
    apply htail
    · dsimp [c1,k]
      omega
    · dsimp [c1,k]
      omega
  have honeAt : c2.tape (c2.head+1)=true := by
    rw [ht2,hh2]
    rw [cbPaint_right c1.tape c1.head k
      (c1.head+2*(k:Int)+1) (by omega)]
    apply htail
    · dsimp [c1,k]
      omega
    · dsimp [c1,k]
      omega
  obtain ⟨c3,hexit,hs3,hh3,ht3⟩ :=
    cb_exit target429 c2 hCrow hBone hs2 hzeroAt honeAt
  have hhead3 : c3.head=2*(u:Int)+3 := by
    rw [hh3,hhead2]
    omega
  have htape3 :
      c3.tape =
        jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3) := by
    calc
      c3.tape = cbPaint c2.tape c2.head 1 := ht3
      _ = cbPaint (cbPaint c1.tape c1.head k)
            (c1.head+2*(k:Int)) 1 := by rw [ht2,hh2]
      _ = cbPaint c1.tape c1.head (Nat.succ k) :=
        cbPaint_compose_right c1.tape c1.head k
      _ = jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3) := by
        simpa [c1,k] using j_first_branch_tape u w hw
  have hcfg : c3 =
      Config.mk A (2*(u:Int)+3)
        (jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)) := by
    apply config_ext
    · exact hs3
    · exact hhead3
    · exact htape3
  have htime :
      4*u*u+10*u+27 =
        (4*u*u+6*u+7+14)+(2*k+2) := by
    dsimp [k]
    omega
  have htotal :
      run target429 (4*u*u+10*u+27) c0 = some c3 := by
    rw [htime,run_add',hfirst]
    simp only [Option.bind_some]
    rw [run_add',hsweep]
    simp only [Option.bind_some]
    exact hexit
  exact htotal.trans (congrArg some hcfg)

#print axioms f0_local
#print axioms j_F0_exact
#print axioms f0_to_c1
#print axioms cb_sweep
#print axioms cb_exit
#print axioms j_first_branch_tape
#print axioms j_first_branch
end BB429JFirstBranch
