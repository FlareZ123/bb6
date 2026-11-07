import JF0Prefix
import BCFuture
import Lean.Elab.Tactic.Omega

namespace BB429JFirstBranch
open BB6Coverage BB6Bubble BB6BCFuture BB429PhysicalFrontier BB429JPhysical

def D : Fin 6 := ⟨3, by decide⟩
def E : Fin 6 := ⟨4, by decide⟩

def writeAt (t : Int → Bool) (x : Int) (b : Bool) : Int → Bool :=
  fun y => if y = x then b else t y

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
      have hzero : c.tape c.head=true := (hpair 0 (by omega)).1
      have hone : c.tape (c.head+1)=false := (hpair 0 (by omega)).2
      obtain ⟨d1,hr1,hs1,hd1,ht1⟩ := bc_two_full m c hC hB hs hzero hone
      have hpair' : ∀ i : Nat, i<k →
          d1.tape (d1.head+2*(i:Int))=true ∧
          d1.tape (d1.head+2*(i:Int)+1)=false := by
        intro i hi
        have h0 : d1.tape (d1.head+2*(i:Int)) =
            c.tape (c.head+2*(i:Int)+2) := by
          rw [ht1,hd1]
          rw [cbPaint_right c.tape c.head 1 (c.head+2*(i:Int)+2) (by omega)]
          rfl
        have h1 : d1.tape (d1.head+2*(i:Int)+1) =
            c.tape (c.head+2*(i:Int)+3) := by
          rw [ht1,hd1]
          rw [cbPaint_right c.tape c.head 1 (c.head+2*(i:Int)+3) (by omega)]
          rfl
        have hp := hpair (i+1) (by omega)
        constructor
        · simpa [show (i+1:Int) = (i:Int)+1 by omega, Int.add_assoc,
            Int.add_left_comm, Int.add_comm] using hp.1
        · simpa [show (i+1:Int) = (i:Int)+1 by omega, Int.add_assoc,
            Int.add_left_comm, Int.add_comm] using hp.2
      obtain ⟨d,hr2,hs2,hd2,ht2⟩ := ih d1 hpair'
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

lemma baseTape_atA (u w : Nat) :
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

lemma baseTape_left_blank (u w : Nat) (x : Int)
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

lemma baseTape_odd (u w : Nat) (x : Int)
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

lemma baseTape_even_zero (u w : Nat) (x : Int)
    (hlo : -2*(u:Int)-2≤x) (hhi : x≤2*(u:Int))
    (heven : x%2=0) :
    baseTape u w x=false := by
  have hz : zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  simp [baseTape,zeroPaint,hz]

lemma baseTape_right (u w : Nat) (x : Int)
    (hx : 2*(u:Int)+3≤x) :
    baseTape u w x=jTape u w x := by
  have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  have hn : ¬negFillTest u x := by
    unfold negFillTest
    omega
  simp [baseTape,zeroPaint,hz,negFill,hn]

lemma baseTape_right_one (u w : Nat) (hw : 2*u+3≤w)
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

lemma f0_local (u w : Nat) :
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
    apply baseTape_even_zero u w <;> simp
    omega
  have hodd3 : baseTape u w (-2*(u:Int)-3)=true := by
    apply baseTape_odd u w _ <;> omega
  unfold f0Tape
  simp [writeAt,hblank7,hblank8,hblank9,hodd5,heven4,hodd3]
  omega

theorem j_F0_exact (u w : Nat) (hw : 2*u≤w+1) :
    run target429 (4*u*u+6*u+7)
      {state:=A,head:=0,tape:=jTape u w} =
    some {state:=F,head:=-2*(u:Int)-7,tape:=f0Tape u w} := by
  have hp := j_left_sweep u w hw
  have hb := baseTape_atA u w
  have hstep :
      rawStep target429
        {state:=A,head:=-2*(u:Int)-6,tape:=baseTape u w} =
      some {state:=F,head:=-2*(u:Int)-7,tape:=f0Tape u w} := by
    simp [rawStep,readSlot,target429,applyMove,f0Tape,writeAt,hb]
  have htime : 4*u*u+6*u+7=(4*u*u+6*u+6)+1 := by omega
  rw [htime,run_add',hp]
  simp [hstep]

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
    simp [readSlot,c1,writeAt,h1]
  have hs2 : readSlot c2=(E,true) := by
    simp [readSlot,c2,c1,writeAt]
  have hs3 : readSlot c3=(E,false) := by
    simp [readSlot,c3,c2,c1,writeAt,hm1]
  have hs4 : readSlot c4=(A,false) := by
    simp [readSlot,c4,c3,c2,c1,writeAt,hm2]
  have hs5 : readSlot c5=(B,false) := by
    simp [readSlot,c5,c4,c3,c2,c1,writeAt]
  have hs6 : readSlot c6=(C,true) := by
    simp [readSlot,c6,c5,c4,c3,c2,c1,writeAt]
  have hs7 : readSlot c7=(B,true) := by
    simp [readSlot,c7,c6,c5,c4,c3,c2,c1,writeAt]
  have hs8 : readSlot c8=(A,true) := by
    simp [readSlot,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h2]
  have hs9 : readSlot c9=(F,true) := by
    simp [readSlot,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt]
  have hs10 : readSlot c10=(A,false) := by
    simp [readSlot,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt]
  have hs11 : readSlot c11=(B,true) := by
    simp [readSlot,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt]
  have hs12 : readSlot c12=(A,false) := by
    simp [readSlot,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt]
  have hs13 : readSlot c13=(B,false) := by
    simp [readSlot,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h3]
  have hs14 : readSlot c14=(C,true) := by
    simp [readSlot,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,writeAt,h4]
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
    simpa [c1,c0,applyMove,writeAt] using rawStep_of_read target429 c0 F false _ hs0 hrow0
  have r1 : rawStep target429 c1=some c2 := by
    simpa [c2,c1,applyMove,writeAt] using rawStep_of_read target429 c1 D false _ hs1 hrow1
  have r2 : rawStep target429 c2=some c3 := by
    simpa [c3,c2,applyMove,writeAt] using rawStep_of_read target429 c2 E true _ hs2 hrow2
  have r3 : rawStep target429 c3=some c4 := by
    simpa [c4,c3,applyMove,writeAt] using rawStep_of_read target429 c3 E false _ hs3 hrow3
  have r4 : rawStep target429 c4=some c5 := by
    simpa [c5,c4,applyMove,writeAt] using rawStep_of_read target429 c4 A false _ hs4 hrow4
  have r5 : rawStep target429 c5=some c6 := by
    simpa [c6,c5,applyMove,writeAt] using rawStep_of_read target429 c5 B false _ hs5 hrow5
  have r6 : rawStep target429 c6=some c7 := by
    simpa [c7,c6,applyMove,writeAt] using rawStep_of_read target429 c6 C true _ hs6 hrow6
  have r7 : rawStep target429 c7=some c8 := by
    simpa [c8,c7,applyMove,writeAt] using rawStep_of_read target429 c7 B true _ hs7 hrow7
  have r8 : rawStep target429 c8=some c9 := by
    simpa [c9,c8,applyMove,writeAt] using rawStep_of_read target429 c8 A true _ hs8 hrow8
  have r9 : rawStep target429 c9=some c10 := by
    simpa [c10,c9,applyMove,writeAt] using rawStep_of_read target429 c9 F true _ hs9 hrow9
  have r10 : rawStep target429 c10=some c11 := by
    simpa [c11,c10,applyMove,writeAt] using rawStep_of_read target429 c10 A false _ hs10 hrow10
  have r11 : rawStep target429 c11=some c12 := by
    simpa [c12,c11,applyMove,writeAt] using rawStep_of_read target429 c11 B true _ hs11 hrow11
  have r12 : rawStep target429 c12=some c13 := by
    simpa [c13,c12,applyMove,writeAt] using rawStep_of_read target429 c12 A false _ hs12 hrow12
  have r13 : rawStep target429 c13=some c14 := by
    simpa [c14,c13,applyMove,writeAt] using rawStep_of_read target429 c13 B false _ hs13 hrow13
  have hrun : run target429 14 c0=some c14 := by
    simp [run,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13]
  have htape : c14.tape=setupTape t h := by
    funext x
    have hcases : x=h-2 ∨ x=h-1 ∨ x=h ∨ x=h+1 ∨ x=h+2 ∨ x=h+3 ∨
        x<h-2 ∨ h+3<x := by omega
    rcases hcases with h0x | h1x | h2x | h3x | h4x | h5x | hleft | hright
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · subst x
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,writeAt,setupTape]
    · have hout : ¬(h-2≤x ∧ x≤h+3) := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,
        writeAt,setupTape,hout] <;> omega
    · have hout : ¬(h-2≤x ∧ x≤h+3) := by omega
      simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,c0,
        writeAt,setupTape,hout] <;> omega
  have hcfg : c14 = {state:=C,head:=h+4,tape:=setupTape t h} := by
    ext
    · rfl
    · rfl
    · exact htape
  simpa [c0,hcfg] using hrun

def firstBranchTape (u w : Nat) (x : Int) : Bool :=
  if x < -2*(u:Int)-9 then false
  else if x < -2*(u:Int)-3 then true
  else if x < 2*(u:Int)+3 then decide (x%2=0)
  else jTape u w x

lemma cCfg_tape_left_blank (u w : Nat) (x : Int)
    (hx : x < -2*(u:Int)-9) :
    setupTape (f0Tape u w) (-2*(u:Int)-7) x=false := by
  have hout : ¬(-2*(u:Int)-9 ≤ x ∧ x ≤ -2*(u:Int)-4) := by omega
  have hbase : baseTape u w x=false :=
    baseTape_left_blank u w x (by omega)
  have hne : x≠-2*(u:Int)-6 := by omega
  simp [setupTape,f0Tape,writeAt,hout,hne,hbase]

lemma cCfg_tape_left_ones (u w : Nat) (x : Int)
    (hlo : -2*(u:Int)-9≤x) (hhi : x < -2*(u:Int)-3) :
    setupTape (f0Tape u w) (-2*(u:Int)-7) x=true := by
  have hrange : -2*(u:Int)-9 ≤ x ∧ x ≤ -2*(u:Int)-4 := by omega
  simp [setupTape,hrange]

lemma cCfg_tape_right (u w : Nat) (x : Int)
    (hx : -2*(u:Int)-3 ≤ x) :
    setupTape (f0Tape u w) (-2*(u:Int)-7) x=baseTape u w x := by
  have hout : ¬(-2*(u:Int)-9 ≤ x ∧ x ≤ -2*(u:Int)-4) := by omega
  have hne : x≠-2*(u:Int)-6 := by omega
  simp [setupTape,f0Tape,writeAt,hout,hne]

lemma firstBranchTape_eq_jTapeAt (u w : Nat) (hw : 2*u+3≤w) :
    firstBranchTape u w =
      jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3) := by
  funext x
  by_cases hx0 : x < -2*(u:Int)-9
  · simp [firstBranchTape,jTapeAt,jTape,jMark,jHole,hx0]
    omega
  · by_cases hx1 : x < -2*(u:Int)-3
    · simp [firstBranchTape,jTapeAt,jTape,jMark,jHole,hx0,hx1]
      omega
    · by_cases hx2 : x < 2*(u:Int)+3
      · simp [firstBranchTape,jTapeAt,jTape,jMark,jHole,hx0,hx1,hx2]
        omega
      · simp [firstBranchTape,jTapeAt,jTape,jMark,jHole,hx0,hx1,hx2]
        omega

/-- Exact raw primitive-step realization of the high-level first branch
    J(u,w) -> J(2u+3,w-2u-3), including its complete two-sided tape. -/
theorem j_first_branch (u w : Nat) (hw : 2*u+3≤w) :
    run target429 (4*u*u+10*u+27)
      {state:=A,head:=0,tape:=jTape u w} =
    some {state:=A,head:=2*(u:Int)+3,
      tape:=jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)} := by
  let hF : Int := -2*(u:Int)-7
  let hC : Int := -2*(u:Int)-3
  let k : Nat := 2*u+2
  let cC : Config :=
    {state:=C,head:=hC,tape:=setupTape (f0Tape u w) hF}
  have hw' : 2*u≤w+1 := by omega
  have hF0 := j_F0_exact u w hw'
  have hlocal := f0_local u w
  have hsetup := f0_to_c1 hF (f0Tape u w)
      (by simpa [hF] using hlocal.1)
      (by simpa [hF] using hlocal.2.1)
      (by simpa [hF] using hlocal.2.2.1)
      (by simpa [hF] using hlocal.2.2.2.1)
      (by simpa [hF] using hlocal.2.2.2.2.1)
      (by simpa [hF] using hlocal.2.2.2.2.2.1)
      (by simpa [hF] using hlocal.2.2.2.2.2.2)
  have hC1 : target429 (C,true)=some ⟨false,true,B⟩ := by decide
  have hB0 : target429 (B,false)=some ⟨true,true,C⟩ := by decide
  have hB1 : target429 (B,true)=some ⟨true,true,A⟩ := by decide
  have hpair : ∀ i : Nat, i<k →
      cC.tape (cC.head+2*(i:Int))=true ∧
      cC.tape (cC.head+2*(i:Int)+1)=false := by
    intro i hi
    have hx0lo : -2*(u:Int)-6 ≤ cC.head+2*(i:Int) := by
      simp [cC,hC]
      omega
    have hx0hi : cC.head+2*(i:Int) ≤ 2*(u:Int)-1 := by
      simp [cC,hC,k] at *
      omega
    have hx1lo : -2*(u:Int)-2 ≤ cC.head+2*(i:Int)+1 := by
      simp [cC,hC]
      omega
    have hx1hi : cC.head+2*(i:Int)+1 ≤ 2*(u:Int) := by
      simp [cC,hC,k] at *
      omega
    have hodd : (cC.head+2*(i:Int))%2≠0 := by
      simp [cC,hC]
      omega
    have heven : (cC.head+2*(i:Int)+1)%2=0 := by
      simp [cC,hC]
      omega
    rw [cCfg_tape_right u w _ (by simp [cC,hC]; omega)]
    rw [cCfg_tape_right u w _ (by simp [cC,hC]; omega)]
    constructor
    · exact baseTape_odd u w _ hx0lo (by omega) hodd
    · exact baseTape_even_zero u w _ hx1lo hx1hi heven
  obtain ⟨cE,hSweep,hsE,hhE,htE⟩ :=
    bc_sweep target429 k cC hC1 hB0 rfl hpair
  have hheadE : cE.head=2*(u:Int)+1 := by
    rw [hhE]
    simp [cC,hC,k]
    omega
  have hE0 : cE.tape cE.head=true := by
    rw [htE,hheadE]
    rw [cbPaint_right cC.tape cC.head k (2*(u:Int)+1) (by simp [cC,hC,k]; omega)]
    rw [cCfg_tape_right u w _ (by simp [cC,hC]; omega)]
    exact baseTape_right_one u w hw _ (by omega) (by omega)
  have hE1 : cE.tape (cE.head+1)=true := by
    rw [htE,hheadE]
    rw [cbPaint_right cC.tape cC.head k (2*(u:Int)+2) (by simp [cC,hC,k]; omega)]
    rw [cCfg_tape_right u w _ (by simp [cC,hC]; omega)]
    exact baseTape_right_one u w hw _ (by omega) (by omega)
  obtain ⟨cFinal,hExit,hsFinal,hhFinal,htFinal⟩ :=
    cb_exit target429 cE hC1 hB1 hsE hE0 hE1
  have htime : 4*u*u+10*u+27 =
      (4*u*u+6*u+7) + (14 + (2*k+2)) := by
    simp [k]
    omega
  have hrunTail : run target429 (14+(2*k+2)) cC=some cFinal := by
    rw [run_add',hsetup]
    simp only [Option.bind_some]
    rw [run_add',hSweep]
    simp only [Option.bind_some]
    exact hExit
  rw [htime,run_add',hF0]
  simp only [Option.bind_some]
  rw [hrunTail]
  have hheadFinal : cFinal.head=2*(u:Int)+3 := by
    rw [hhFinal,hheadE]
    omega
  have hcompose : cFinal.tape =
      cbPaint cC.tape cC.head (k+1) := by
    calc
      cFinal.tape = cbPaint cE.tape cE.head 1 := htFinal
      _ = cbPaint (cbPaint cC.tape cC.head k) (cC.head+2*(k:Int)) 1 := by
        rw [htE,hhE]
      _ = cbPaint cC.tape cC.head (k+1) := by
        simpa using cbPaint_compose_right cC.tape cC.head k
  have hprofile : cFinal.tape=firstBranchTape u w := by
    rw [hcompose]
    funext x
    by_cases hx0 : x < -2*(u:Int)-9
    · have hc := cCfg_tape_left_blank u w x hx0
      have hleft : x<cC.head := by simp [cC,hC]; omega
      simp [firstBranchTape,cbPaint_left cC.tape cC.head (k+1) x hleft,
        cC,hC,hx0,hc]
    · by_cases hx1 : x < -2*(u:Int)-3
      · have hc := cCfg_tape_left_ones u w x (by omega) hx1
        have hleft : x<cC.head := by simp [cC,hC]; omega
        simp [firstBranchTape,cbPaint_left cC.tape cC.head (k+1) x hleft,
          cC,hC,hx0,hx1,hc]
      · by_cases hx2 : x < 2*(u:Int)+3
        · by_cases heven : x%2=0
          · have hoff : (x-cC.head)%2=1 := by
              simp [cC,hC]
              omega
            have hpaint : cbPaint cC.tape cC.head (k+1) x=true := by
              apply cbPaint_odd cC.tape cC.head (k+1) x
              · simp [cC,hC]
                omega
              · simp [cC,hC,k]
                omega
              · exact hoff
            simp [firstBranchTape,cC,hC,k,hx0,hx1,hx2,heven,hpaint]
          · have hoff : (x-cC.head)%2=0 := by
              simp [cC,hC]
              omega
            have hpaint : cbPaint cC.tape cC.head (k+1) x=false := by
              apply cbPaint_even cC.tape cC.head (k+1) x
              · simp [cC,hC]
                omega
              · simp [cC,hC,k]
                omega
              · exact hoff
            simp [firstBranchTape,cC,hC,k,hx0,hx1,hx2,heven,hpaint]
        · have hright : cC.head+2*((k+1):Int) ≤ x := by
            simp [cC,hC,k]
            omega
          have hc := cCfg_tape_right u w x (by simp [cC,hC]; omega)
          have hb := baseTape_right u w x (by omega)
          simp [firstBranchTape,cbPaint_right cC.tape cC.head (k+1) x hright,
            cC,hC,hx0,hx1,hx2,hc,hb]
  have hfinal : cFinal =
      {state:=A,head:=2*(u:Int)+3,
        tape:=jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)} := by
    apply Config.ext
    · exact hsFinal
    · exact hheadFinal
    · exact hprofile.trans (firstBranchTape_eq_jTapeAt u w hw)
  simpa [hfinal] using (show run target429 (4*u*u+10*u+27)
      {state:=A,head:=0,tape:=jTape u w}=some cFinal from by
        rw [htime,run_add',hF0]
        simp only [Option.bind_some]
        exact hrunTail)

#print axioms j_first_branch
end BB429JFirstBranch
