import WindowR4
import Lean.Elab.Tactic.Omega
namespace BB429D0Window
open BB6Coverage BB429PhysicalFrontier BB429WindowR4

private def A : Fin 6 := ⟨0, by decide⟩
private def B : Fin 6 := ⟨1, by decide⟩
private def C : Fin 6 := ⟨2, by decide⟩
private def D : Fin 6 := ⟨3, by decide⟩
private def F : Fin 6 := ⟨5, by decide⟩

private theorem state_cases (q : Fin 6) :
    q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
  have h := q.isLt
  omega

private theorem incomingD (s : Slot) (t : Move)
    (hs : target429 s = some t) (hn : t.next = D) :
    s = (C,false) ∨ s=(F,false) := by
  rcases s with ⟨q,b⟩
  rcases state_cases q with h|h|h|h|h|h <;> subst q <;> cases b <;>
    simp [target429,prefix11,prefix10,prefix9,prefix8,prefix7,prefix6,
      prefix5,prefix4,prefix3,prefix2,prefix1,prefix0,refine,emptyTable]
      at hs <;> cases hs <;> simp_all [A,B,C,D,F]

private theorem incomingC (s : Slot) (t : Move)
    (hs : target429 s = some t) (hn : t.next = C) :
    s = (B,false) := by
  rcases s with ⟨q,b⟩
  rcases state_cases q with h|h|h|h|h|h <;> subst q <;> cases b <;>
    simp [target429,prefix11,prefix10,prefix9,prefix8,prefix7,prefix6,
      prefix5,prefix4,prefix3,prefix2,prefix1,prefix0,refine,emptyTable]
      at hs <;> cases hs <;> simp_all [A,B,C,D,F]

private theorem incomingB (s : Slot) (t : Move)
    (hs : target429 s = some t) (hn : t.next = B) :
    s = (A,false) ∨ s=(C,true) := by
  rcases s with ⟨q,b⟩
  rcases state_cases q with h|h|h|h|h|h <;> subst q <;> cases b <;>
    simp [target429,prefix11,prefix10,prefix9,prefix8,prefix7,prefix6,
      prefix5,prefix4,prefix3,prefix2,prefix1,prefix0,refine,emptyTable]
      at hs <;> cases hs <;> simp_all [A,B,C,D,F]

theorem pred (n:Nat) (c:Config)
    (hr : run target429 (n+1) blank = some c) :
    ∃ d t, run target429 n blank = some d ∧
      target429 (readSlot d) = some t ∧ c=applyMove d t := by
  cases hp : run target429 n blank with
  | none => simp [run,hp] at hr
  | some d =>
      cases hm : target429 (readSlot d) with
      | none => simp [run,hp,rawStep,hm] at hr
      | some t =>
          refine ⟨d,t,?_,?_,?_⟩
          · rfl
          · exact hm
          · simpa [run,hp,rawStep,hm] using hr.symm

private theorem noninitial_pred (n:Nat) (c:Config)
    (hr: run target429 n blank = some c)
    (hnot: c.state ≠ A) :
    ∃ k d t, n=k+1 ∧ run target429 k blank=some d ∧
      target429 (readSlot d)=some t ∧ c=applyMove d t := by
  cases n with
  | zero =>
      have hc : c=blank := by simpa [run] using hr.symm
      subst c
      simp [A,blank] at hnot
  | succ k =>
      obtain ⟨d,t,hd,ht,hc⟩ := pred k c hr
      exact ⟨k,d,t,rfl,hd,ht,hc⟩

private theorem C_pred_B0 (n:Nat) (c:Config)
    (hr: run target429 n blank=some c)
    (hstate: c.state=C) :
    ∃ k d, n=k+1 ∧ run target429 k blank=some d ∧
      readSlot d=(B,false) ∧
      c=applyMove d ⟨true,true,C⟩ := by
  obtain ⟨k,d,t,hn,hd,ht,hc⟩ := noninitial_pred n c hr (by
    intro h; have h0 : C=A := hstate.symm.trans h; exact (by decide : C ≠ A) h0)
  have hnstate : t.next=C := by rw [hc] at hstate; exact hstate
  have hslot : readSlot d=(B,false) := incomingC (readSlot d) t ht hnstate
  have htable : target429 (B,false) = some ⟨true,true,C⟩ := by decide
  have hmv : t=⟨true,true,C⟩ := by
    rw [hslot,htable] at ht
    exact Option.some.inj ht.symm
  rw [hmv] at hc
  exact ⟨k,d,hn,hd,hslot,hc⟩

private theorem right_last_write (d:Config) (w:Bool) (s:Fin 6) :
    (applyMove d ⟨w,true,s⟩).tape
      ((applyMove d ⟨w,true,s⟩).head-1) = w := by
  simp [applyMove,Int.sub_eq_add_neg,Int.add_assoc]

private theorem D0_left_zero_pred_C0 (n:Nat) (c:Config)
    (hr:run target429 n blank=some c)
    (hstate:c.state=D) (hleft:c.tape (c.head-1)=false) :
    ∃ k d, n=k+1 ∧ run target429 k blank=some d ∧
      readSlot d=(C,false) ∧
      c=applyMove d ⟨false,true,D⟩ := by
  obtain ⟨k,d,t,hn,hd,ht,hc⟩ := noninitial_pred n c hr (by
    intro h; have h0 : D=A := hstate.symm.trans h; exact (by decide : D ≠ A) h0)
  have hnext : t.next=D := by rw [hc] at hstate; exact hstate
  rcases incomingD (readSlot d) t ht hnext with hslot|hslot
  · have htable : target429 (C,false)=some ⟨false,true,D⟩ := by decide
    have hmv : t=⟨false,true,D⟩ := by
      rw [hslot,htable] at ht
      exact Option.some.inj ht.symm
    rw [hmv] at hc
    exact ⟨k,d,hn,hd,hslot,hc⟩
  · have htable : target429 (F,false)=some ⟨true,true,D⟩ := by decide
    have hmv : t=⟨true,true,D⟩ := by
      rw [hslot,htable] at ht
      exact Option.some.inj ht.symm
    have hb : c.tape (c.head-1)=true := by
      rw [hc,hmv]
      exact right_last_write d true D
    simp [hb] at hleft

private theorem B0_left_one_pred_A0 (n:Nat) (c:Config)
    (hr:run target429 n blank=some c)
    (hstate:c.state=B) (hleft:c.tape (c.head-1)=true) :
    ∃ k d, n=k+1 ∧ run target429 k blank=some d ∧
      readSlot d=(A,false) ∧
      c=applyMove d ⟨true,true,B⟩ := by
  obtain ⟨k,d,t,hn,hd,ht,hc⟩ := noninitial_pred n c hr (by
    intro h; have h0 : B=A := hstate.symm.trans h; exact (by decide : B ≠ A) h0)
  have hnext : t.next=B := by rw [hc] at hstate; exact hstate
  rcases incomingB (readSlot d) t ht hnext with hslot|hslot
  · have htable : target429 (A,false)=some ⟨true,true,B⟩ := by decide
    have hmv : t=⟨true,true,B⟩ := by
      rw [hslot,htable] at ht
      exact Option.some.inj ht.symm
    rw [hmv] at hc
    exact ⟨k,d,hn,hd,hslot,hc⟩
  · have htable : target429 (C,true)=some ⟨false,true,B⟩ := by decide
    have hmv : t=⟨false,true,B⟩ := by
      rw [hslot,htable] at ht
      exact Option.some.inj ht.symm
    have hb : c.tape (c.head-1)=false := by
      rw [hc,hmv]
      exact right_last_write d false B
    simp [hb] at hleft

private theorem right_move_unchanged (d : Config) (w : Bool) (st : Fin 6)
    (x : Int) (hx : x ≠ d.head) :
    (applyMove d ⟨w,true,st⟩).tape x = d.tape x := by
  simp [applyMove,hx]

/-- All genuine D/0 scans have a nontrivial left-tape restriction: the
five symbols at offsets -1,-2,-3,-4,-6 cannot be 0,1,1,1,0. -/
theorem D0_prefix_forbidden (n : Nat) (c : Config)
    (hr : run target429 n blank = some c)
    (hs : c.state=D)
    (hD0 : c.tape c.head = false)
    (hl1 : c.tape (c.head-1)=false)
    (hl3 : c.tape (c.head-3)=true)
    (hl4 : c.tape (c.head-4)=true)
    (hl6 : c.tape (c.head-6)=false) : False := by
  obtain ⟨kC,dC,_,hRunC,hCslot,hcC⟩ := D0_left_zero_pred_C0 n c hr hs hl1
  have hCstate : dC.state=C := by simpa [readSlot] using congrArg Prod.fst hCslot
  obtain ⟨kB,dB,_,hRunB,hBslot,hcB⟩ := C_pred_B0 kC dC hRunC hCstate
  have hBstate : dB.state=B := by simpa [readSlot] using congrArg Prod.fst hBslot
  have hCpos : c.head=dC.head+1 := by simp [hcC,applyMove]
  have hBpos : dC.head=dB.head+1 := by simp [hcB,applyMove]
  have hdropC (x:Int) (hx:x≠dC.head): c.tape x=dC.tape x := by
    rw [hcC]; exact right_move_unchanged dC false D x hx
  have hdropB (x:Int) (hx:x≠dB.head): dC.tape x=dB.tape x := by
    rw [hcB]; exact right_move_unchanged dB true C x hx
  have hleftB : dB.tape (dB.head-1)=true := by
    calc
      dB.tape (dB.head-1) = dC.tape (dB.head-1) := (hdropB _ (by omega)).symm
      _ = c.tape (dB.head-1) := (hdropC _ (by omega)).symm
      _ = true := by
        have hpos : dB.head-1=c.head-3 := by omega
        rw [hpos]
        exact hl3
  obtain ⟨kA,dA,_,hRunA,hAslot,hcA⟩ :=
    B0_left_one_pred_A0 kB dB hRunB hBstate hleftB
  have hApos : dB.head=dA.head+1 := by simp [hcA,applyMove]
  have hdropA (x:Int) (hx:x≠dA.head): dB.tape x=dA.tape x := by
    rw [hcA]; exact right_move_unchanged dA true B x hx
  have hchain (x:Int) (ha:x≠dA.head) (hb:x≠dB.head) (hc:x≠dC.head):
      c.tape x=dA.tape x := by
    calc
      c.tape x=dC.tape x := hdropC x hc
      _ = dB.tape x := hdropB x hb
      _ = dA.tape x := hdropA x ha
  have hAstate : dA.state=A := by simpa [readSlot] using congrArg Prod.fst hAslot
  have hA0 : dA.tape dA.head=false := by simpa [readSlot] using congrArg Prod.snd hAslot
  have hB0 : dB.tape dB.head=false := by simpa [readSlot] using congrArg Prod.snd hBslot
  have hC0 : dC.tape dC.head=false := by simpa [readSlot] using congrArg Prod.snd hCslot
  have hAl1 : dA.tape (dA.head-1)=true := by
    calc
      dA.tape (dA.head-1)=c.tape (dA.head-1) :=
        (hchain _ (by omega) (by omega) (by omega)).symm
      _ = true := by
        have hpos : dA.head-1=c.head-4 := by omega
        rw [hpos]; exact hl4
  have hAl3 : dA.tape (dA.head-3)=false := by
    calc
      dA.tape (dA.head-3)=c.tape (dA.head-3) :=
        (hchain _ (by omega) (by omega) (by omega)).symm
      _ = false := by
        have hpos : dA.head-3=c.head-6 := by omega
        rw [hpos]; exact hl6
  have hAr1 : dA.tape (dA.head+1)=false := by
    have hpos : dA.head+1=dB.head := by omega
    rw [hpos]
    exact (hdropA dB.head (by omega)).symm.trans hB0
  have hAr2 : dA.tape (dA.head+2)=false := by
    have hpos : dA.head+2=dC.head := by omega
    rw [hpos]
    calc
      dA.tape dC.head=dB.tape dC.head := (hdropA _ (by omega)).symm
      _ = dC.tape dC.head := (hdropB _ (by omega)).symm
      _ = false := hC0
  have hAr3 : dA.tape (dA.head+3)=false := by
    have hpos : dA.head+3=c.head := by omega
    rw [hpos]
    calc
      dA.tape c.head=dB.tape c.head := (hdropA _ (by omega)).symm
      _ = dC.tape c.head := (hdropB _ (by omega)).symm
      _ = c.tape c.head := (hdropC _ (by omega)).symm
      _ = false := hD0
  exact (forbidden_blank_A0_window kA dA hRunA)
    ⟨hAstate,hA0,hAl1,hAl3,hAr1,hAr2,hAr3⟩

#print axioms D0_prefix_forbidden
end BB429D0Window
