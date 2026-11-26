import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRF4570
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth
open BB6Coverage.Agent10ZipAudit

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def O (n : Nat) : List Bool := rep [true] n
def Zs (n : Nat) : List Bool := rep [false] n
@[simp] theorem O_zero : O 0 = [] := rfl
@[simp] theorem O_succ (n : Nat) : O (n+1) = true :: O n := rfl
@[simp] theorem Zs_zero : Zs 0 = [] := rfl
@[simp] theorem Zs_succ (n : Nat) : Zs (n+1) = false :: Zs n := rfl

theorem O_add (a b : Nat) : O (a+b) = O a ++ O b := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add,O_succ,O_succ,ih]; rfl

theorem Zs_add (a b : Nat) : Zs (a+b) = Zs a ++ Zs b := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add,Zs_succ,Zs_succ,ih]; rfl

def F (L R : List Bool) : Z0 := ⟨5,false::L,R⟩

theorem cblock (L R : List Bool) : run0 p 3 ⟨2,[false,true,true]++L,R⟩ = some ⟨2,[false,true]++L,[true]++R⟩ := rfl
-- C0 erases one left-hand 1 per three-step traversal, until the final one.
theorem cb (L R : List Bool) : run0 p 3 ⟨2,[false]++[true,true]++L,R⟩ = some ⟨2,[false,true]++L,[true]++R⟩ := rfl

theorem r000 (x : Nat) (U T : List Bool) : run0 p (3*x+12) (F (O x++false::U) ([false,false,false]++T)) = some (F (false::U) (O (x+3)++T)) := by
  have h0 (L R : List Bool) : run0 p 3 (F L ([false,false,false]++R)) = some ⟨2,[false,true,true,true]++L,R⟩ := rfl
  have hs (L R : List Bool) : run0 p 3 ⟨2,[false,true]++[true]++L,R⟩ = some ⟨2,[false,true]++L,[true]++R⟩ := rfl
  have h1 := sweepL p 2 [false,true] [] [true] [true] 3 hs (x+2) (false::U) T
  have h2 (L R : List Bool) : run0 p 3 ⟨2,[false,true,false]++L,R⟩ = some (F (false::L) (true::R)) := rfl
  have h0' := h0 (O x++false::U) T
  rw [show [false,true,true,true]++(O x++false::U) = [false,true]++rep [true] (x+2)++(false::U) by rfl] at h0'
  have h := join0 (join0 h0' h1) (h2 U (O (x+2)++T))
  rw [show 3*x+12=3+3*(x+2)+3 by omega]
  exact h

theorem r0011 (x : Nat) (U T : List Bool) : run0 p (x+9) (F (O x++false::U) ([false,false,true,true]++T)) = some (F U (Zs (x+5)++T)) := by
  have h0 (L R : List Bool) : run0 p 4 (F L ([false,false,true,true]++R)) = some ⟨5,[true,true,true,true,true]++L,R⟩ := rfl
  have hs (L R : List Bool) : run0 p 1 ⟨5,[true]++L,R⟩ = some ⟨5,L,[false]++R⟩ := rfl
  have h1 := sweepL p 5 [] [] [true] [false] 1 hs (x+5) (false::U) T
  have h0' := h0 (O x++false::U) T
  rw [show [true,true,true,true,true]++(O x++false::U) = []++rep [true] (x+5)++(false::U) by rfl] at h0'
  have h := join0 h0' h1
  rw [show x+9=4+1*(x+5) by omega]
  exact h

theorem r0010 (L T : List Bool) : run0 p 4 (F L ([false,false,true,false]++T)) = some (F ([true,true,true,true]++L) T) := rfl
theorem r010 (L T : List Bool) : run0 p 3 (F L ([false,true,false]++T)) = some (F ([false,true,true]++L) T) := rfl
theorem r011 (L T : List Bool) : run0 p 4 (F L ([false,true,true]++T)) = some (F ([true,true]++L) (false::T)) := rfl
theorem r110 (L T : List Bool) : run0 p 3 (F L ([true,true,false]++T)) = some (F ([true,false,true]++L) T) := rfl
theorem r111 (L T : List Bool) : run0 p 5 (F L ([true,true,true]++T)) = some (F (true::L) ([false,false]++T)) := rfl

theorem ew_nil_zeros (n : Nat) : EqW [] (Zs n) := by
  intro i
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem ew_prefix (P : List Bool) {a b : List Bool} (h : EqW a b) : EqW (P++a) (P++b) := by
  induction P with
  | nil => exact h
  | cons c P ih => exact eqW_cons rfl ih

theorem ew_pad (P : List Bool) (n : Nat) : EqW P (P++Zs n) := by
  have h := ew_prefix P (ew_nil_zeros n)
  simpa only [List.append_nil] using h

theorem eqF {L R L' R' : List Bool} (hl : EqW L L') (hr : EqW R R') : EqZ (F L R) (F L' R') := ⟨rfl,eqW_cons rfl hl,hr⟩
theorem ew_refl (L : List Bool) : EqW L L := fun _ => rfl
theorem ew_symm {L R : List Bool} (h : EqW L R) : EqW R L := fun i => (h i).symm

theorem sweep011 (j : Nat) (L T : List Bool) : run0 p (4*j) (F L (false::(O (2*j)++T))) = some (F (O (2*j)++L) (false::T)) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    have h := r011 L (O (2*j)++T)
    have H := join0 h (ih ([true,true]++L))
    rw [show 4*(j+1)=4+4*j by omega,show 2*(j+1)=2+2*j by omega,O_add]
    have hcomm : O (2*j) ++ [true,true] = [true,true] ++ O (2*j) := by
      change O (2*j) ++ O 2 = O 2 ++ O (2*j)
      rw [←O_add,←O_add,Nat.add_comm]
    change run0 p (4+4*j) (F L (false::(O 2++(O (2*j)++T)))) = some (F (O 2++(O (2*j)++L)) (false::T))
    change run0 p (4+4*j) (F L (false::(O 2++(O (2*j)++T)))) = some (F (O (2*j)++(O 2++L)) (false::T)) at H
    simpa only [←List.append_assoc,←O_add,Nat.add_comm (2*j) 2] using H

theorem transfer (j : Nat) (T : List Bool) : Reach p (4*j+59) (F [] (O (2*j+6)++false::T)) (F (false::O (2*j+7)) T) := by
  have h0 (Y : List Bool) : run0 p 56 (F [] (O 5++Y)) = some (F (O 5++[false]) (false::Y)) := rfl
  have h1 := h0 (O (2*j)++true::false::T)
  have h2 := sweep011 j (O 5++[false]) (true::false::T)
  have h3 := r010 (O (2*j)++(O 5++[false])) T
  have H := join0 (join0 h1 h2) h3
  rw [show 56+4*j+3=4*j+59 by omega] at H
  have hi : O (2*j+6)++false::T = O 5 ++ (O (2*j)++true::false::T) := by
    rw [show 2*j+6=5+2*j+1 by omega,O_add,O_add]
    simp [List.append_assoc]
  have ho : [false,true,true]++(O (2*j)++(O 5++[false])) = (false::O (2*j+7))++[false] := by
    change false::(O 2++(O (2*j)++(O 5++[false]))) = false::O (2*j+7)++[false]
    simp only [←List.append_assoc,←O_add]
    rw [show 2+(2*j+5)=2*j+7 by omega]
    rfl
  rw [←hi,ho] at H
  exact padRun (exactRun H) (eqZ_refl _) (eqF (ew_symm (ew_pad _ 1)) (ew_refl T))

-- Fixed bridge prefixes, followed by one parametric C0 sweep.
theorem b1prefix (L : List Bool) : run0 p 83 (F (false::L) []) = some (F L (Zs 6++O 3)) := rfl
theorem b3prefix (L : List Bool) : run0 p 116 (F ([false,true,true,false]++L) []) = some (F L (Zs 9++O 3)) := rfl
theorem b4prefix (L : List Bool) : run0 p 91 (F (false::L) (Zs 5++O 3)) = some (F L (Zs 6++O 4)) := rfl
theorem b6prefix (L : List Bool) : run0 p 37 (F (false::L) [false,true,true]) = some (F L (Zs 6)) := rfl

theorem sweepBlank (x : Nat) (T : List Bool) : Reach p (3*x+12) (F (O x) (Zs 3++T)) (F [] (O (x+3)++T)) := by
  apply padRun (exactRun (r000 x [] T))
  · exact eqF (ew_pad _ 1) (ew_refl _)
  · exact eqF (ew_symm (ew_nil_zeros 1)) (ew_refl _)

theorem bridge1 (n : Nat) : Reach p (3*n+98) (F (false::O (n+1)) []) (F [] (O (n+4)++Zs 3++O 3)) := by
  have h := join (exactRun (b1prefix (O (n+1)))) (sweepBlank (n+1) (Zs 3++O 3))
  simpa only [show 83+(3*(n+1)+12)=3*n+98 by omega,show n+1+3=n+4 by omega,List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h

theorem bridge2 (n : Nat) : Reach p (3*n+36) (F (false::O (n+5)) (Zs 2++O 3)) (F [] (O (n+8)++Zs 2++O 1)) := by
  have h := join (exactRun (r0011 0 (O (n+5)) (O 1))) (sweepBlank (n+5) (Zs 2++O 1))
  simpa only [show 0+9+(3*(n+5)+12)=3*n+36 by omega,show n+5+3=n+8 by omega,List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h

theorem bridge3 (n : Nat) : Reach p (3*n+158) (F (false::O (n+9)) [false,true]) (F [] (O (n+12)++Zs 6++O 3)) := by
  have h0 : Reach p 3 (F (false::O (n+9)) [false,true]) (F ([false,true,true,false]++O (n+9)) []) := by
    apply padRun (exactRun (r010 (false::O (n+9)) []))
    · exact eqF (ew_refl _) (ew_pad _ 1)
    · exact eqZ_refl _
  have h := join (join h0 (exactRun (b3prefix (O (n+9))))) (sweepBlank (n+9) (Zs 6++O 3))
  simpa only [show 3+116+(3*(n+9)+12)=3*n+158 by omega,show n+9+3=n+12 by omega,List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h

theorem bridge4 (n : Nat) : Reach p (3*n+142) (F (false::O (n+13)) (Zs 5++O 3)) (F [] (O (n+16)++Zs 3++O 4)) := by
  have h := join (exactRun (b4prefix (O (n+13)))) (sweepBlank (n+13) (Zs 3++O 4))
  simpa only [show 91+(3*(n+13)+12)=3*n+142 by omega,show n+13+3=n+16 by omega,List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h

theorem bridge5 (n : Nat) : Reach p (3*n+72) (F (false::O (n+17)) (Zs 2++O 4)) (F [] (O (n+20)++Zs 2++O 2)) := by
  have h := join (exactRun (r0011 0 (O (n+17)) (O 2))) (sweepBlank (n+17) (Zs 2++O 2))
  simpa only [show 0+9+(3*(n+17)+12)=3*n+72 by omega,show n+17+3=n+20 by omega,List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h

theorem bridge6 (n : Nat) : Reach p (3*n+112) (F (false::O (n+21)) (Zs 1++O 2)) (F [] (O (n+24))) := by
  have h := join (exactRun (b6prefix (O (n+21)))) (sweepBlank (n+21) (Zs 3))
  rw [show 37+(3*(n+21)+12)=3*n+112 by omega,show n+21+3=n+24 by omega] at h
  exact padRun h (eqZ_refl _) (eqF (ew_refl []) (ew_symm (ew_pad _ 3)))

theorem period (j : Nat) : Reach p (60*j+1200) (F [] (O (2*j+6))) (F [] (O (2*j+30))) := by
  let n := 2*j+6
  have t1 : Reach p (2*n+47) (F [] (O n)) (F (false::O (n+1)) []) := by
    have h := transfer j []
    rw [show 4*j+59=2*n+47 by dsimp [n] <;> omega,show 2*j+7=n+1 by dsimp [n] <;> omega] at h
    exact padRun h (eqF (ew_refl []) (ew_pad _ 1)) (eqZ_refl _)
  have t2 : Reach p (2*n+55) (F [] (O (n+4)++Zs 3++O 3)) (F (false::O (n+5)) (Zs 2++O 3)) := by
    have h := transfer (j+2) (Zs 2++O 3)
    rw [show 4*(j+2)+59=2*n+55 by dsimp [n] <;> omega,show 2*(j+2)+6=n+4 by dsimp [n] <;> omega,show 2*(j+2)+7=n+5 by dsimp [n] <;> omega] at h
    simpa only [List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h
  have t3 : Reach p (2*n+63) (F [] (O (n+8)++Zs 2++O 1)) (F (false::O (n+9)) [false,true]) := by
    have h := transfer (j+4) [false,true]
    rw [show 4*(j+4)+59=2*n+63 by dsimp [n] <;> omega,show 2*(j+4)+6=n+8 by dsimp [n] <;> omega,show 2*(j+4)+7=n+9 by dsimp [n] <;> omega] at h
    simpa only [List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h
  have t4 : Reach p (2*n+71) (F [] (O (n+12)++Zs 6++O 3)) (F (false::O (n+13)) (Zs 5++O 3)) := by
    have h := transfer (j+6) (Zs 5++O 3)
    rw [show 4*(j+6)+59=2*n+71 by dsimp [n] <;> omega,show 2*(j+6)+6=n+12 by dsimp [n] <;> omega,show 2*(j+6)+7=n+13 by dsimp [n] <;> omega] at h
    simpa only [List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h
  have t5 : Reach p (2*n+79) (F [] (O (n+16)++Zs 3++O 4)) (F (false::O (n+17)) (Zs 2++O 4)) := by
    have h := transfer (j+8) (Zs 2++O 4)
    rw [show 4*(j+8)+59=2*n+79 by dsimp [n] <;> omega,show 2*(j+8)+6=n+16 by dsimp [n] <;> omega,show 2*(j+8)+7=n+17 by dsimp [n] <;> omega] at h
    simpa only [List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h
  have t6 : Reach p (2*n+87) (F [] (O (n+20)++Zs 2++O 2)) (F (false::O (n+21)) (Zs 1++O 2)) := by
    have h := transfer (j+10) (Zs 1++O 2)
    rw [show 4*(j+10)+59=2*n+87 by dsimp [n] <;> omega,show 2*(j+10)+6=n+20 by dsimp [n] <;> omega,show 2*(j+10)+7=n+21 by dsimp [n] <;> omega] at h
    simpa only [List.append_assoc,O_zero,O_succ,Zs_zero,Zs_succ,List.nil_append,List.cons_append,List.append_nil] using h
  have h := join (join (join (join (join (join t1 (bridge1 n)) t2) (bridge2 n)) t3) (bridge3 n)) (join (join (join (join (join t4 (bridge4 n)) t5) (bridge5 n)) t6) (bridge6 n))
  have hc : 2*n+47+(3*n+98)+(2*n+55)+(3*n+36)+(2*n+63)+(3*n+158)+(2*n+71+(3*n+142)+(2*n+79)+(3*n+72)+(2*n+87)+(3*n+112)) = 60*j+1200 := by dsimp [n] <;> omega
  rw [hc,show n+24=2*j+30 by dsimp [n] <;> omega] at h
  exact h

def family (k : Nat) := F [] (O (24*(k+1)))
theorem growth (k : Nat) : Reach p (720*k+1740) (family k) (family (k+1)) := by
  have h := period (12*k+9)
  simpa only [family,show 60*(12*k+9)+1200=720*k+1740 by omega,show 2*(12*k+9)+6=24*(k+1) by omega,show 2*(12*k+9)+30=24*(k+1+1) by omega] using h

theorem seed : Reach p 967 ⟨0,[],[]⟩ (family 0) := by
  have h : run0 p 967 ⟨0,[],[]⟩ = some (F [false] (O 24++Zs 3)) := by decide +kernel
  exact padRun (exactRun h) (eqZ_refl _) (eqF (ew_symm (ew_nil_zeros 1)) (ew_symm (ew_pad _ 3)))
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_pad_growth p family 967 (fun k => 720*k+1740) seed (by intro k; omega) growth m hm
#print axioms period
#print axioms growth
#print axioms never
end BB6.Agent6E0ZeroRF4570
