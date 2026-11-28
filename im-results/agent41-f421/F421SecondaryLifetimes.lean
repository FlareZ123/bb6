import Std

namespace F421SecondaryLifetimes

/-- Far-to-near normalized positional P lifetimes, with d deleted ranks. -/
def advanceAux (d : Nat) : List Nat → List Nat × Nat
  | [] => ([],d)
  | l::ls =>
    if l=1 then advanceAux (d+1) ls
    else
      let (ys,D) := advanceAux d ls
      ((l-1)*2^d::ys,D)

def advance (ls : List Nat) : List Nat :=
  let (ys,D) := advanceAux 0 ls
  ys ++ [2^(D+1)]

def Positive (xs : List Nat) : Prop := ∀ x ∈ xs, 0 < x

def mass : List Nat → Nat
  | [] => 0
  | x::xs => x+2*mass xs

theorem mass_append (xs ys : List Nat) :
    mass (xs++ys)=mass xs+2^xs.length *mass ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    simp only [List.cons_append, mass,List.length_cons,Nat.pow_succ,ih]
    simp only [Nat.mul_add]
    ac_rfl

theorem advanceAux_length (d : Nat) (xs : List Nat) :
    (advanceAux d xs).1.length+(advanceAux d xs).2 = xs.length+d := by
  induction xs generalizing d with
  | nil => simp [advanceAux]
  | cons x xs ih =>
    by_cases hx : x=1
    · simp only [advanceAux,if_pos hx,List.length_cons]
      have h:=ih (d+1)
      omega
    · rcases he : advanceAux d xs with ⟨ys,D⟩
      have h:=ih d
      rw [he] at h
      simp only [Prod.fst,Prod.snd] at h
      simp only [advanceAux,if_neg hx,he,List.length_cons]
      omega

theorem advanceAux_mass (d : Nat) (xs : List Nat) (hp : Positive xs) :
    mass (advanceAux d xs).1+2^d*2^xs.length=2^d*(mass xs+1) := by
  induction xs generalizing d with
  | nil => simp [advanceAux,mass]
  | cons x xs ih =>
    have px : 0<x := hp x (by simp)
    have ht : Positive xs := fun y hy => hp y (by simp [hy])
    by_cases hx : x=1
    · have h:=ih (d+1) ht
      simp only [advanceAux,ite_eq_left hx,List.length_cons,Nat.pow_succ,mass,hx]
      calc
        mass (advanceAux (d+1) xs).1 + 2^d*(2^xs.length*2)
            = mass (advanceAux (d+1) xs).1+2^(d+1)*2^xs.length := by
                rw [Nat.pow_succ]; ac_rfl
        _ = 2^(d+1)*(mass xs+1) := h
        _ = 2^d*(1+2*mass xs+1) := by
          rw [Nat.pow_succ]
          have hh : 1+2*mass xs+1=2*(mass xs+1) := by omega
          rw [hh]
          ac_rfl
    · rcases he : advanceAux d xs with ⟨ys,D⟩
      have h:=ih d ht
      rw [he] at h
      simp only [Prod.fst,Prod.snd] at h
      simp only [advanceAux,ite_eq_right hx,he,List.length_cons,Nat.pow_succ,mass]
      have hpos : 1≤x := by omega
      calc
        (x-1)*2^d+2*mass ys+2^d*(2^xs.length*2)
            = (x-1)*2^d+2*(mass ys+2^d*2^xs.length) := by
                simp only [Nat.mul_add]
                ac_rfl
        _ = (x-1)*2^d+2*(2^d*(mass xs+1)) := by rw [h]
        _ = 2^d*(x+2*mass xs+1) := by
          have hh : (x-1)+2*(mass xs+1)=x+2*mass xs+1 := by omega
          rw [←hh]
          simp only [Nat.mul_add]
          ac_rfl

/-- Exact weighted-mass growth regardless of which lifetimes expire. -/
theorem advance_mass (xs : List Nat) (hp : Positive xs) :
    mass (advance xs)=mass xs+2^xs.length+1 := by
  rcases he : advanceAux 0 xs with ⟨ys,D⟩
  have hl:=advanceAux_length 0 xs
  have hm:=advanceAux_mass 0 xs hp
  rw [he] at hl hm
  simp only [Nat.pow_zero,Nat.one_mul,Nat.add_zero] at hl hm
  unfold advance
  rw [he]
  rw [mass_append]
  simp only [mass,List.length_singleton,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
  have heq : 2^ys.length*2^(D+1)=2^(xs.length+1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [heq,Nat.pow_succ]
  omega

theorem advance_nonempty (xs : List Nat) : 0<(advance xs).length := by
  unfold advance
  rcases advanceAux 0 xs with ⟨ys,D⟩
  simp

/-- Physical P sizes of a far-to-near normalized cylinder. -/
def physicalP (B : Nat) : List Nat → List Nat
  | [] => []
  | l::ls => 2*B*l :: physicalP (2*B) ls

/-- P projection of the all-marked source drain, with already-decremented P. -/
def sourcePDrain (h : Nat) : List Nat → List Nat × Nat
  | [] => ([],h)
  | p::ps =>
    if p≤2*h+1 then sourcePDrain (h+(p+1)/2) ps
    else let (ys,H):=sourcePDrain (2*h+1) ps
         ((p-(2*h+1))::ys,H)

def markedPhysicalP (B : Nat) (xs : List Nat) : List Nat :=
  (physicalP B xs).map (· - 1)

/-- Exact physical P vector, not merely a halting or count approximation.
    B=C*2^d carries the number of deleted positional ranks. -/
theorem sourcePDrain_lifetime (B C d : Nat) (xs : List Nat)
    (hB : 0<B) (he : B=C*2^d) (hp : Positive xs) :
    let (ys,D) := advanceAux d xs
    sourcePDrain (B-1) (markedPhysicalP B xs) =
      (physicalP C ys,B*2^xs.length-1) := by
  induction xs generalizing B C d with
  | nil => simp [advanceAux,sourcePDrain,markedPhysicalP,physicalP]
  | cons x xs ih =>
    have hx : 0<x := hp x (by simp)
    have ht : Positive xs := fun y hy => hp y (by simp [hy])
    have hcap : 2*(B-1)+1=2*B-1 := by omega
    have hpow : B*2^(xs.length+1)=(2*B)*2^xs.length := by
      simp [Nat.pow_succ]; ac_rfl
    by_cases h1 : x=1
    · have hbnew : 0<2*B := by omega
      have heNew : 2*B=C*2^(d+1) := by rw [he,Nat.pow_succ]; ac_rfl
      have h := ih (2*B) C (d+1) hbnew heNew ht
      have hstep : (2*B*x-1+1)/2=B := by rw [h1]; omega
      have hle : 2*B*x-1≤2*(B-1)+1 := by rw [h1]; omega
      rcases hk : advanceAux (d+1) xs with ⟨ys,D⟩
      rw [hk] at h
      simp only [advanceAux,ite_eq_left h1,markedPhysicalP,physicalP,List.map_cons]
      simp only [sourcePDrain,ite_eq_left hle,hstep,show B-1+B=2*B-1 by omega]
      change sourcePDrain (2*B-1) (markedPhysicalP (2*B) xs) = _
      rw [h]
      simp only [hk,Prod.fst,List.length_cons,hpow]
    · have hx2 : 2≤x := by omega
      have hbnew : 0<2*B := by omega
      have heNew : 2*B=(2*C)*2^d := by rw [he]; ac_rfl
      have h := ih (2*B) (2*C) d hbnew heNew ht
      have hmul : (2*B)*2≤(2*B)*x := Nat.mul_le_mul_left (2*B) hx2
      have hnot : ¬2*B*x-1≤2*(B-1)+1 := by omega
      have hdecomp : 2*B*x=2*B*(x-1)+2*B := by
        calc
          2*B*x = 2*B*((x-1)+1) := by rw [Nat.sub_add_cancel (by omega : 1≤x)]
          _ = 2*B*(x-1)+2*B := by simp [Nat.mul_add]
      have hminus : 2*B*x-1-(2*(B-1)+1)=2*B*(x-1) := by omega
      rcases hk : advanceAux d xs with ⟨ys,D⟩
      rw [hk] at h
      simp only [advanceAux,ite_eq_right h1,markedPhysicalP,physicalP,List.map_cons]
      simp only [sourcePDrain,ite_eq_right hnot,show 2*(B-1)+1=2*B-1 by omega]
      have hnot2 : ¬2*B*x-1≤2*B-1 := by omega
      simp only [ite_eq_right hnot2]
      change (((2*B*x-1-(2*B-1))::(sourcePDrain (2*B-1) (markedPhysicalP (2*B) xs)).1),
        (sourcePDrain (2*B-1) (markedPhysicalP (2*B) xs)).2) = _
      rw [h]
      simp only [Prod.fst,Prod.snd,physicalP,List.length_cons,hpow]
      congr 1
      · rw [hcap] at hminus
        rw [hminus,he,hk]
        simp only [Prod.fst,Nat.mul_assoc]
        ac_rfl

#print axioms advanceAux_length
#print axioms advanceAux_mass
#print axioms advance_mass
#print axioms sourcePDrain_lifetime

end F421SecondaryLifetimes
