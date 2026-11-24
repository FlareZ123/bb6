import Q0MacroCore
import Lean.Elab.Tactic.Omega

namespace BB429Q0Macro
set_option maxHeartbeats 2000000

inductive WordPath : List Digit → Nat → Nat → Prop where
  | nil (p y : Nat) : WordPath [] p y
  | cons {d : Digit} {ds : List Digit} {p y : Nat}
      (hdiv : num d p y % 16 = 0)
      (tail : WordPath ds (nextP d p) (nextY d p y)) :
      WordPath (d::ds) p y

theorem WordPath.toPath {ds p y} (h : WordPath ds p y) :
    Path ds.length p y := by
  induction h with
  | nil => exact .nil _ _
  | cons h tail ih => exact .cons _ h ih

def checkResidues : Bool :=
  (List.range 16).all fun c =>
    (List.range 16).all fun b =>
      c%2 == 0 || (List.range 16).any fun r => (c*r+b)%16 == 0

theorem checkResidues_true : checkResidues = true := by decide

theorem odd_linear_mod16 (c b : Nat) (hc : c%2=1) :
    ∃ r<16, (c*r+b)%16=0 := by
  have h := List.all_eq_true.mp checkResidues_true (c%16)
      (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have h := List.all_eq_true.mp h (b%16)
      (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hc' : (c%16)%2=1 := by omega
  simp [hc'] at h
  obtain ⟨r,hr,he⟩ := h
  refine ⟨r,hr,?_⟩
  rw [Nat.add_mod,Nat.mul_mod]
  rw [Nat.add_mod,Nat.mul_mod] at he
  simpa [Nat.mod_mod] using he

theorem affine_num (d : Digit) (A B C E t : Nat) :
    num d (A*t+B) (C*t+E) =
    (C+digit d*A)*t+num d B E := by
  unfold num
  rw [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  ac_rfl

theorem affine_lift (d : Digit) (A B C E r t : Nat)
    (hr : num d (A*r+B) (C*r+E)%16=0) :
    num d (A*(r+16*t)+B) (C*(r+16*t)+E)%16=0 ∧
    nextP d (A*(r+16*t)+B) = (16*A)*t+nextP d (A*r+B) ∧
    nextY d (A*(r+16*t)+B) (C*(r+16*t)+E) =
      (C+digit d*A)*t+nextY d (A*r+B) (C*r+E) := by
  have he : num d (A*(r+16*t)+B) (C*(r+16*t)+E) =
      num d (A*r+B) (C*r+E)+16*((C+digit d*A)*t) := by
    rw [affine_num,affine_num,Nat.mul_add]
    ac_rfl
  constructor
  · rw [he]; omega
  constructor
  · unfold nextP
    rw [Nat.mul_add]; ac_rfl
  · unfold nextY
    rw [he]; omega

/-- For an affine line with rank coefficient divisible by 16 and
odd height coefficient, every word has an entire parameter cylinder. -/
theorem affine_word (ds : List Digit) (A B C E : Nat)
    (hA : A%16=0) (hC : C%2=1) :
    ∃ r<16^ds.length, ∀ t, WordPath ds
      (A*(r+16^ds.length*t)+B) (C*(r+16^ds.length*t)+E) := by
  induction ds generalizing A B C E with
  | nil => exact ⟨0,by decide,fun t => .nil _ _⟩
  | cons d ds ih =>
    have hodd : (C+digit d*A)%2=1 := by
      cases d <;> simp [digit] <;> omega
    obtain ⟨r,hr,hdiv⟩ := odd_linear_mod16 (C+digit d*A) (num d B E) hodd
    rw [←affine_num] at hdiv
    obtain ⟨s,hs,hpath⟩ := ih (16*A) (nextP d (A*r+B))
      (C+digit d*A) (nextY d (A*r+B) (C*r+E)) (by omega) hodd
    refine ⟨r+16*s,?_ ,?_⟩
    · simp only [List.length_cons,Nat.pow_succ]; omega
    · intro t
      have he : r+16*s+16^(d::ds).length*t =
          r+16*(s+16^ds.length*t) := by
        simp only [List.length_cons,Nat.pow_succ,Nat.mul_add]
        ac_rfl
      rw [he]
      obtain ⟨hd,hp,hy⟩ := affine_lift d A B C E r
        (s+16^ds.length*t) hdiv
      exact .cons hd (by rw [hp,hy]; exact hpath t)

def firstResidue : Digit → Nat
  | .zero => 2
  | .one => 0
  | .four => 3
  | .five => 1

/-- Every nonempty finite digit word is realized by an unbounded
arithmetic progression of q0 ray parameters. -/
theorem q0_word (d : Digit) (ds : List Digit) :
    ∃ u<8*16^ds.length, ∀ t,
      WordPath (d::ds) (24*(u+8*16^ds.length*t)+22)
        (6*(u+8*16^ds.length*t)+4) := by
  let r := firstResidue d
  let A := 192
  let B := nextP d (24*r+22)
  let C := 3+12*digit d
  let E := nextY d (24*r+22) (6*r+4)
  have hstep (v : Nat) :
      num d (24*(r+8*v)+22) (6*(r+8*v)+4)%16=0 ∧
      nextP d (24*(r+8*v)+22)=A*v+B ∧
      nextY d (24*(r+8*v)+22) (6*(r+8*v)+4)=C*v+E := by
    cases d <;> simp [r,A,B,C,E,firstResidue,num,nextP,nextY,cost,digit,offset] <;> omega
  obtain ⟨s,hs,hpath⟩ := affine_word ds A B C E (by decide)
    (by cases d <;> decide)
  refine ⟨r+8*s,?_ ,?_⟩
  · have hr : r<8 := by cases d <;> decide
    omega
  · intro t
    have he : r+8*s+8*16^ds.length*t = r+8*(s+16^ds.length*t) := by
      rw [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
    rw [he]
    obtain ⟨hd,hp,hy⟩ := hstep (s+16^ds.length*t)
    exact .cons hd (by rw [hp,hy]; exact hpath t)

theorem arbitrary_word_arbitrarily_large (ds : List Digit) (N : Nat) :
    ∃ u≥N, WordPath ds (24*u+22) (6*u+4) := by
  cases ds with
  | nil => exact ⟨N,by omega,.nil _ _⟩
  | cons d ds =>
    obtain ⟨u,hu,h⟩ := q0_word d ds
    refine ⟨u+8*16^ds.length*N,?_ ,h N⟩
    have hp : 0<16^ds.length := Nat.pow_pos (by decide)
    have hm := Nat.mul_le_mul_right N (show 1≤8*16^ds.length by omega)
    omega

#print axioms affine_word
#print axioms q0_word
#print axioms arbitrary_word_arbitrarily_large
end BB429Q0Macro
