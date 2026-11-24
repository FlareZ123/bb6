import Lean

namespace MachineCSteering

abbrev State := Int × Int

def direct (s : State) : State := (2*s.1-s.2,s.2+4)
def affine (P Q C W : Int) (s : State) : State :=
  (P*s.1-Q*s.2+C,s.2+W)
def shear (g h : Int) (s : State) : State := (s.1+g*s.2+h,s.2)
def translate (t : Int) (s : State) : State := (s.1+t,s.2)

-- The commutator shear identity, without invoking an inverse in the integers.
theorem commute_affine (P Q C W : Int) (s : State) :
    direct (affine P Q C W s) =
      shear (P-Q-1) (C-W+4*Q-(P-Q-1)*(W+4))
        (affine P Q C W (direct s)) := by
  rcases s with ⟨a,m⟩
  simp only [direct, affine, shear, Prod.mk.injEq]
  constructor <;> grind

-- In a finite modular permutation group, K = D F D⁻¹ F⁻¹.
-- This identity gives D K D⁻¹ K⁻² = translation by -8g.
theorem commute_shear (g h : Int) (s : State) :
    direct (shear g h s) = translate (-8*g) (shear g h (shear g h (direct s))) := by
  rcases s with ⟨a,m⟩
  simp only [direct,shear,translate,Prod.mk.injEq]
  constructor <;> grind

def bounce2 (o : Int) : State → State := affine 4 1 (1+2*o) 7
def bounce3 (o : Int) : State → State := affine 8 1 (6+6*o) 10

theorem bounce2_twice (o : Int) (s : State) :
    bounce2 (1-o) (bounce2 o s) = affine 16 5 (6*o) 14 s := by
  rcases s with ⟨a,m⟩
  simp only [bounce2,affine,Prod.mk.injEq]
  constructor <;> omega

theorem shift_generators (o : Int) (s : State) :
    direct (bounce3 o s) = shear 6 (6*o-84) (bounce3 o (direct s)) := by
  rcases s with ⟨a,m⟩
  simp only [direct,bounce3,affine,shear,Prod.mk.injEq]
  constructor <;> omega

-- Both translation steps are even, and their difference combinations generate 16.
theorem translation16 (s : State) :
    translate (-48) (translate (-48) (translate 80 s)) = translate (-16) s := by
  rcases s with ⟨a,m⟩
  simp [translate]
  omega

#print axioms commute_affine
#print axioms commute_shear
#print axioms bounce2_twice
#print axioms shift_generators
#print axioms translation16
end MachineCSteering
