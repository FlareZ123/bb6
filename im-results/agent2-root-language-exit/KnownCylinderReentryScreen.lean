import BlankEighteenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2KnownCylinderReentryScreen

def c1 : Nat :=
  5268534872184678030381663891870832023467293190261557

def c2 : Nat :=
  14049426325825808081017770378322218729246115174030817

/-- The authentic eighteenth regular segment starts from this
    seventeenth source reentry. -/
abbrev seed18 : DRegular.L := BB6.Agent2EighteenthRoot.seed18

/-- The authentic eighteenth packet reentry. -/
def seed19 : DRegular.L :=
  ⟨64*BB6.Agent2EighteenthRoot.t18+23,1,5⟩

theorem c1_mod3 : c1 % 3 = 1 := by norm_num [c1]
theorem c2_mod3 : c2 % 3 = 2 := by norm_num [c2]

/-- The seventeenth reentry parameter t17 is 3*u17 and
    t17 mod 27 = 6, hence u17 mod 9 = 2. -/
theorem u17_mod9 : BB6.Agent2EighteenthRoot.u17 % 9 = 2 := by
  have ht : BB6.Agent2SeventeenthRoot.t17 % 27 = 6 :=
    BB6.Agent2SeventeenthRoot.t17_mod27
  have hdiv :
      BB6.Agent2SeventeenthRoot.t17 =
        3 * BB6.Agent2EighteenthRoot.u17 := by
    dsimp [BB6.Agent2EighteenthRoot.u17]
    omega
  omega

/-- Episode 17 reenters at suffix (3,2), but its unary parameter is
    0 mod 3, whereas external checkpoint 2 requires 2 mod 3. -/
theorem seed18_mod3 : seed18.a % 3 = 0 := by
  have hu := u17_mod9
  change
    (8*(64*BB6.Agent2EighteenthRoot.u17+10)+39) % 3 = 0
  omega

theorem episode17_suffix : seed18.q = 3 ∧ seed18.b = 2 := by
  rfl

theorem episode17_misses_checkpoint2 :
    ∀ k : Nat, seed18.a ≠ c2 + 3^106*8^2*k := by
  intro k h
  have hmod := congrArg (fun n : Nat => n % 3) h
  have hfamily : (c2 + 3^106*8^2*k) % 3 = 2 := by
    omega
  omega

/-- Episode 18 reenters at suffix (1,5), but its unary parameter is
    0 mod 3, whereas external checkpoint 1 requires 1 mod 3. -/
theorem seed19_mod3 : seed19.a % 3 = 0 := by
  have ht : BB6.Agent2EighteenthRoot.t18 % 27 = 22 :=
    BB6.Agent2EighteenthRoot.t18_mod27
  change (64*BB6.Agent2EighteenthRoot.t18+23) % 3 = 0
  omega

theorem episode18_suffix : seed19.q = 1 ∧ seed19.b = 5 := by
  rfl

theorem episode18_misses_checkpoint1 :
    ∀ k : Nat, seed19.a ≠ c1 + 3^107*8*k := by
  intro k h
  have hmod := congrArg (fun n : Nat => n % 3) h
  have hfamily : (c1 + 3^107*8*k) % 3 = 1 := by
    omega
  omega

#print axioms u17_mod9
#print axioms seed18_mod3
#print axioms episode17_misses_checkpoint2
#print axioms seed19_mod3
#print axioms episode18_misses_checkpoint1

end BB6.Agent2KnownCylinderReentryScreen
