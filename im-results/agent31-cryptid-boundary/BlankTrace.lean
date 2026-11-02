import Lean.Elab.Tactic.Omega
import BoundaryExtra

namespace CryptidBoundary

theorem blank226 : run 226 blank = init (List.replicate 25 true) := by
  have h : 226 = 36+(12*2*2+49*2+44) := by decide
  rw [h, run_add, blank36]
  simpa [init] using full_A_nil 2

theorem blank1430 : run 1430 blank = init (List.replicate 73 true) := by
  have h : 1430 = 226+(12*8*8+49*8+44) := by decide
  rw [h, run_add, blank226]
  simpa [init] using full_A_nil 8

theorem blank9562 : run 9562 blank = init (List.replicate 201 true) := by
  have h : 9562 = 1430+(12*24*24+49*24+44) := by decide
  rw [h, run_add, blank1430]
  simpa [init] using full_A_nil 24

theorem blank66753 : run 66753 blank = init (List.replicate 543 true) := by
  have h : 66753 = 9562+(12*67*67+49*67+40) := by decide
  rw [h, run_add, blank9562]
  simpa [init] using full_B_nil 67

#print axioms blank226
#print axioms blank1430
#print axioms blank9562
#print axioms blank66753

end CryptidBoundary
