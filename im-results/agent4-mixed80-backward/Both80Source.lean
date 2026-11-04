import First80Stop
import Five80Second
set_option maxHeartbeats 0
namespace A4MachineC80

/-- A uniform source-connected exclusion spanning both exact stopping families.
All candidate parameters remain unrestricted natural numbers except displayed residue gates. -/
theorem three_halting_sectors_unreachable (a k u m : Nat)
    (h : (a=1 ∧ k+3*m+4=2*4^(m+1) ∧ m%80=39) ∨
      (a=2*u+1 ∧ k+u+3*m+4=4^(m+1)*(u+2) ∧
         ((u%80=60 ∧ m%80=11) ∨ (u%80=20 ∧ m%80=51)))) :
    ¬ BB6CLine.Reach (a,k,0) := by
  rcases h with ⟨rfl,he,hm⟩ | ⟨rfl,he,hcond⟩
  · exact A4First80.source_first_m39_unreachable m k hm he
  · rcases hcond with ⟨hu,hm⟩ | ⟨hu,hm⟩
    · exact A4Five80.source_stop_m11_u60_unreachable u m k hu hm he
    · exact A4Five80.source_stop_m51_u20_unreachable u m k hu hm he

#print axioms three_halting_sectors_unreachable
end A4MachineC80
