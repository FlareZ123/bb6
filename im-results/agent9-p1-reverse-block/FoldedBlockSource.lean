import FoldedBlockProbe
import ReverseBlockSource
import JumpResidueSource
import BatchCarrySource

namespace BB6.Agent9FoldedProbe
open BB6.Agent9BatchCarry (Interior Walk)

def foldedBack (q k : Nat) (ends : List Nat) : List Nat :=
  ((BB6.Agent45ReverseBlock.backBlock q k ends).map (fold q)).eraseDups

theorem foldedBack_cover (q k j : Nat) (ends : List Nat)
    (hfit : 2^(k+1)≤q+k) (hends : LiveCover (q+k) j ends) :
    LiveCover q (k+j) (foldedBack q k ends) := by
  exact folded_back_cover q k j ends _ hends
    (fun c => BB6.Agent45ReverseBlock.mem_backBlock q k c ends hfit)

/-- The modular subset-sum jump initializes the same folded live cover,
    without enumerating terminal carries or requiring a fitted block. -/
def foldedJump (q k : Nat) : List Nat :=
  (BB6.Agent9JumpResidue.liftResidues q k 0).filter
    (fun c => decide (1≤c ∧ c+3≤q ∧ c≤(q-2)/2))

theorem canon_iff (q c : Nat) :
    Canon q c ↔ 1≤c ∧ c+3≤q ∧ c≤(q-2)/2 := by
  unfold Canon Interior fold complement
  constructor
  · rintro ⟨⟨h1,h2⟩,h3⟩
    have h4 : c≤q-2-c := by
      have hm : min c (q-2-c) ≤ q-2-c := Nat.min_le_right _ _
      omega
    exact ⟨h1,h2,by omega⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨⟨h1,h2⟩,Nat.min_eq_left (by omega)⟩

theorem foldedJump_cover (q k : Nat) : LiveCover q k (foldedJump q k) := by
  intro c
  have hr := BB6.Agent9ReverseBlock.mem_lift_iff_walk (q+k) c (List.replicate k 0) (by simp)
  simp only [List.length_replicate,Nat.add_sub_cancel,
    BB6.Agent45ReverseBlock.digits_zero] at hr
  simp only [foldedJump,List.mem_filter,decide_eq_true_eq,←canon_iff,hr]
  constructor
  · rintro ⟨⟨z,hz⟩,hc⟩
    have hw := BB6.Agent45ReverseBlock.reverse_to_source hc.1 hz
    exact ⟨fold (q+k) z,c,z,hw,hc.2,rfl⟩
  · rintro ⟨b,hb⟩
    obtain ⟨z,hz,_⟩ := folded_lift_start hb
    exact ⟨⟨z,BB6.Agent45ReverseBlock.source_to_reverse hz⟩,folded_start hb⟩

/-- Absence from a short in-block probe excludes the original P1 critical
    reset, via the accepted common-clock source theorem. -/
theorem no_reach_of_empty_probe (F j n : Nat) (ends : List Nat)
    (hn : 14≤n) (he : n%2=0) (hF : n+4≤F) (hK : F+j≤2*n+3)
    (hends : LiveCover F j ends)
    (hprobe : ¬∃ b∈forward (n+4) ((n+2)/2) (F-(n+4)), b∈ends) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  apply BB6.Agent9BatchCarry.critical_reset_no_reach_batch (F+j) n n hn (by omega) (by omega) hK he
  intro hm
  obtain ⟨_,_,_,hmem⟩ := (BB6.Agent9BatchCarry.mem_batch (F+j) n n (by omega)).1 hm
  obtain ⟨z,hz⟩ := (BB6.Agent9BatchCarry.mem_live (n+4) ((n+2)/2) ((F+j)-(n+4))).1 hmem
  have hq : n+4+(F-(n+4))=F := by omega
  have hlen : (F+j)-(n+4)=(F-(n+4))+j := by omega
  rw [hlen] at hz
  have hc : Canon (n+4) ((n+2)/2) := by
    simpa [show n+4-2=n+2 by omega] using center_canon (n+4) (by omega)
  have hcover : LiveCover (n+4+(F-(n+4))) j ends := by rw [hq]; exact hends
  exact hprobe ((probe_iff _ _ _ _ ends hc hcover).2 ⟨z,hz⟩)

#print axioms foldedBack_cover
#print axioms foldedJump_cover
#print axioms no_reach_of_empty_probe
end BB6.Agent9FoldedProbe
