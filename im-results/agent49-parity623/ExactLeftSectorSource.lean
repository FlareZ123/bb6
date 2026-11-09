import Agent49SharpSpectrumCapacitySource

/-!
Exact left-sector one-step halting geometry for the original Cryptids #623
high-level map, in terms of the universally complete finite fatal lists.
This does not establish that the authentic blank-root orbit reaches or avoids
the listed states.
-/

namespace BB6.Agent49LeftSector
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FastSpectrum
open BB6.Agent49Capacity

/-- Odd third-counter, far-left input: the entire original source halting
predicate is membership in one exact finite block-spectrum. -/
theorem odd_left_none_iff_spectrum (a d : Nat)
    (hd : d%2=1) (ha : d+5≤a) :
    (highLevelNext (.D a d) = none) ↔
      a-d-5 ∈ fastSpectrum (d+3) := by
  have ha0 : a≠0 := by omega
  have hg : d%2=1 ∧ a≥d+5 := ⟨hd,ha⟩
  have hs : highLevelNext (.D a d) = drainB (a-d-5) (d+3) 5 := by
    simp only [highLevelNext,if_neg ha0, if_pos hg]
  rw [hs]
  exact drain_none_iff_fastSpectrum (a-d-5) (d+3) 5

/-- Even third-counter, far-left input: same exact arithmetic criterion. -/
theorem even_left_none_iff_spectrum (a d : Nat)
    (hd : d%2=0) (ha : d+3≤a) :
    (highLevelNext (.D a d) = none) ↔
      a-d-2 ∈ fastSpectrum (d+2) := by
  have ha0 : a≠0 := by omega
  have hnot : ¬(d%2=1 ∧ a≥d+5) := by omega
  have hg : d%2=0 ∧ a≥d+3 := ⟨hd,ha⟩
  have hs : highLevelNext (.D a d) = drainB (a-d-2) (d+2) 2 := by
    simp only [highLevelNext,if_neg ha0,if_neg hnot,if_pos hg]
  rw [hs]
  exact drain_none_iff_fastSpectrum (a-d-2) (d+2) 2

/-- For a fixed odd d, even the complete infinite far-left input ray
contains only the explicitly finite original-source fatal points. -/
theorem odd_left_none_iff_list (a d : Nat) (hd : d%2=1) :
    (d+5≤a ∧ highLevelNext (.D a d)=none) ↔
       a ∈ (fastSpectrum (d+3)).map (fun x => x+d+5) := by
  constructor
  · rintro ⟨ha,hh⟩
    have hx : a-d-5 ∈ fastSpectrum (d+3) :=
      (odd_left_none_iff_spectrum a d hd ha).1 hh
    apply List.mem_map.mpr
    refine ⟨a-d-5,hx,?_⟩
    omega
  · intro hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have ha : d+5≤a := by omega
    have heq : a-d-5=x := by omega
    refine ⟨ha,(odd_left_none_iff_spectrum a d hd ha).2 ?_⟩
    simpa only [heq] using hx

/-- Corresponding exact finite fatal points in every even-d left ray. -/
theorem even_left_none_iff_list (a d : Nat) (hd : d%2=0) :
    (d+3≤a ∧ highLevelNext (.D a d)=none) ↔
       (d+3≤a ∧ a ∈ (fastSpectrum (d+2)).map (fun x => x+d+2)) := by
  constructor
  · rintro ⟨ha,hh⟩
    have hx : a-d-2 ∈ fastSpectrum (d+2) :=
      (even_left_none_iff_spectrum a d hd ha).1 hh
    refine ⟨ha,?_⟩
    apply List.mem_map.mpr
    refine ⟨a-d-2,hx,?_⟩
    omega
  · rintro ⟨ha,hh⟩
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have heq : a-d-2=x := by omega
    refine ⟨ha,(even_left_none_iff_spectrum a d hd ha).2 ?_⟩
    simpa only [heq] using hx

#print axioms odd_left_none_iff_list
#print axioms even_left_none_iff_list
end BB6.Agent49LeftSector
