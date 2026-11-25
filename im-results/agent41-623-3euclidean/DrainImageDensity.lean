import DrainImageAP

namespace BB6.Agent41DrainImageDecoder

def evenGate (E : Nat → Nat) (b : Nat) : Nat :=
  image E b + (if b%2=0 then 2 else 3)

def oddGate (E : Nat → Nat) (b : Nat) : Nat :=
  image E b + (if b%2=0 then 5 else 0)

/-- The three consecutive same-parity blocks b, b+2, b+4
with b≡2 mod 3 have image differences 8 and 10. -/
theorem triple_offsets {E : Nat → Nat} (he : ExcessLaws E)
    (b : Nat) (hb : b%3=2) :
    image E (b+2)= image E b+8 ∧
    image E (b+4)= image E b+10 := by
  have h0 := image_gap_eight he b hb
  have h1 := (image_min_gap he (b+2)).2.mpr (by omega)
  rw [show b+2+2=b+4 by omega] at h1
  omega

def pickMod (v r : Nat) : Nat :=
  if v%6= r then v else if (v+8)%6= r then v+8 else v+10

theorem pickMod_complete (v r w : Nat)
    (hw : w= v ∨ w= v+8 ∨ w= v+10) (hr : w%6= r) :
    w= pickMod v r := by
  unfold pickMod
  split <;> (try split) <;> omega

def gatePair (E : Nat → Nat) (q : Nat) : List Nat :=
  [pickMod (evenGate E (3*q-1)) 2,
   pickMod (oddGate E (3*q-1)) 1]

/-- Every gate hit in a same-parity triple that satisfies the immediate
halting congruence occurs in a list of just two rows. -/
theorem gatePair_complete {E : Nat → Nat} (he : ExcessLaws E)
    (q b d : Nat) (hq : 0 < q)
    (hb : b=3*q-1 ∨ b=3*q+1 ∨ b=3*q+3)
    (hd : (d= evenGate E b ∧ d%6=2) ∨ (d= oddGate E b ∧ d%6=1)) :
    d ∈ gatePair E q := by
  let a := 3*q-1
  have ha : a%3=2 := by dsimp [a]; omega
  have hab : b= a ∨ b= a+2 ∨ b= a+4 := by dsimp [a]; omega
  obtain ⟨h0,h1⟩ := triple_offsets he a ha
  have hp : b%2= a%2 := by omega
  unfold gatePair
  change d ∈ [pickMod (evenGate E a) 2,pickMod (oddGate E a) 1]
  rcases hd with ⟨hd,hr⟩|⟨hd,hr⟩
  · have ho : d= evenGate E a ∨ d= evenGate E a+8 ∨ d= evenGate E a+10 := by
      unfold evenGate at hd ⊢
      rw [hp] at hd
      rcases hab with h|h|h
      · rw [h] at hd; omega
      · rw [h,h0] at hd; omega
      · rw [h,h1] at hd; omega
    simp [pickMod_complete _ _ _ ho hr]
  · have ho : d= oddGate E a ∨ d= oddGate E a+8 ∨ d= oddGate E a+10 := by
      unfold oddGate at hd ⊢
      rw [hp] at hd
      rcases hab with h|h|h
      · rw [h] at hd; omega
      · rw [h,h0] at hd; omega
      · rw [h,h1] at hd; omega
    simp [pickMod_complete _ _ _ ho hr]

def gateCover (E : Nat → Nat) : Nat → List Nat
  | 0 => [1,2,7,8,13,14]
  | Q+1 => gateCover E Q ++ gatePair E (Q+1)

theorem gateCover_length (E : Nat → Nat) (Q : Nat) :
    (gateCover E Q).length=2*Q+6 := by
  induction Q with
  | zero => rfl
  | succ Q ih => simp [gateCover,gatePair,ih]; omega

theorem gatePair_mem_cover (E : Nat → Nat) (Q q d : Nat)
    (hq : 0 < q) (hq' : q≤ Q) (hd : d ∈ gatePair E q) :
    d ∈ gateCover E Q := by
  induction Q with
  | zero => omega
  | succ Q ih =>
    rw [gateCover,List.mem_append]
    by_cases h : q= Q+1
    · exact Or.inr (h ▸ hd)
    · exact Or.inl (ih (by omega))

theorem small_terminal_cover (E : Nat → Nat) (Q d : Nat)
    (hd : d≤14) (hr : d%6=1 ∨ d%6=2) :
    d ∈ gateCover E Q := by
  induction Q with
  | zero =>
    simp [gateCover]; omega
  | succ Q ih => simp only [gateCover,List.mem_append]; exact Or.inl ih

theorem gate_hit_of_unblocked {E : Nat → Nat} (he : ExcessLaws E)
    (d : Nat) (hd : 14 < d) (hr : d%6=1 ∨ d%6=2)
    (h : ¬blocked d) :
    ∃ b, 3*b≤ d ∧ ((d= evenGate E b ∧ d%6=2) ∨ (d= oddGate E b ∧ d%6=1)) := by
  unfold blocked at h
  by_cases hp : d%2=0
  · rw [if_pos hp] at h
    have hr' : d%6=2 := by omega
    by_cases h0 : inverse (d-2)= none
    · have h1 : inverse (d-3)≠none := by intro hh; exact h ⟨h0,hh⟩
      cases hi : inverse (d-3) with
      | none => contradiction
      | some b =>
        have hh := inverse_sound he _ _ hi
        change image E b = _ at hh
        have hb := image_parity he b
        have hb' : b%2≠0 := by omega
        have hb0 : 3*b≤ image E b := by unfold image; omega
        refine ⟨b,?_,Or.inl ⟨?_,hr'⟩⟩
        · omega
        · unfold evenGate; rw [if_neg hb']; omega
    · cases hi : inverse (d-2) with
      | none => contradiction
      | some b =>
        have hh := inverse_sound he _ _ hi
        change image E b = _ at hh
        have hb := image_parity he b
        have hb' : b%2=0 := by omega
        have hb0 : 3*b≤ image E b := by unfold image; omega
        refine ⟨b,?_,Or.inl ⟨?_,hr'⟩⟩
        · omega
        · unfold evenGate; rw [if_pos hb']; omega
  · rw [if_neg hp] at h
    have hr' : d%6=1 := by omega
    by_cases h0 : inverse (d-5)= none
    · have h1 : inverse d≠none := by intro hh; exact h ⟨h0,hh⟩
      cases hi : inverse d with
      | none => contradiction
      | some b =>
        have hh := inverse_sound he _ _ hi
        change image E b = _ at hh
        have hb := image_parity he b
        have hb' : b%2≠0 := by omega
        have hb0 : 3*b≤ image E b := by unfold image; omega
        refine ⟨b,?_,Or.inr ⟨?_,hr'⟩⟩
        · omega
        · unfold oddGate; rw [if_neg hb']; omega
    · cases hi : inverse (d-5) with
      | none => contradiction
      | some b =>
        have hh := inverse_sound he _ _ hi
        change image E b = _ at hh
        have hb := image_parity he b
        have hb' : b%2=0 := by omega
        have hb0 : 3*b≤ image E b := by unfold image; omega
        refine ⟨b,?_,Or.inr ⟨?_,hr'⟩⟩
        · omega
        · unfold oddGate; rw [if_pos hb']; omega

theorem base_gates_small {E : Nat → Nat} (he : ExcessLaws E)
    (b d : Nat) (hb : b=0 ∨ b=1 ∨ b=3)
    (hd : (d= evenGate E b ∧ d%6=2) ∨ (d= oddGate E b ∧ d%6=1)) :
    d≤14 := by
  have h0 := he.zero
  have h1 := he.r1 0
  have h3 := he.r0 1 (by decide)
  have h1' : E 1=4 := by simp [h0] at h1; omega
  have h3' : E 3=0 := by simpa [h0] using h3
  rcases hb with h|h|h <;> subst b <;>
    simp [evenGate,oddGate,image,h0,h1',h3'] at hd <;> omega

theorem gateCover_complete {E : Nat → Nat} (he : ExcessLaws E)
    (Q d : Nat) (hd : d < 9*Q) (hr : d%6=1 ∨ d%6=2)
    (h : ¬(14 < d ∧ blocked d)) :
    d ∈ gateCover E Q := by
  by_cases hsmall : d≤14
  · exact small_terminal_cover E Q d hsmall hr
  · have hn : ¬blocked d := by intro hh; exact h ⟨by omega,hh⟩
    obtain ⟨b,hb,hgate⟩ := gate_hit_of_unblocked he d (by omega) hr hn
    by_cases hbase : b=0 ∨ b=1 ∨ b=3
    · have hh := base_gates_small he b d hbase hgate
      omega
    · have hq : ∃ q, 0 < q ∧ q≤ Q ∧ (b=3*q-1 ∨ b=3*q+1 ∨ b=3*q+3) := by
        have hm : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
        rcases hm with hm|hm|hm
        · exact ⟨b/3-1,by omega,by omega,Or.inr (Or.inr (by omega))⟩
        · exact ⟨b/3,by omega,by omega,Or.inr (Or.inl (by omega))⟩
        · exact ⟨b/3+1,by omega,by omega,Or.inl (by omega)⟩
      obtain ⟨q,hq,hq',hqb⟩ := hq
      exact gatePair_mem_cover E Q q d hq hq' (gatePair_complete he q b d hq hqb hgate)

def terminalRows : Nat → List Nat
  | 0 => []
  | n+1 => terminalRows n ++ [6*n+1,6*n+2]

theorem terminalRows_length (n : Nat) : (terminalRows n).length=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [terminalRows,ih]; omega

theorem terminalRows_mem (n d : Nat) :
    d ∈ terminalRows n ↔ d < 6*n ∧ (d%6=1 ∨ d%6=2) := by
  induction n with
  | zero => simp [terminalRows]
  | succ n ih =>
    simp [terminalRows,ih]
    omega

theorem terminalRows_nodup (n : Nat) : (terminalRows n).Nodup := by
  induction n with
  | zero => simp [terminalRows]
  | succ n ih =>
    rw [terminalRows,List.nodup_append]
    refine ⟨ih,by simp,?_⟩
    intro d hd c hc heq
    have h := (terminalRows_mem n d).mp hd
    simp at hc
    omega

def isGoodTerminal (d : Nat) : Bool := decide (14 < d ∧ blocked d)

def goodTerminalRows (N : Nat) : List Nat :=
  (terminalRows (3*N)).filter isGoodTerminal

private theorem filter_partition_length (p : Nat → Bool) (l : List Nat) :
    (l.filter p).length+(l.filter (fun d => !p d)).length= l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a= true <;> simp [h,ih] <;> omega

/-- A finite lower bound that implies lower asymptotic density 1/9.
At least 2N-6 distinct rows below 18N are blocked, satisfy the
terminal congruence, and are above 14. -/
theorem goodTerminalRows_count {E : Nat → Nat} (he : ExcessLaws E)
    (N : Nat) : 2*N≤ (goodTerminalRows N).length+6 := by
  let bad := (terminalRows (3*N)).filter (fun d => !isGoodTerminal d)
  have hn : bad.Nodup := (List.filter_sublist).nodup (terminalRows_nodup (3*N))
  have hsub : bad ⊆ gateCover E (2*N) := by
    intro d hd
    have hh := List.mem_filter.mp hd
    obtain ⟨hbound,hmod⟩ := (terminalRows_mem _ _).mp hh.1
    have hb : ¬(14 < d ∧ blocked d) := by
      have hfalse := hh.2
      simp [isGoodTerminal] at hfalse
      rcases hfalse with h|h <;> intro hh
      · omega
      · exact h hh.2
    exact gateCover_complete he _ d (by omega) hmod hb
  have hlen := hn.length_le_of_subset hsub
  rw [gateCover_length] at hlen
  have hp := filter_partition_length isGoodTerminal (terminalRows (3*N))
  rw [terminalRows_length] at hp
  change (goodTerminalRows N).length+bad.length=2*(3*N) at hp
  omega

theorem goodTerminalRows_spec (N d : Nat) (hd : d ∈ goodTerminalRows N) :
    d < 18*N ∧ 14 < d ∧ (d%6=1 ∨ d%6=2) ∧ blocked d := by
  have hh := List.mem_filter.mp hd
  have h := (terminalRows_mem _ _).mp hh.1
  have hg := hh.2
  simp [isGoodTerminal] at hg
  exact ⟨by omega,hg.1,h.2,hg.2⟩

theorem goodTerminalRows_nodup (N : Nat) : (goodTerminalRows N).Nodup :=
  List.filter_sublist.nodup (terminalRows_nodup _)

#print axioms goodTerminalRows_count
#print axioms goodTerminalRows_spec
#print axioms goodTerminalRows_nodup

end BB6.Agent41DrainImageDecoder
