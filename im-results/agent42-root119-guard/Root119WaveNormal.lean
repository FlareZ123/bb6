import Root119Wave
set_option linter.unusedSimpArgs false
namespace BB6Root119

def dfTouched (n : Nat) (c : Conf) (x : Int) : Prop :=
  ∃ i : Nat, i < n ∧ x = c.h+1+2*(i:Int)

def fbTouched (n : Nat) (c : Conf) (x : Int) : Prop :=
  ∃ i : Nat, i < n ∧ x = c.h-2*(i:Int)

theorem df_many_unvisited (n : Nat) (c : Conf) (x : Int)
    (hn : ¬dfTouched n c x) : (dfMany n c).tape x = c.tape x := by
  induction n generalizing c with
  | zero => simp [dfMany]
  | succ n ih =>
    have hn0 : x ≠ c.h+1 := by
      intro heq
      apply hn
      exact ⟨0,by omega,by simpa using heq⟩
    have hnt : ¬dfTouched n (dfPair c) x := by
      rintro ⟨i,hi,hx⟩
      apply hn
      refine ⟨i+1,by omega,?_⟩
      change x = c.h+2+1+2*(i:Int) at hx
      have heq : c.h+2+1+2*(i:Int) = c.h+1+2*((i+1:Nat):Int) := by omega
      rw [←heq]
      exact hx
    change (dfMany n (dfPair c)).tape x = c.tape x
    rw [ih (dfPair c) hnt]
    exact dfPair_left c x hn0

theorem fb_many_preserves_right (n : Nat) (c : Conf) (x : Int)
    (hx : c.h < x) : (fbMany n c).tape x = c.tape x := by
  induction n generalizing c with
  | zero => simp [fbMany]
  | succ n ih =>
    change (fbMany n (fbPair c)).tape x = c.tape x
    rw [ih (fbPair c) (by change c.h-2 < x; omega)]
    simp [fbPair,setBit,show x ≠ c.h by omega]

theorem fb_many_written (n : Nat) (c : Conf) (i : Nat) (hi : i < n) :
    (fbMany n c).tape (c.h-2*(i:Int)) = true := by
  induction n generalizing c i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      change (fbMany n (fbPair c)).tape (c.h-2*(0:Int)) = true
      rw [fb_many_preserves_right n (fbPair c) (c.h-2*(0:Int)) (by simp [fbPair] <;> omega)]
      simp [fbPair,setBit]
    | succ i =>
      have ht : i < n := by omega
      change (fbMany n (fbPair c)).tape (c.h-2*((i+1:Int))) = true
      have heq : c.h-2*((i+1:Int)) = (fbPair c).h-2*(i:Int) := by change c.h-2*((i+1:Int)) = c.h-2-2*(i:Int); omega
      rw [heq]
      exact ih (fbPair c) i ht

theorem fb_many_unvisited (n : Nat) (c : Conf) (x : Int)
    (hn : ¬fbTouched n c x) : (fbMany n c).tape x = c.tape x := by
  induction n generalizing c with
  | zero => simp [fbMany]
  | succ n ih =>
    have hn0 : x ≠ c.h := by
      intro heq
      apply hn
      exact ⟨0,by omega,by simpa using heq⟩
    have hnt : ¬fbTouched n (fbPair c) x := by
      rintro ⟨i,hi,hx⟩
      apply hn
      refine ⟨i+1,by omega,?_⟩
      change x = c.h-2-2*(i:Int) at hx
      have heq : c.h-2-2*(i:Int) = c.h-2*((i+1:Nat):Int) := by omega
      rw [←heq]
      exact hx
    change (fbMany n (fbPair c)).tape x = c.tape x
    rw [ih (fbPair c) hnt]
    simp [fbPair,setBit,hn0]

theorem waveF_head (n : Nat) (c : Conf) :
    (waveF n c).h = c.h+2*(n:Int)+2 := by
  change (dfMany n (waveD c)).h+1 = c.h+2*(n:Int)+2
  rw [dfMany_head]
  change c.h+1+2*(n:Int)+1 = c.h+2*(n:Int)+2
  omega

theorem wave_df_subset_fb (n : Nat) (c : Conf) (x : Int)
    (ht : dfTouched n (waveD c) x) :
    fbTouched (n+1) (waveF n c) x := by
  obtain ⟨i,hi,hx⟩ := ht
  have hj : n-i < n+1 := by omega
  refine ⟨n-i,hj,?_⟩
  rw [waveF_head]
  change x = c.h+1+1+2*(i:Int) at hx
  omega

theorem wave_fb_written_old (n : Nat) (c : Conf) (x : Int)
    (hv : waveValid n c)
    (ht : fbTouched (n+1) (waveF n c) x)
    (hne : x ≠ c.h+2*(n:Int)+2) :
    c.tape x = true := by
  obtain ⟨hq,h0,hleft,hones,hend⟩ := hv
  obtain ⟨i,hi,hx⟩ := ht
  have hi0 : i ≠ 0 := by
    intro heq
    subst i
    apply hne
    rw [waveF_head] at hx
    simpa using hx
  have hb : 2*(n-i)+1 < 2*n+1 := by omega
  have ho := hones (2*(n-i)+1) hb
  have heq : x = c.h+1+((2*(n-i)+1:Nat):Int) := by
    rw [waveF_head] at hx
    omega
  rw [heq]
  exact ho

/-- Exact full-tape wave normal form: restore every cell except the far-end zero. -/
theorem waveB_tape_normal (n : Nat) (c : Conf) (hv : waveValid n c) :
    (waveB n c).tape = setBit c.tape (c.h+2*(n:Int)+2) true := by
  funext x
  have hh := wave_FB_endpoint_head n c
  change (setBit (fbMany (n+1) (waveF n c)).tape
     (fbMany (n+1) (waveF n c)).h true) x =
    setBit c.tape (c.h+2*(n:Int)+2) true x
  rw [hh]
  by_cases hH : x=c.h
  · subst x
    have hon : c.tape c.h = true := hv.2.1
    simp [setBit,show c.h ≠ c.h+2*(n:Int)+2 by omega,hon]
  · have leftSet : setBit (fbMany (n+1) (waveF n c)).tape c.h true x =
        (fbMany (n+1) (waveF n c)).tape x := by
      simp [setBit,hH]
    rw [leftSet]
    by_cases hvisited : fbTouched (n+1) (waveF n c) x
    · obtain ⟨i,hi,hx⟩ := hvisited
      have hw := fb_many_written (n+1) (waveF n c) i hi
      rw [←hx] at hw
      rw [hw]
      by_cases hend : x=c.h+2*(n:Int)+2
      · simp [setBit,hend]
      · have hOld := wave_fb_written_old n c x hv ⟨i,hi,hx⟩ hend
        simp [setBit,hend,hOld]
    · have hnotdf : ¬dfTouched n (waveD c) x := by
        intro ht
        exact hvisited (wave_df_subset_fb n c x ht)
      rw [fb_many_unvisited (n+1) (waveF n c) x hvisited]
      change (dfMany n (waveD c)).tape x = setBit c.tape (c.h+2*(n:Int)+2) true x
      rw [df_many_unvisited n (waveD c) x hnotdf]
      change setBit c.tape c.h false x = setBit c.tape (c.h+2*(n:Int)+2) true x
      have he : x ≠ c.h+2*(n:Int)+2 := by
        intro e
        apply hvisited
        refine ⟨0,by omega,?_⟩
        rw [waveF_head]
        simpa using e
      simp [setBit,hH,he]

#print axioms BB6Root119.waveB_tape_normal
#print axioms BB6Root119.df_many_unvisited
#print axioms BB6Root119.fb_many_unvisited
#print axioms BB6Root119.fb_many_written
end BB6Root119
