import H1784Tape

namespace BB6Coverage.Agent48.H1784
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem rep_add (p : List Bool) (m n : Nat) :
    rep p (m+n) = rep p m ++ rep p n := by
  induction m with
  | zero => simp [rep]
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem rep_double (p : List Bool) (n : Nat) :
    rep (p++p) n = rep p (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (p++p) ++ rep (p++p) n = rep p (2*(n+1))
    rw [ih,show 2*(n+1)=2+2*n by omega,rep_add p 2 (2*n)]
    simp only [rep,List.append_nil]

theorem rep_end (p R : List Bool) (n : Nat) :
    rep p n ++ (p ++ R) = rep p (n+1) ++ R := by
  rw [← List.append_assoc (rep p n) p R,rep_snoc]
  rfl

abbrev ones (n : Nat) := rep [true] n
abbrev zeros (n : Nat) := rep [false] n

def enc : List Bool → List Bool
  | [] => []
  | false::w => E0 ++ enc w
  | true::w => E1 ++ enc w

def B (w : List Bool) : List Bool := W ++ enc w

theorem enc_append (w z : List Bool) : enc (w++z)=enc w++enc z := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [enc,ih,List.append_assoc]

theorem enc_ones (u : Nat) : enc (ones u)=rep E1 u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [rep,List.cons_append,List.nil_append,enc,ih]

theorem enc_zeros (u : Nat) : enc (zeros u)=rep E0 u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [rep,List.cons_append,List.nil_append,enc,ih]

theorem word_zeros (u : Nat) (w : List Bool) :
    B (zeros u ++ true::w) = W ++ rep E0 u ++ W ++ B w := by
  simp only [B,enc_append,enc_zeros,enc,List.append_assoc]
  rfl

theorem word_ones (u : Nat) (w : List Bool) :
    B (ones u ++ false::w) = rep W (2*u+1) ++ E0 ++ enc w := by
  unfold B
  rw [enc_append,enc_ones]
  simp only [enc,List.append_assoc]
  rw [show E1 = W++W by rfl,rep_double]
  rw [show 2*u+1=1+2*u by omega,rep_add]
  simp only [rep,List.append_nil,List.append_assoc]

theorem word_all (u : Nat) : B (ones u)=rep W (2*u+1) := by
  unfold B
  rw [enc_ones,show E1=W++W by rfl,rep_double]
  rw [show 2*u+1=1+2*u by omega,rep_add]
  simp only [rep,List.append_nil]

theorem right_carry (u : Nat) : H ++ rep H (2*u+1) = rep V (u+1) := by
  rw [show V=H++H by rfl,rep_double,show 2*(u+1)=2*u+1+1 by omega]
  rfl

theorem scan_rot (u : Nat) :
    false :: (rep K u ++ [true,true,false,true]) = U ++ rep U u ++ [true] := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change U ++ (false :: (rep K u ++ [true,true,false,true])) =
      U ++ (U ++ rep U u) ++ [true]
    rw [ih]
    simp only [List.append_assoc]

theorem scan_word (u : Nat) (L : List Bool) :
    [false,true,true,false,false] ++ rep K u ++ [true,true,false,true] ++ L =
      U ++ U ++ rep U u ++ [true] ++ L := by
  have h := congrArg (fun v : List Bool => U ++ v ++ L) (scan_rot u)
  simpa only [List.cons_append,List.nil_append,List.append_assoc] using h

theorem left_rot (u : Nat) :
    false :: (rep U u ++ [true]) = rep E0 u ++ W := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change E0 ++ (false :: (rep U u ++ [true])) = (E0 ++ rep E0 u) ++ W
    rw [ih]
    simp only [List.append_assoc]

theorem over_word (u : Nat) :
    [false,false] ++ rep K u ++ [true,true] = rep E0 (u+1) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change E0 ++ ([false,false] ++ rep K u ++ [true,true]) = E0 ++ rep E0 (u+1)
    rw [ih]

theorem over_right (u : Nat) (R : List Bool) :
    rep H (2*u+1) ++ (Q ++ R) = rep V (u+1) ++ ([true,true,false] ++ R) := by
  calc
    _ = (rep H (2*u+1) ++ H) ++ [true,true,false] ++ R := by
      simp only [List.append_assoc]
      rfl
    _ = (H ++ rep H (2*u+1)) ++ [true,true,false] ++ R := by rw [rep_snoc]
    _ = _ := by rw [right_carry]; simp only [List.append_assoc]

def Y (w : List Bool) (j : Nat) (T : List Bool) : Z0 :=
  A (B w) (rep Q j ++ T)
def X (w : List Bool) (u j : Nat) (T : List Bool) : Z0 :=
  A (B w) (rep V (u+1) ++ rep Q (j+1) ++ T)

abbrev T101 : List Bool := [true,false,true]
abbrev T11 : List Bool := [true,true]
def aux (i : Nat) : List Bool := [true,false,false] ++ rep Q i ++ [true]
def tail110 (i : Nat) : List Bool := [true,true,false] ++ rep Q i ++ [true]

theorem x_core (u j : Nat) (L T T' : List Bool) (c : Nat)
    (turn : ∀ M, RRun c (A M T) (D M T')) :
    RRun (6+6*u+7+7*j+c+7*j+9)
      (A L (rep V (u+1) ++ rep Q (j+1) ++ T))
      (A (W ++ rep E0 u ++ W ++ L) (rep Q (j+1) ++ T')) := by
  have h1 := af_one L (rep V u ++ Q ++ rep Q j ++ T)
  have h1' : run0 ctr 6 (A L (rep V (u+1) ++ rep Q (j+1) ++ T)) =
      some (F ([true,true,false,true]++L) (rep V u ++ Q ++ rep Q j ++ T)) := by
    simpa only [rep,List.append_assoc] using h1
  have h2 := f_sweep u ([true,true,false,true]++L) (Q++rep Q j++T)
  have h3 := fa_one (rep K u++[true,true,false,true]++L) (rep Q j++T)
  have h3' : run0 ctr 7 (F (rep K u++[true,true,false,true]++L) (Q++rep Q j++T)) =
      some (A (U++U++rep U u++[true]++L) (rep Q j++T)) := by
    rw [← scan_word]
    exact h3
  have h4 := q_sweep j (U++U++rep U u++[true]++L) T
  have h5 := turn (rep P j++U++U++rep U u++[true]++L)
  have h6 := p_sweep j (U++U++rep U u++[true]++L) T'
  have h7 := x_finish (false::(rep U u++[true]++L)) (rep Q j++T')
  have hleft : W ++ (false::(rep U u++[true]++L)) =
      W++rep E0 u++W++L := by
    have h := congrArg (fun v : List Bool => W ++ v ++ L) (left_rot u)
    simpa only [List.cons_append,List.append_assoc] using h
  rw [hleft] at h7
  have h7' : run0 ctr 9 (D (U++U++rep U u++[true]++L) (rep Q j++T')) =
      some (A (W++rep E0 u++W++L) (rep Q (j+1)++T')) := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using h7
  simp only [List.append_assoc] at h1' h2 h3' h4 h5 h6 h7' ⊢
  exact rjoin (rjoin (rjoin (rjoin (rjoin (rjoin (exactR h1') (exactR h2)) (exactR h3')) (exactR h4)) h5) (exactR h6)) (exactR h7')

theorem x_step (w : List Bool) (u j : Nat) (T T' : List Bool) (c : Nat)
    (turn : ∀ M, RRun c (A M T) (D M T')) :
    Live (X w u j T) (Y (zeros u++true::w) (j+1) T') := by
  refine ⟨6+6*u+7+7*j+c+7*j+9,by omega,?_⟩
  simpa only [X,Y,word_zeros] using x_core u j (B w) T T' c turn

theorem y_core (u j : Nat) (L T T' : List Bool) (c : Nat)
    (turn : ∀ M, RRun c (A M T) (D M T')) :
    RRun (7*j+c+7*j+2*(2*u+1)+4)
      (A (rep W (2*u+1)++E0++L) (rep Q j++T))
      (A (W++L) (rep V (u+1)++rep Q j++T')) := by
  have h1 := q_sweep j (rep W (2*u+1)++E0++L) T
  have h2 := turn (rep P j++rep W (2*u+1)++E0++L)
  have h3 := p_sweep j (rep W (2*u+1)++E0++L) T'
  have h4 := w_sweep (2*u+1) (E0++L) (rep Q j++T')
  have h5 := b_finish L (rep H (2*u+1)++rep Q j++T')
  have h5' : run0 ctr 4 (D (E0++L) (rep H (2*u+1)++rep Q j++T')) =
      some (A (W++L) (rep V (u+1)++rep Q j++T')) := by
    have h := congrArg (fun v : List Bool => v ++ rep Q j ++ T') (right_carry u)
    rw [← h]
    simpa only [List.append_assoc] using h5
  simp only [List.append_assoc] at h1 h2 h3 h4 h5' ⊢
  exact rjoin (rjoin (rjoin (rjoin (exactR h1) h2) (exactR h3)) (exactR h4)) (exactR h5')

theorem y_step (u j : Nat) (w T T' : List Bool) (c : Nat)
    (turn : ∀ M, RRun c (A M T) (D M T')) :
    Live (Y (ones u++false::w) j T)
      (A (B w) (rep V (u+1)++rep Q j++T')) := by
  refine ⟨7*j+c+7*j+2*(2*u+1)+4,by omega,?_⟩
  unfold Y
  rw [word_ones]
  exact y_core u j (enc w) T T' c turn

theorem main_inc (u j : Nat) (w : List Bool) :
    Live (Y (ones u++false::w) j T101) (Y (zeros u++true::w) (j+1) T101) := by
  have h := y_step u j w T101 (Q++[true]) 16 (fun M => exactR (turn101 M))
  have h' : Live (Y (ones u++false::w) j T101) (X w u j [true]) := by
    simpa only [X,List.append_assoc,rep_end] using h
  exact live_join h' (x_step w u j [true] T101 8 (fun M => exactR (turn1 M)))

theorem aux_inc (u j i : Nat) (w : List Bool) :
    Live (Y (ones u++false::w) j (aux (i+1)))
      (Y (zeros u++true::w) (j+1) (aux i)) := by
  have ht (M : List Bool) : RRun 8 (A M (aux (i+1))) (D M (Q++tail110 i)) :=
    exactR (turn100 M (rep Q (i+1)++[true]))
  have h := y_step u j w (aux (i+1)) (Q++tail110 i) 8 ht
  have h' : Live (Y (ones u++false::w) j (aux (i+1))) (X w u j (tail110 i)) := by
    simpa only [X,List.append_assoc,rep_end] using h
  exact live_join h' (x_step w u j (tail110 i) (aux i) 4
    (fun M => exactR (turn110 M (rep Q i++[true]))))

theorem aux_end (u j : Nat) (w : List Bool) :
    Live (Y (ones u++false::w) j (aux 0))
      (Y (zeros u++true::w) (j+1) T11) := by
  have ht (M : List Bool) : RRun 8 (A M (aux 0)) (D M [true,false,true,true]) :=
    exactR (turn100 M [true])
  obtain ⟨n,hn,h⟩ := y_step u j w (aux 0) [true,false,true,true] 8 ht
  have he : EqZ (A (B w) (rep V (u+1)++rep Q j++[true,false,true,true])) (X w u j []) := by
    refine ⟨rfl,same_refl _,?_⟩
    change Same (rep V (u+1)++rep Q j++[true,false,true,true])
      (rep V (u+1)++rep Q (j+1)++[])
    simp only [List.append_assoc]
    rw [← rep_end Q [] j]
    simp only [List.append_nil]
    exact same_append (rep V (u+1)) (same_append (rep Q j) (same_zero [true,false,true,true]))
  exact live_join ⟨n,hn,reframe h he⟩ (x_step w u j [] T11 6 (fun M => exactR (turn0 M)))

theorem turn_inc (u j : Nat) (w : List Bool) :
    Live (Y (ones u++false::w) (j+1) T11)
      (Y (zeros u++true::w) (j+1) T101) := by
  have h := y_step u (j+1) w T11 [true] 4 turn11
  exact live_join h (x_step w u j [true] T101 8 (fun M => exactR (turn1 M)))

theorem main_over (u j : Nat) :
    Live (Y (ones u) j T101) (Y (zeros (u+1)) 0 (aux j)) := by
  have h1 := q_sweep j (B (ones u)) T101
  have h2 := turn101 (rep P j++B (ones u))
  have h3 := p_sweep j (B (ones u)) (Q++[true])
  have h3' : run0 ctr (7*j) (D (rep P j++B (ones u)) (Q++[true])) =
      some (D (rep W (2*u+1)) (Q++rep Q j++[true])) := by
    simpa only [word_all,List.append_assoc,rep_end,rep] using h3
  have h4 := w_sweep (2*u+1) [] (Q++rep Q j++[true])
  have h4' : run0 ctr (2*(2*u+1)) (D (rep W (2*u+1)) (Q++rep Q j++[true])) =
      some (D [] (rep V (u+1)++[true,true,false]++rep Q j++[true])) := by
    simpa only [List.append_nil,List.append_assoc,over_right] using h4
  have h5 := over_turn (rep V (u+1)++[true,true,false]++rep Q j++[true])
  have h6 := f_sweep (u+1) [true,true] ([true,true,false]++rep Q j++[true])
  have h7 := over_finish ([true,false,false]++rep K u++[true,true]) (rep Q j++[true])
  have h7' : run0 ctr 6 (F (rep K (u+1)++[true,true]) ([true,true,false]++rep Q j++[true])) =
      some (Y (zeros (u+1)) 0 (aux j)) := by
    unfold Y B aux
    rw [enc_zeros]
    simp only [rep,List.nil_append]
    have e := congrArg (fun v : List Bool => W ++ v) (over_word u)
    have g : false :: ([true,false,false]++rep K u++[true,true]) =
        W ++ rep E0 (u+1) := e
    rw [g] at h7
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using h7
  refine ⟨7*j+16+7*j+2*(2*u+1)+6+6*(u+1)+6,by omega,?_⟩
  simp only [List.append_assoc] at h1 h2 h3' h4' h5 h6 h7' ⊢
  exact rjoin (rjoin (rjoin (rjoin (rjoin (rjoin (exactR h1) (exactR h2)) (exactR h3')) (exactR h4')) h5) (exactR h6)) (exactR h7')

#print axioms main_inc
#print axioms aux_inc
#print axioms aux_end
#print axioms turn_inc
#print axioms main_over

end BB6Coverage.Agent48.H1784
