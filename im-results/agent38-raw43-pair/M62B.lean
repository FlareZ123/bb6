import M62Right
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

theorem outer_first_zero {s : List Bool} (h : OuterTail s) :
    s.headD false = false := by
  cases h <;> rfl

theorem outer_second_zero {s : List Bool} (h : OuterTail s) :
    s.tail.headD false = false := by
  cases h <;> rfl

theorem outer_drop {s : List Bool} (h : OuterTail s) :
    s.tail.tail = s.drop 2 := by
  cases h <;> rfl

theorem word_append {u v : List Bool} (hu : Word u) (hv : Word v) :
    Word (u++v) := by
  induction hu with
  | nil => simpa using hv
  | two k w hw ih =>
      simpa only [List.append_assoc] using Word.two k (w++v) ih
  | four k w hw ih =>
      simpa only [List.append_assoc] using Word.four k (w++v) ih

/-- An arbitrary B terminal, with any number of O frames to its left,
is converted to phase A after its five-zero carry. The only initial
hypothesis is the exact 13-step P macro, so the lemma covers both finite
zero prefixes and the blank right ray without representation shortcuts. -/
theorem carry_b_after_prepare (t s V : List Bool)
    (ht : BFrame t) (hs : OuterTail s) (hv : Word V)
    (z : Z0)
    (hp : run0 table 13 z =
      some ⟨0,ones 2++(t++s),bits "101"++V⟩) :
    ∃ n L' R', 0<n ∧ LeftA L' ∧ RightA R' ∧
      run0 table n z = some (fSection L' R') := by
  have h0 := outer_first_zero hs
  have h00 := outer_second_zero hs
  have hd := outer_drop hs
  have hleft := carry_left hs
  cases ht with
  | base a =>
      have he : ones 2 ++ (ones (5*a+2)++s) =
          ones ((5*a+2)+2)++s := by
        rw [←List.append_assoc,←ones_add]
        have hn : 2+(5*a+2)=(5*a+2)+2 := by omega
        rw [hn]
      have hp' : run0 table 13 z =
          some ⟨0,ones ((5*a+2)+2)++s,bits "101"++V⟩ := by
        simpa only [he] using hp
      have hscan := scan_last (5*a+2) (by omega) s V h0
      have hn : (5*a+2)-1 = 5*a+1 := by omega
      have hscan' : run0 table ((5*a+2)+10)
          ⟨0,ones ((5*a+2)+2)++s,bits "101"++V⟩ =
          some ⟨0,true::s.tail,bits "101"++(zeros (5*a+1)++bits "101"++V)⟩ := by
        simpa only [hn,List.append_assoc] using hscan
      have hfinish :=
        carry_finish s.tail (zeros (5*a+1)++bits "101"++V) h00
      have h := join0 (join0 hp' hscan') hfinish
      have hr : RightA (bits "01"++zeros (5*a+1)++bits "101"++V) :=
        RightA.extended a V hv
      refine ⟨13+(((5*a+2)+10)+4),ones 3++s.drop 2,
        bits "01"++zeros (5*a+1)++bits "101"++V,by omega,
        hleft,hr,?_⟩
      simpa [fSection,bits,hd,List.append_assoc,Nat.add_assoc] using h
  | more c w hw =>
      have he : ones 2 ++ ((ones (5*(c+1))++false::w)++s) =
          ones ((5*(c+1))+2)++(false::w++s) := by
        rw [←List.append_assoc,←List.append_assoc,←ones_add]
        have hn : 2+(5*(c+1))=5*(c+1)+2 := by omega
        rw [hn]
        simp only [List.append_assoc,List.cons_append]
      have hp' : run0 table 13 z =
          some ⟨0,ones ((5*(c+1))+2)++(false::w++s),bits "101"++V⟩ := by
        simpa only [he] using hp
      have hscan := scan_last (5*(c+1)) (by omega)
        (false::w++s) V (by rfl)
      have hn : 5*(c+1)-1 = 5*c+4 := by omega
      have hscan' : run0 table ((5*(c+1))+10)
          ⟨0,ones ((5*(c+1))+2)++(false::w++s),bits "101"++V⟩ =
          some ⟨0,true::(w++s),bits "101"++(w4 c++V)⟩ := by
        simpa only [hn,w4,List.append_assoc,List.cons_append,List.tail_cons] using hscan
      obtain ⟨n,code,hnpos,hcode,hforward⟩ :=
        scan_a hw s (w4 c++V) h0
      have hfinish := carry_finish s.tail (code++w4 c++V) h00
      have h := join0 (join0 (join0 hp' hscan') hforward) (by
        simpa only [List.append_assoc] using hfinish)
      obtain ⟨a,payload,hw0,hcodeeq⟩ := ac_as_prefix hcode
      have hword : Word ((payload++w4 c)++V) :=
        word_append (word_append_w4 hw0 c) hv
      have hright : RightA (bits "01"++zeros (5*a+1)++
          bits "101"++((payload++w4 c)++V)) :=
        RightA.extended a ((payload++w4 c)++V) hword
      refine ⟨13+(((5*(c+1))+10)+n+4),ones 3++s.drop 2,
        bits "01"++zeros (5*a+1)++bits "101"++((payload++w4 c)++V),
        by omega,hleft,hright,?_⟩
      rw [hcodeeq] at h
      simpa [fSection,bits,hd,List.append_assoc,Nat.add_assoc] using h

/-- Whether the first five 0s are explicitly represented or implicit
in the blank suffix makes no mathematical difference to the carry. -/
theorem prepare_five (t s V : List Bool) :
    run0 table 13 (fSection (t++s) (zeros 5++V)) =
      some ⟨0,ones 2++(t++s),bits "101"++V⟩ := by
  simpa [fSection,zeros,bits,List.append_assoc] using carry_prepare (t++s) V

theorem prepare_empty (t s : List Bool) :
    run0 table 13 (fSection (t++s) []) =
      some ⟨0,ones 2++(t++s),bits "101"⟩ := by
  simpa [fSection] using carry_prepare_blank (t++s)

/-- The complete unbounded B→A return, for any B-frame stack,
after the five 0s, with an arbitrary well-formed W suffix. -/
theorem phase_b_carry_five (t s V : List Bool)
    (ht : BFrame t) (hs : OuterTail s) (hv : Word V) :
    ∃ n L' R', 0<n ∧ LeftA L' ∧ RightA R' ∧
      run0 table n (fSection (t++s) (zeros 5++V)) =
        some (fSection L' R') :=
  carry_b_after_prepare t s V ht hs hv _
    (prepare_five t s V)

theorem phase_b_carry_empty (t s : List Bool)
    (ht : BFrame t) (hs : OuterTail s) :
    ∃ n L' R', 0<n ∧ LeftA L' ∧ RightA R' ∧
      run0 table n (fSection (t++s) []) =
        some (fSection L' R') :=
  carry_b_after_prepare t s [] ht hs Word.nil _
    (prepare_empty t s)

#print axioms carry_b_after_prepare
#print axioms phase_b_carry_five
#print axioms phase_b_carry_empty
end BB6.Agent38M62
