import Q0151MacroSteps

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151SourceMacro

/-!
Exact closure algebra for the physical left segments in the q0-151
source macro proof. A segment is scanned from the head leftwards by
one-bits and zero-one pairs, and has a final one (forward orientation).
No abstract finite-state assumptions are used here.
-/

def SegGood (s : List Bool) : Prop :=
  Scan s.reverse ∧ ∃ u, s = u ++ [true]

theorem scan_drop_one {s : List Bool} (h : Scan (true::s)) :
    Scan s := by
  cases h with
  | one hrest => exact hrest

theorem scan_append {a b : List Bool}
    (ha : Scan a.reverse) (hb : Scan b.reverse) :
    Scan (a++b).reverse := by
  simpa [List.reverse_append] using Scan.append hb ha

theorem good_append {a b : List Bool}
    (ha : SegGood a) (hb : SegGood b) : SegGood (a++b) := by
  refine ⟨scan_append ha.1 hb.1,?_⟩
  obtain ⟨u,hu⟩ := hb.2
  exact ⟨a++u,by simp [hu,List.append_assoc]⟩

theorem good_one : SegGood [true] := by
  exact ⟨by exact Scan.one Scan.nil,⟨[],rfl⟩⟩

theorem good_ones_two : SegGood [true,true] := by
  exact ⟨by exact Scan.one (Scan.one Scan.nil),⟨[true],rfl⟩⟩

theorem good_ones_three : SegGood [true,true,true] := by
  exact ⟨by exact Scan.one (Scan.one (Scan.one Scan.nil)),
    ⟨[true,true],rfl⟩⟩

theorem good_ones_four : SegGood [true,true,true,true] := by
  exact ⟨by exact Scan.one (Scan.one (Scan.one (Scan.one Scan.nil))),
    ⟨[true,true,true],rfl⟩⟩

theorem good_alt_two (n : Nat) :
    SegGood (alt n ++ [true,true]) := by
  refine ⟨?_,⟨alt n ++ [true],by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append,alt_reverse] using
    (Scan.one (Scan.one (scanAlt n)))

theorem good_alt_three (n : Nat) :
    SegGood (alt n ++ [true,true,true]) := by
  refine ⟨?_,⟨alt n ++ [true,true],by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append,alt_reverse] using
    (Scan.one (Scan.one (Scan.one (scanAlt n))))

theorem good_append_odd_one (s : List Bool) (hs : SegGood s) :
    SegGood (s ++ [false,true]) := by
  obtain ⟨u,hu⟩ := hs.2
  subst s
  have hpre : Scan u.reverse := by
    have h : Scan (true :: u.reverse) := by
      simpa [List.reverse_append] using hs.1
    exact scan_drop_one h
  refine ⟨?_,⟨u ++ [true,false],by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append,List.append_assoc] using
    (Scan.one (Scan.pair hpre))

theorem good_append_alt_two (s : List Bool) (hs : SegGood s) (n : Nat) :
    SegGood (s ++ alt n ++ [true,true]) := by
  simpa [List.append_assoc] using good_append hs (good_alt_two n)

theorem good_append_alt_three (s : List Bool) (hs : SegGood s) (n : Nat) :
    SegGood (s ++ alt n ++ [true,true,true]) := by
  simpa [List.append_assoc] using good_append hs (good_alt_three n)

theorem good_append_four (s : List Bool) (hs : SegGood s) :
    SegGood (s ++ [true,true,true,true]) :=
  good_append hs good_ones_four

theorem good_two_zero_suffix (n : Nat) :
    SegGood ([true,true,true,false] ++ alt n ++ [true,true]) := by
  have ht : Scan ([false,true,true,true] : List Bool) :=
    Scan.pair (Scan.one (Scan.one Scan.nil))
  have hr : Scan ([true,true] ++ revAlt n ++ [false,true,true,true]) :=
    Scan.one (Scan.one (Scan.append (scanAlt n) ht))
  refine ⟨?_,⟨[true,true,true,false] ++ alt n ++ [true],by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append,alt_reverse,List.append_assoc] using hr

theorem good_append_two_zero (s : List Bool) (hs : SegGood s) (n : Nat) :
    SegGood (s ++ [true,true,true,false] ++ alt n ++ [true,true]) := by
  simpa [List.append_assoc] using good_append hs (good_two_zero_suffix n)

theorem good_c_end_trim (s : List Bool)
    (hs : Scan (s ++ [true,true,true]).reverse) :
    SegGood (s ++ [true,true]) := by
  have hpre : Scan s.reverse := by
    have h : Scan (true :: true :: true :: s.reverse) := by
      simpa [List.reverse_append] using hs
    exact scan_drop_one (scan_drop_one (scan_drop_one h))
  refine ⟨?_,⟨s++[true],by simp [List.append_assoc]⟩⟩
  simpa [List.reverse_append] using
    (Scan.one (Scan.one hpre))

#print axioms good_append
#print axioms good_alt_two
#print axioms good_alt_three
#print axioms good_append_odd_one
#print axioms good_append_alt_two
#print axioms good_append_alt_three
#print axioms good_two_zero_suffix
#print axioms good_append_two_zero
#print axioms good_c_end_trim
end BB6.Agent5Q0151SegmentGrammar
