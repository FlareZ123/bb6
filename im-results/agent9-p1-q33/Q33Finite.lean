import Lean
set_option maxRecDepth 8192
set_option maxHeartbeats 30000000
namespace BB6.Agent9Q33

def checkGraph (L : Nat) (nodes : List (Nat × Nat)) : Bool :=
  nodes.all fun p =>
    (List.range 10).all fun t =>
      decide (p.2 % 2^t ≠ 0 ∨
        (L+p.1+t+p.2/2^t)%2 ≠ 1 ∨
        (p.1+t+1,(L+p.1+t+p.2/2^t)/2) ∈ nodes)

theorem checkGraph_sound (L : Nat) (nodes : List (Nat × Nat))
    (hc : checkGraph L nodes = true)
    (m z t v zp : Nat) (hm : (m,z) ∈ nodes) (ht : t < 10)
    (hdiv : z = 2^t*v) (hn : 2*zp+1 = L+m+t+v) :
    (m+t+1,zp) ∈ nodes := by
  have hh := (List.all_eq_true.mp hc) (m,z) hm
  have hhc := (List.all_eq_true.mp hh) t (List.mem_range.mpr ht)
  have hp : z%2^t ≠ 0 ∨ (L+m+t+z/2^t)%2 ≠ 1 ∨
      (m+t+1,(L+m+t+z/2^t)/2) ∈ nodes := of_decide_eq_true hhc
  have hmod : z%2^t = 0 := Nat.mod_eq_zero_of_dvd ⟨v,hdiv⟩
  have hquot : z/2^t = v := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left v (Nat.pow_pos (by decide))
  have hpar : (L+m+t+z/2^t)%2=1 := by
    rw [hquot, ←hn]
    omega
  have hhalf : (L+m+t+z/2^t)/2=zp := by
    rw [hquot, ←hn]
    omega
  rcases hp with hx | hx | hx
  · exact False.elim (hx hmod)
  · exact False.elim (hx hpar)
  · simpa [hhalf] using hx

def q33L0Nodes : List (Nat × Nat) := [
  (0,400),
  (2,368),
  (4,294),
  (4,361),
  (5,282),
  (5,450),
  (6,293),
  (6,411),
  (6,495),
  (7,282),
  (7,341),
  (7,383),
  (7,417),
  (7,476),
  (7,518),
  (8,412),
  (8,509),
  (8,530),
  (9,342),
  (9,401),
  (9,526),
  (10,375),
  (10,443),
  (10,535),
  (11,324),
  (11,358),
  (11,404),
  (11,460),
  (11,494),
  (11,540),
  (12,435),
  (12,452),
  (12,475),
  (12,503),
  (12,520),
  (12,543),
  (13,363),
  (13,397),
  (13,491),
  (13,511),
  (13,525),
  (13,545),
  (14,387),
  (14,404),
  (15,331),
  (15,468),
  (16,376),
  (16,509),
  (17,326),
  (17,530),
  (18,370),
  (18,439),
  (18,541),
  (19,358),
  (19,409),
  (19,496),
  (19,547),
  (20,456),
  (20,525),
  (21,367),
  (21,540),
  (22,340),
  (22,392),
  (22,548),
  (24,364),
  (24,377),
  (24,416),
  (25,322),
  (25,348),
  (25,468),
  (26,371),
  (26,384),
  (26,441),
  (26,454),
  (26,514),
  (27,326),
  (27,361),
  (27,466),
  (27,501),
  (28,307),
  (28,377),
  (28,444),
  (28,514),
  (29,363),
  (29,398),
  (29,435),
  (29,470),
  (30,306),
  (30,393),
  (30,481),
  (30,517),
  (31,338),
  (31,382),
  (31,400),
  (31,479),
  (31,523),
  (31,541),
  (32,289),
  (32,452),
  (32,474),
  (32,483),
  (33,368),
  (33,379),
  (33,428),
  (33,525),
  (34,334),
  (34,397),
  (34,468),
  (34,498),
  (35,341),
  (35,483),
  (36,331),
  (36,402),
  (37,344),
  (37,451),
  (38,458),
  (40,330),
  (41,309)]

theorem q33L0_root : (0, 400) ∈ q33L0Nodes := by decide

theorem q33L0_check : checkGraph 536 q33L0Nodes = true := by decide

theorem q33L0_bounds :
  q33L0Nodes.all (fun p => decide (p.1 ≤ 41 ∧ ¬1024 ∣ p.2)) = true := by decide

theorem q33L0_closed (m z t v zp : Nat)
    (hm : (m,z) ∈ q33L0Nodes) (hdiv : z = 2^t*v)
    (hn : 2*zp+1 = 536+m+t+v) :
    (m+t+1,zp) ∈ q33L0Nodes := by
  have hb := (List.all_eq_true.mp q33L0_bounds) (m,z) hm
  have hmod : ¬1024 ∣ z := (of_decide_eq_true hb).2
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024 ∣ 2^t := by
      have hd : (2:Nat)^10 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    exact False.elim (hmod (Nat.dvd_trans hp ⟨v,hdiv⟩))
  exact checkGraph_sound 536 q33L0Nodes q33L0_check m z t v zp hm ht hdiv hn

theorem q33L0_small (m z : Nat) (hm : (m,z) ∈ q33L0Nodes) : m≤41 := by
  have hb := (List.all_eq_true.mp q33L0_bounds) (m,z) hm
  exact (of_decide_eq_true hb).1

theorem q33L0_no1024 (m z : Nat) (hm : (m,z) ∈ q33L0Nodes) : ¬1024 ∣ z := by
  have hb := (List.all_eq_true.mp q33L0_bounds) (m,z) hm
  exact (of_decide_eq_true hb).2

#print axioms q33L0_closed

def q33L1Nodes : List (Nat × Nat) := [
  (0,334),
  (1,435),
  (2,352),
  (2,486),
  (3,445),
  (3,512),
  (4,391),
  (4,492),
  (5,314),
  (5,398),
  (5,516),
  (7,282),
  (7,303),
  (7,400),
  (8,277),
  (8,336),
  (8,423),
  (9,280),
  (9,372),
  (9,440),
  (11,275),
  (11,298),
  (11,315),
  (11,343),
  (11,366),
  (11,383),
  (12,286),
  (12,320),
  (12,411),
  (12,431),
  (12,445),
  (12,465),
  (13,417),
  (13,434),
  (14,346),
  (14,483),
  (15,315),
  (15,448),
  (16,362),
  (16,433),
  (17,286),
  (17,388),
  (17,457),
  (18,367),
  (18,505),
  (19,305),
  (19,374),
  (20,326),
  (20,430),
  (21,285),
  (21,441),
  (21,493),
  (22,282),
  (22,360),
  (22,386),
  (22,421),
  (22,499),
  (22,525),
  (23,420),
  (23,459),
  (23,472),
  (24,350),
  (24,376),
  (24,509),
  (25,325),
  (25,385),
  (25,398),
  (25,455),
  (25,468),
  (26,303),
  (26,333),
  (26,368),
  (26,443),
  (26,473),
  (26,508),
  (27,328),
  (27,398),
  (27,465),
  (27,535),
  (28,305),
  (28,340),
  (28,514),
  (28,549),
  (29,328),
  (29,364),
  (29,452),
  (29,539),
  (30,411),
  (30,552),
  (31,365),
  (31,374),
  (31,396),
  (31,559),
  (32,329),
  (32,340),
  (32,466),
  (32,563),
  (33,353),
  (33,383),
  (33,454),
  (33,517),
  (34,319),
  (34,334),
  (34,401),
  (34,461),
  (34,476),
  (34,543),
  (35,452),
  (35,523),
  (36,369),
  (36,547),
  (37,399),
  (38,343),
  (38,486),
  (39,530),
  (40,409)]

theorem q33L1_root : (0, 334) ∈ q33L1Nodes := by decide

theorem q33L1_check : checkGraph 537 q33L1Nodes = true := by decide

theorem q33L1_bounds :
  q33L1Nodes.all (fun p => decide (p.1 ≤ 41 ∧ ¬1024 ∣ p.2)) = true := by decide

theorem q33L1_closed (m z t v zp : Nat)
    (hm : (m,z) ∈ q33L1Nodes) (hdiv : z = 2^t*v)
    (hn : 2*zp+1 = 537+m+t+v) :
    (m+t+1,zp) ∈ q33L1Nodes := by
  have hb := (List.all_eq_true.mp q33L1_bounds) (m,z) hm
  have hmod : ¬1024 ∣ z := (of_decide_eq_true hb).2
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024 ∣ 2^t := by
      have hd : (2:Nat)^10 ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
      simpa using hd
    exact False.elim (hmod (Nat.dvd_trans hp ⟨v,hdiv⟩))
  exact checkGraph_sound 537 q33L1Nodes q33L1_check m z t v zp hm ht hdiv hn

theorem q33L1_small (m z : Nat) (hm : (m,z) ∈ q33L1Nodes) : m≤41 := by
  have hb := (List.all_eq_true.mp q33L1_bounds) (m,z) hm
  exact (of_decide_eq_true hb).1

theorem q33L1_no1024 (m z : Nat) (hm : (m,z) ∈ q33L1Nodes) : ¬1024 ∣ z := by
  have hb := (List.all_eq_true.mp q33L1_bounds) (m,z) hm
  exact (of_decide_eq_true hb).2

#print axioms q33L1_closed

end BB6.Agent9Q33
