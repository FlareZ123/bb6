import QFinal
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent28Affine4096

/-- Additional late-start residue q≡5 modulo4096, with source gateway bridge valid from q=4101. -/

def q4101nodes0 : List (Nat×Nat×Nat×Nat) := [
  (0,49216,49152,7),
  (2,45116,45056,3),
  (4,35889,35840,1),
  (4,44092,44032,3),
  (5,38453,38400,1),
  (5,50758,50688,2),
  (6,33583,33536,1),
  (6,43837,43776,1),
  (6,58193,58112,1),
  (7,33199,33152,1),
  (7,38326,38272,2),
  (7,45504,45440,7),
  (7,49606,49536,2),
  (7,54733,54656,1),
  (7,61911,61824,1),
  (8,51978,51904,2),
  (8,55567,55488,1),
  (8,57618,57536,2),
  (9,42397,42336,1),
  (9,45217,45152,1),
  (9,60599,60512,1),
  (10,38504,38448,4),
  (12,34239,34188,1),
  (12,42443,42380,1),
  (13,49937,49862,1),
  (13,54039,53958,1)
]
theorem q4101check0 : BB6.Agent13AdaptiveParam.check 12 13 (16*4101+8) P4096 q4101nodes0 = true := by decide

def q4101nodes1 : List (Nat×Nat×Nat×Nat) := [
  (0,41014,40960,2),
  (1,53319,53248,1),
  (2,43066,43008,2),
  (2,59472,59392,5),
  (3,54346,54272,2),
  (3,62549,62464,1),
  (4,43580,43520,3),
  (4,64088,64000,4),
  (5,40248,40192,4),
  (5,54604,54528,3),
  (5,64858,64768,2),
  (7,40826,40768,2),
  (7,42877,42816,1),
  (7,46466,46400,2),
  (8,36821,36768,1),
  (8,39641,39584,1),
  (8,54254,54176,2),
  (9,59943,59856,1),
  (10,46380,46312,3),
  (10,62788,62696,3),
  (11,56007,55924,1),
  (11,64211,64116,1),
  (12,60821,60730,1),
  (12,64923,64826,1)
]
theorem q4101check1 : BB6.Agent13AdaptiveParam.check 12 13 (16*4101+9) P4096 q4101nodes1 = true := by decide

theorem q4101_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(4101+P4096*r)+2)-2*(16*(4101+P4096*r)+2)-10) := by
  exact BB6.Agent13AdaptiveParam.critical_unreachable_of_affine_check
    12 13 4101 P4096 (by decide) (by decide)
    q4101nodes0 q4101nodes1 q4101check0 q4101check1
    (root_mem 12 4101 P4096 7 q4101nodes0 (by decide))
    (root_mem 10 4101 P4096 2 q4101nodes1 (by decide)) r

def expandedQ : List Nat := newQ ++ [4101]

theorem expandedQ_unreachable (q r : Nat) (hq : q ∈ expandedQ) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(q+P4096*r)+2)-2*(16*(q+P4096*r)+2)-10) := by
  have hh : q ∈ newQ ∨ q=4101 := by
    simpa only [expandedQ, List.mem_append, List.mem_singleton] using hq
  rcases hh with h | h
  · exact newQ_unreachable q r h
  · subst q
    exact q4101_unreachable r

#print axioms expandedQ_unreachable
end BB6.Agent28Affine4096
