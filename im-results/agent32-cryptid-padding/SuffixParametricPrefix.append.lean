/- The 107 source-preserving A_step2 moves from the external halting proof,
    with each exact original checkpoint kept explicit. This does NOT prove
    halting for the arbitrary suffix; the final finite tail is a separate gate. -/
set_option maxHeartbeats 1000000 in
theorem reaches_108_cylinder_suffix (k : Nat) (ls : List Symbol) :
    A (3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086) ls ⊢*
    A (3 ^ 1 * (8 ^ 107 * k) + 7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106)
      ([0, 1, 0, 1, 1, 0, 1, 1] ++ ls) := by
  apply stepStar_trans (c₂ := A (3 ^ 98 * (8 ^ 10 * k) + 35925965576050291197954676646168812866911688985763244505) ([0, 1, 0, 1, 0, 1, 0, 1, 1] ++ ls))
  · nth_rw 1 [(by simp : k = 8 ^ 0 * k)]
    A_step2 13
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 27
    finish
  apply stepStar_trans (c₂ := A (3 ^ 88 * (8 ^ 20 * k) + 653274599173389056319717515476765122857837155218448003942322) ([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ ls))
  · A_step2 35
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 78 * (8 ^ 30 * k) + 11879087870908968104360314522392758770461111276045783640742261386) ([0, 1, 1, 1, 0, 1, 0, 1, 1, 1] ++ ls))
  · A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 68 * (8 ^ 40 * k) + 216008289352335720339610602524813115320952275950623503089297980541682) ([0, 1, 0, 1, 1, 0, 1, 1, 1] ++ ls))
  · A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 58 * (8 ^ 50 * k) + 3927875740627220359664132971002588353805172690412603331883223229967369354) ([0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0] ++ ls))
  · A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 48 * (8 ^ 60 * k) + 71424147101329785314496471805836819044114607618056461822634921267834080686730) ([0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1] ++ ls))
  · A_step2 21
    A_step2 5
    A_step2 27
    A_step2 39
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 38 * (8 ^ 70 * k) + 1298770410781319861625359536628288369435308900216028055554241136144906066587587722) ([0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1] ++ ls))
  · A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 28 * (8 ^ 80 * k) + 23616726952692910182205306669292505610517611280824263889413609179834777358573759023858) ([0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1] ++ ls))
  · A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 18 * (8 ^ 90 * k) + 429444486360386240087203819295254784395458238425633310167425409595064063059982219052239602) ([0, 1, 0, 0, 1, 0, 1, 0, 1, 1] ++ ls))
  · A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 31
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  apply stepStar_trans (c₂ := A (3 ^ 8 * (8 ^ 100 * k) + 7808980780222260203826248505306665087325883016528076661998155848237077485933315200811517542561) ([0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] ++ ls))
  · A_step2 17
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 21
    A_step2 21
    finish
  apply stepStar_trans (c₂ := A (3 ^ 1 * (8 ^ 107 * k) + 7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106) ([0, 1, 0, 1, 1, 0, 1, 1] ++ ls) )
  · A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    A_step2 5
    A_step2 21
    A_step2 5
    finish
  finish
