import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent7LF11188
open BB6Coverage Agent31Pump
-- 1RB1LF_1RC0LB_0RD1RF_1LD1RE_---0RA_1LB0RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

macro "bits" s:str : term => do
  let ts ← s.getString.toList.mapM fun c =>
    if c == '1' then `(true) else `(false)
  let ts := ts.toArray
  `([$ts,*])
def H : List Bool := bits "01111111100"
def P : List Bool := bits "11110000"
def M : List Bool := bits "1111001100000011110001111111110000000000000000"
def W : List Bool := bits "11111100"
def T : List Bool := bits "1111110011111100111111000000111100000000111111"
def phase (n : Nat) (R : List Bool) : Z0 := ⟨1, [], H ++ rep P n ++ M ++ R⟩

theorem rep_add (X : List Bool) (n m : Nat) : rep X (n+m) = rep X n ++ rep X m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [show n+1+m=n+m+1 by omega,rep,ih,List.append_assoc]

theorem rotate (U V : List Bool) (n : Nat) : U ++ rep (V++U) n = rep (U++V) n ++ U := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,← ih]

private theorem step1 (n : Nat) (R : List Bool) : run0 table (30) ⟨1,[],((bits "01111111100") ++ (rep (bits "11110000") n) ++ (bits "1111001100000011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "1011111")),((bits "11100") ++ (rep (bits "11110000") n) ++ (bits "1111001100000011110001111111110000000000000000") ++ R)⟩ := by rfl

private theorem step2 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨3,((bits "1011111")),((bits "11100") ++ (rep (bits "11110000") n) ++ (bits "1111001100000011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111001111001100000011110001111111110000000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 3 (bits "10") (bits "11100") (bits "11110000") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "1111001100000011110001111111110000000000000000") ++ R)

private theorem step3 (n : Nat) (R : List Bool) : run0 table (93) ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111001111001100000011110001111111110000000000000000") ++ R)⟩ = some ⟨1,((bits "11111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "001111110011110001111111110000000000000000") ++ R)⟩ := by rfl

private theorem step4 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "11111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "001111110011110001111111110000000000000000") ++ R)⟩ = some ⟨1,((bits "1111110101111111")),((rep (bits "11110000") n) ++ (bits "001111110011110001111111110000000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "11111101011") [] (bits "11101011") (bits "11110000") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "001111110011110001111111110000000000000000") ++ R)

private theorem step5 (n : Nat) (R : List Bool) : run0 table (115) ⟨1,((bits "1111110101111111")),((rep (bits "11110000") n) ++ (bits "001111110011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "1011111")),((bits "1110011110000") ++ (rep (bits "11110000") n) ++ (bits "001111110011110001111111110000000000000000") ++ R)⟩ := by rfl

private theorem step6 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨3,((bits "1011111")),((bits "1110011110000") ++ (rep (bits "11110000") n) ++ (bits "001111110011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1110011110000001111110011110001111111110000000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 3 (bits "10") (bits "1110011110000") (bits "11110000") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "001111110011110001111111110000000000000000") ++ R)

private theorem step7 (n : Nat) (R : List Bool) : run0 table (57) ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1110011110000001111110011110001111111110000000000000000") ++ R)⟩ = some ⟨1,((bits "110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111111110011110001111111110000000000000000") ++ R)⟩ := by rfl

private theorem step8 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111111110011110001111111110000000000000000") ++ R)⟩ = some ⟨1,((bits "11010111110101111111")),((rep (bits "00001111") n) ++ (bits "111111110011110001111111110000000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "110101111101011") [] (bits "11101011") (bits "00001111") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "111111110011110001111111110000000000000000") ++ R)

private theorem step9 (n : Nat) (R : List Bool) : run0 table (135) ⟨1,((bits "11010111110101111111")),((rep (bits "00001111") n) ++ (bits "111111110011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "1011111")),((bits "11100111100001111") ++ (rep (bits "00001111") n) ++ (bits "111111110011110001111111110000000000000000") ++ R)⟩ := by rfl

private theorem step10 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨3,((bits "1011111")),((bits "11100111100001111") ++ (rep (bits "00001111") n) ++ (bits "111111110011110001111111110000000000000000") ++ R)⟩ = some ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "11100111100001111111111110011110001111111110000000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 3 (bits "10") (bits "11100111100001111") (bits "00001111") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "111111110011110001111111110000000000000000") ++ R)

private theorem step11 (n : Nat) (R : List Bool) : run0 table (599) ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "11100111100001111111111110011110001111111110000000000000000") ++ R)⟩ = some ⟨1,((bits "1111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000001111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step12 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "1111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000001111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "111111010111110101111111")),((rep (bits "11110000") n) ++ (bits "000001111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "1111110101111101011") [] (bits "11101011") (bits "11110000") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "000001111001111111111100111111000000000000") ++ R)

private theorem step13 (n : Nat) (R : List Bool) : run0 table (139) ⟨1,((bits "111111010111110101111111")),((rep (bits "11110000") n) ++ (bits "000001111001111111111100111111000000000000") ++ R)⟩ = some ⟨3,((bits "1011111")),((bits "111001111000011110000") ++ (rep (bits "11110000") n) ++ (bits "000001111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step14 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨3,((bits "1011111")),((bits "111001111000011110000") ++ (rep (bits "11110000") n) ++ (bits "000001111001111111111100111111000000000000") ++ R)⟩ = some ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111001111000011110000000001111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 3 (bits "10") (bits "111001111000011110000") (bits "11110000") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "000001111001111111111100111111000000000000") ++ R)

private theorem step15 (n : Nat) (R : List Bool) : run0 table (89) ⟨3,((bits "10") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "111001111000011110000000001111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "11010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "110001111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step16 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "11010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "110001111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "1101011111010111110101111111")),((rep (bits "00001111") n) ++ (bits "110001111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "11010111110101111101011") [] (bits "11101011") (bits "00001111") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "110001111001111111111100111111000000000000") ++ R)

private theorem step17 (n : Nat) (R : List Bool) : run0 table (160) ⟨1,((bits "1101011111010111110101111111")),((rep (bits "00001111") n) ++ (bits "110001111001111111111100111111000000000000") ++ R)⟩ = some ⟨4,((bits "11011111")),((bits "110011110000111100001111") ++ (rep (bits "00001111") n) ++ (bits "110001111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step18 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨4,((bits "11011111")),((bits "110011110000111100001111") ++ (rep (bits "00001111") n) ++ (bits "110001111001111111111100111111000000000000") ++ R)⟩ = some ⟨4,((bits "110") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "110011110000111100001111110001111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 4 (bits "110") (bits "110011110000111100001111") (bits "00001111") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "110001111001111111111100111111000000000000") ++ R)

private theorem step19 (n : Nat) (R : List Bool) : run0 table (173) ⟨4,((bits "110") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "110011110000111100001111110001111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "001111111111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step20 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "001111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "001111111111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "001111111111001111111111100111111000000000000") ++ R)

private theorem step21 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "001111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "001111111111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step22 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "001111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110001111111111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "001111111111001111111111100111111000000000000") ++ R)

private theorem step23 (n : Nat) (R : List Bool) : run0 table (134) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110001111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step24 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111111111111001111111111100111111000000000000") ++ R)

private theorem step25 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ := by rfl

private theorem step26 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111111111111001111111111100111111000000000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111111111111001111111111100111111000000000000") ++ R)

private theorem step27 (n : Nat) (R : List Bool) : run0 table (812) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111111111111001111111111100111111000000000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step28 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110011000000111100011111110000111111111111000000") ++ R)

private theorem step29 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step30 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110011000000111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110011000000111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110011000000111100011111110000111111111111000000") ++ R)

private theorem step31 (n : Nat) (R : List Bool) : run0 table (214) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110011000000111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step32 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "000111100000011111100111100011111110000111111111111000000") ++ R)

private theorem step33 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step34 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "000111100000011111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110000111100000011111100111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "000111100000011111100111100011111110000111111111111000000") ++ R)

private theorem step35 (n : Nat) (R : List Bool) : run0 table (198) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110000111100000011111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step36 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)

private theorem step37 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ := by rfl

private theorem step38 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111000011111111111100111100011111110000111111111111000000") ++ R)

private theorem step39 (n : Nat) (R : List Bool) : run0 table (728) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111000011111111111100111100011111110000111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step40 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)

private theorem step41 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step42 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110000111100000000011110011111111111111111111111111111000000") ++ R)

private theorem step43 (n : Nat) (R : List Bool) : run0 table (254) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110000111100000000011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step44 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)

private theorem step45 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step46 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "000111100001111000011111100011110011111111111111111111111111111000000") ++ R)

private theorem step47 (n : Nat) (R : List Bool) : run0 table (340) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "100111100001111000011110000111100001111000011111100011110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step48 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)

private theorem step49 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step50 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "0001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)

private theorem step51 (n : Nat) (R : List Bool) : run0 table (302) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "1001111000011110000111100001111000011110000111100011111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step52 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)

private theorem step53 (n : Nat) (R : List Bool) : run0 table (162) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ := by rfl

private theorem step54 (n : Nat) (R : List Bool) : run0 table (32*n) ⟨0,((bits "101011111")),((bits "100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepR table 0 (bits "1010") (bits "100111100001111000011110") (bits "00011110") (bits "11101011") 32 (by intro L R; rfl) n ((bits "11111")) ((bits "00011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)

private theorem step55 (n : Nat) (R : List Bool) : run0 table (982) ⟨0,((bits "1010") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "10011110000111100001111000011110000111100001111000011111111111110011111111111111111111111111111000000") ++ R)⟩ = some ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)⟩ := by rfl

private theorem step56 (n : Nat) (R : List Bool) : run0 table (24*n) ⟨1,((bits "111010111110101111101011") ++ (rep (bits "11101011") n) ++ (bits "11111")),((bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)⟩ = some ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using
      sweepL table 1 (bits "111010111110101111101011") [] (bits "11101011") (bits "00011110") 24 (by intro L R; rfl) n ((bits "11111")) ((bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)

private theorem step57 (n : Nat) (R : List Bool) : run0 table (130) ⟨1,((bits "11101011111010111110101111111")),((rep (bits "00011110") n) ++ (bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)⟩ = some ⟨1,[],((bits "01111111100111100001111000011110") ++ (rep (bits "00011110") n) ++ (bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100") ++ R)⟩ := by rfl

def U : List Bool := bits "11110"
def V : List Bool := bits "000"

theorem rotBlock (n : Nat) : U ++ rep (V++U) n ++ V = rep P (n+1) := by
  calc
    _ = (U ++ rep (V++U) n) ++ V := by rw [List.append_assoc]
    _ = (rep P n ++ U) ++ V := by rw [rotate]; rfl
    _ = rep P n ++ P := by rw [List.append_assoc]; rfl
    _ = rep P (n+1) := by rw [rep_snoc]; rfl

theorem endWord (n : Nat) (R : List Bool) :
    bits "01111111100111100001111000011110" ++ rep (bits "00011110") n ++
      bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100" ++ R =
      H ++ rep P (n+6) ++ M ++ W ++ R := by
  calc
    _ = H ++ rep P 2 ++ (U ++ rep (V++U) n ++ V) ++ rep P 3 ++ M ++ W ++ R := by
      simp only [List.append_assoc]
      rfl
    _ = H ++ rep P 2 ++ rep P (n+1) ++ rep P 3 ++ M ++ W ++ R := by rw [rotBlock]
    _ = H ++ rep P (2+(n+1)+3) ++ M ++ W ++ R := by simp only [rep_add,List.append_assoc]
    _ = _ := by rw [show 2+(n+1)+3=n+6 by omega]

theorem return1188 (n : Nat) (R : List Bool) :
    run0 table (7142+784*n) (phase n R) = some (phase (n+6) (W++R)) := by
  have h1 := step1 n R
  have j1 := h1
  have h2 := step2 n R
  have j2 := join0 j1 h2
  have h3 := step3 n R
  have j3 := join0 j2 h3
  have h4 := step4 n R
  have j4 := join0 j3 h4
  have h5 := step5 n R
  have j5 := join0 j4 h5
  have h6 := step6 n R
  have j6 := join0 j5 h6
  have h7 := step7 n R
  have j7 := join0 j6 h7
  have h8 := step8 n R
  have j8 := join0 j7 h8
  have h9 := step9 n R
  have j9 := join0 j8 h9
  have h10 := step10 n R
  have j10 := join0 j9 h10
  have h11 := step11 n R
  have j11 := join0 j10 h11
  have h12 := step12 n R
  have j12 := join0 j11 h12
  have h13 := step13 n R
  have j13 := join0 j12 h13
  have h14 := step14 n R
  have j14 := join0 j13 h14
  have h15 := step15 n R
  have j15 := join0 j14 h15
  have h16 := step16 n R
  have j16 := join0 j15 h16
  have h17 := step17 n R
  have j17 := join0 j16 h17
  have h18 := step18 n R
  have j18 := join0 j17 h18
  have h19 := step19 n R
  have j19 := join0 j18 h19
  have h20 := step20 n R
  have j20 := join0 j19 h20
  have h21 := step21 n R
  have j21 := join0 j20 h21
  have h22 := step22 n R
  have j22 := join0 j21 h22
  have h23 := step23 n R
  have j23 := join0 j22 h23
  have h24 := step24 n R
  have j24 := join0 j23 h24
  have h25 := step25 n R
  have j25 := join0 j24 h25
  have h26 := step26 n R
  have j26 := join0 j25 h26
  have h27 := step27 n R
  have j27 := join0 j26 h27
  have h28 := step28 n R
  have j28 := join0 j27 h28
  have h29 := step29 n R
  have j29 := join0 j28 h29
  have h30 := step30 n R
  have j30 := join0 j29 h30
  have h31 := step31 n R
  have j31 := join0 j30 h31
  have h32 := step32 n R
  have j32 := join0 j31 h32
  have h33 := step33 n R
  have j33 := join0 j32 h33
  have h34 := step34 n R
  have j34 := join0 j33 h34
  have h35 := step35 n R
  have j35 := join0 j34 h35
  have h36 := step36 n R
  have j36 := join0 j35 h36
  have h37 := step37 n R
  have j37 := join0 j36 h37
  have h38 := step38 n R
  have j38 := join0 j37 h38
  have h39 := step39 n R
  have j39 := join0 j38 h39
  have h40 := step40 n R
  have j40 := join0 j39 h40
  have h41 := step41 n R
  have j41 := join0 j40 h41
  have h42 := step42 n R
  have j42 := join0 j41 h42
  have h43 := step43 n R
  have j43 := join0 j42 h43
  have h44 := step44 n R
  have j44 := join0 j43 h44
  have h45 := step45 n R
  have j45 := join0 j44 h45
  have h46 := step46 n R
  have j46 := join0 j45 h46
  have h47 := step47 n R
  have j47 := join0 j46 h47
  have h48 := step48 n R
  have j48 := join0 j47 h48
  have h49 := step49 n R
  have j49 := join0 j48 h49
  have h50 := step50 n R
  have j50 := join0 j49 h50
  have h51 := step51 n R
  have j51 := join0 j50 h51
  have h52 := step52 n R
  have j52 := join0 j51 h52
  have h53 := step53 n R
  have j53 := join0 j52 h53
  have h54 := step54 n R
  have j54 := join0 j53 h54
  have h55 := step55 n R
  have j55 := join0 j54 h55
  have h56 := step56 n R
  have j56 := join0 j55 h56
  have h57 := step57 n R
  have j57 := join0 j56 h57
  rw [show (30)+(32*n)+(93)+(24*n)+(115)+(32*n)+(57)+(24*n)+(135)+(32*n)+(599)+(24*n)+(139)+(32*n)+(89)+(24*n)+(160)+(32*n)+(173)+(24*n)+(162)+(32*n)+(134)+(24*n)+(162)+(32*n)+(812)+(24*n)+(162)+(32*n)+(214)+(24*n)+(162)+(32*n)+(198)+(24*n)+(162)+(32*n)+(728)+(24*n)+(162)+(32*n)+(254)+(24*n)+(162)+(32*n)+(340)+(24*n)+(162)+(32*n)+(302)+(24*n)+(162)+(32*n)+(982)+(24*n)+(130) = 7142+784*n by omega] at j57
  have endEq : (⟨1,[],bits "01111111100111100001111000011110" ++ rep (bits "00011110") n ++ bits "000111100001111000011110000111100110000001111000111111111000000000000000011111100" ++ R⟩ : Z0) = phase (n+6) (W++R) := by
    unfold phase
    simpa only [List.append_assoc] using congrArg (fun r => (⟨1,[],r⟩ : Z0)) (endWord n R)
  rw [endEq] at j57
  exact j57

def family (k : Nat) : Z0 := phase (31+6*k) (rep W k ++ T)
def cost (k : Nat) : Nat := 7142+784*(31+6*k)
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have h := return1188 (31+6*k) (rep W k++T)
  rw [show 31+6*k+6=31+6*(k+1) by omega] at h
  simpa only [family,cost,rep,List.append_assoc] using h
#print axioms return1188
#print axioms growth

private theorem entry1 : run0 table 4000 ⟨0,[],[]⟩ = some ⟨1,(bits "011110101111101011111010111110101111111"),(bits "0110011111111111111101111110000111111")⟩ := by rfl
private theorem entry2 : run0 table 4000 ⟨1,(bits "011110101111101011111010111110101111111"),(bits "0110011111111111111101111110000111111")⟩ = some ⟨2,(bits "111010111110101111111"),(bits "11100001111000011110000111100001111000011110001111111111001111111111111111111111100111111")⟩ := by rfl
private theorem entry3 : run0 table 4000 ⟨2,(bits "111010111110101111111"),(bits "11100001111000011110000111100001111000011110001111111111001111111111111111111111100111111")⟩ = some ⟨1,[],(bits "011111111001111000011110000111100001111000011110000111100001111000011110000111100000000011110011111111111001111110000001111000111111111")⟩ := by rfl
private theorem entry4 : run0 table 4000 ⟨1,[],(bits "011111111001111000011110000111100001111000011110000111100001111000011110000111100000000011110011111111111001111110000001111000111111111")⟩ = some ⟨2,(bits "0111111010111110101111101011111010111110101111111"),(bits "0110000111100001111000011110000111100001111000000111111001111000111111100001111111111111111000111111111")⟩ := by rfl
private theorem entry5 : run0 table 4000 ⟨2,(bits "0111111010111110101111101011111010111110101111111"),(bits "0110000111100001111000011110000111100001111000000111111001111000111111100001111111111111111000111111111")⟩ = some ⟨3,(bits "10111110101111111"),(bits "10011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000111111111100111111111111111111111111111111111000111111111")⟩ := by rfl
private theorem entry6 : run0 table 4000 ⟨3,(bits "10111110101111111"),(bits "10011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000111111111100111111111111111111111111111111111000111111111")⟩ = some ⟨1,(bits "101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "01100001111000011110000111100001111000011111111111100111100011111111100000000000000000000111100000000111111")⟩ := by rfl
private theorem entry7 : run0 table 4000 ⟨1,(bits "101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "01100001111000011110000111100001111000011111111111100111100011111111100000000000000000000111100000000111111")⟩ = some ⟨5,(bits "1011101011111010111110101111101011111010111110101111111"),(bits "10000111100001111000011110000111100001111000011110000111100001111000011110000111100011111111110011111111111001111110000000000000000111100000000111111")⟩ := by rfl
private theorem entry8 : run0 table 4000 ⟨5,(bits "1011101011111010111110101111101011111010111110101111111"),(bits "10000111100001111000011110000111100001111000011110000111100001111000011110000111100011111111110011111111111001111110000000000000000111100000000111111")⟩ = some ⟨3,(bits "0010111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "10011110000111100001111000011110000111100001111000000111111001111000111111100001111111111110000000000111100000000111111")⟩ := by rfl
private theorem entry9 : run0 table 4000 ⟨3,(bits "0010111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "10011110000111100001111000011110000111100001111000000111111001111000111111100001111111111110000000000111100000000111111")⟩ = some ⟨5,(bits "101110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "100001111000011110000111111000111100111111111111111111111111111110000000000111100000000111111")⟩ := by rfl
private theorem entry10 : run0 table 4000 ⟨5,(bits "101110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "100001111000011110000111111000111100111111111111111111111111111110000000000111100000000111111")⟩ = some ⟨3,(bits "101111101011111010111110101111101011111010111110101111111"),(bits "100111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111001100000011110001111111110000000000000000111111000000111100000000111111")⟩ := by rfl
private theorem entry11 : run0 table 4000 ⟨3,(bits "101111101011111010111110101111101011111010111110101111111"),(bits "100111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111001100000011110001111111110000000000000000111111000000111100000000111111")⟩ = some ⟨1,(bits "10111110101111111"),(bits "011000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000000001111001111111111100111111000000000000111111000000111100000000111111")⟩ := by rfl
private theorem entry12 : run0 table 4000 ⟨1,(bits "10111110101111111"),(bits "011000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000000001111001111111111100111111000000000000111111000000111100000000111111")⟩ = some ⟨2,(bits "01111110101111101011111010111110101111111"),(bits "011000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111111111111001111111111100111111000000000000111111000000111100000000111111")⟩ := by rfl
private theorem entry13 : run0 table 4000 ⟨2,(bits "01111110101111101011111010111110101111111"),(bits "011000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111111111111001111111111100111111000000000000111111000000111100000000111111")⟩ = some ⟨4,(bits "11011110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "100111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100000011111100111100011111110000111111111111000000111111000000111100000000111111")⟩ := by rfl
private theorem entry14 : run0 table 4000 ⟨4,(bits "11011110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "100111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100000011111100111100011111110000111111111111000000111111000000111100000000111111")⟩ = some ⟨2,(bits "011111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0110000111100001111000011110000111100001111000011111100011110011111111111111111111111111111000000111111000000111100000000111111")⟩ := by rfl
private theorem entry15 : run0 table 4000 ⟨2,(bits "011111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0110000111100001111000011110000111100001111000011111100011110011111111111111111111111111111000000111111000000111100000000111111")⟩ = some ⟨2,(bits "110011101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011111111111110011111111111111111111111111111000000111111000000111100000000111111")⟩ := by rfl
private theorem entry16 : run0 table 4000 ⟨2,(bits "110011101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011111111111110011111111111111111111111111111000000111111000000111100000000111111")⟩ = some ⟨0,(bits "001011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "011110000111100001111000011110000111100001111000011110000111100001111000000111111001111000111111111000000000000000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry17 : run0 table 4000 ⟨0,(bits "001011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "011110000111100001111000011110000111100001111000011110000111100001111000000111111001111000111111111000000000000000011111100111111000000111100000000111111")⟩ = some ⟨3,(bits "0010111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "1001111000000000111100111111111110011111100000000000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry18 : run0 table 4000 ⟨3,(bits "0010111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "1001111000000000111100111111111110011111100000000000011111100111111000000111100000000111111")⟩ = some ⟨4,(bits "11101111101011111010111110101111101011111010111110101111111"),(bits "10000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111111111111100111111111110011111100000000000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry19 : run0 table 4000 ⟨4,(bits "11101111101011111010111110101111101011111010111110101111111"),(bits "10000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111111111111100111111111110011111100000000000011111100111111000000111100000000111111")⟩ = some ⟨1,(bits "10101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000001111110011110001111111000011111111111100000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry20 : run0 table 4000 ⟨1,(bits "10101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "0000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000001111110011110001111111000011111111111100000011111100111111000000111100000000111111")⟩ = some ⟨1,(bits "11101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000000001111001111111111111111111111111111100000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry21 : run0 table 4000 ⟨1,(bits "11101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000000001111001111111111111111111111111111100000011111100111111000000111100000000111111")⟩ = some ⟨4,(bits "111111101011111010111110101111111"),(bits "1110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110001111111111001111111111111111111111111111100000011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry22 : run0 table 4000 ⟨4,(bits "111111101011111010111110101111111"),(bits "1110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110001111111111001111111111111111111111111111100000011111100111111000000111100000000111111")⟩ = some ⟨4,(bits "1111111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "11100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110011000000111100011111111100000000000000001111110011111100111111000000111100000000111111")⟩ := by rfl
private theorem entry23 : run0 table 544 ⟨4,(bits "1111111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111101011111010111110101111111"),(bits "11100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110011000000111100011111111100000000000000001111110011111100111111000000111100000000111111")⟩ = some ⟨1,[],(bits "011111111001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110011000000111100011111111100000000000000001111110011111100111111000000111100000000111111")⟩ := by rfl
theorem entry : run0 table 88544 ⟨0,[],[]⟩ = some (phase 31 T) := by
  have j1 := entry1
  have j2 := join0 j1 entry2
  have j3 := join0 j2 entry3
  have j4 := join0 j3 entry4
  have j5 := join0 j4 entry5
  have j6 := join0 j5 entry6
  have j7 := join0 j6 entry7
  have j8 := join0 j7 entry8
  have j9 := join0 j8 entry9
  have j10 := join0 j9 entry10
  have j11 := join0 j10 entry11
  have j12 := join0 j11 entry12
  have j13 := join0 j12 entry13
  have j14 := join0 j13 entry14
  have j15 := join0 j14 entry15
  have j16 := join0 j15 entry16
  have j17 := join0 j16 entry17
  have j18 := join0 j17 entry18
  have j19 := join0 j18 entry19
  have j20 := join0 j19 entry20
  have j21 := join0 j20 entry21
  have j22 := join0 j21 entry22
  have j23 := join0 j22 entry23
  exact j23
#print axioms entry

/-- Every completion of the single undefined E0 transition has an infinite blank orbit. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have hentry : run0 table 88544 ⟨0,[],[]⟩ = some (family 0) := by
    simpa only [family,rep,Nat.mul_zero,Nat.add_zero,List.nil_append] using entry
  exact never_of_growth table family 88544 cost hentry (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6Coverage.Agent7LF11188
