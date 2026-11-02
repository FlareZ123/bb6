import DParseRLE

namespace BB6.Portfolio

/-- Kernel source equality at the actual literal rooted machine strings. -/
def rleD0 : String := "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
def rleD1 : String := "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA"
def rleD2 : String := "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---"
def rleD3 : String := "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---"

theorem parsed_D0_eq : parseRLE rleD0 = D0 := by
  funext s b
  exact D0_parseRLE s b

theorem parsed_D1_eq : parseRLE rleD1 = D1 := by
  funext s b
  exact D1_parseRLE s b

theorem parsed_D2_eq : parseRLE rleD2 = D2 := by
  funext s b
  exact D2_parseRLE s b

theorem parsed_D3_eq : parseRLE rleD3 = D3 := by
  funext s b
  exact D3_parseRLE s b

/-- End-to-end original root RLE decoding plus the global halting iff. -/
theorem parsed_D3_halts_iff_I5 :
    haltsFrom (parseRLE rleD3) (0 : State) ↔
      HaltsCfg (parseRLE rleD0) (F0Pure 5 0) := by
  rw [parsed_D3_eq, parsed_D0_eq]
  exact D3_root_halts_iff_I5

theorem parsed_D2_halts_iff_I15 :
    haltsFrom (parseRLE rleD2) (0 : State) ↔
      HaltsCfg (parseRLE rleD0) (F0Pure 15 0) := by
  rw [parsed_D2_eq, parsed_D0_eq]
  exact D2_root_halts_iff_I15

theorem parsed_D1_halts_iff_I39 :
    haltsFrom (parseRLE rleD1) (0 : State) ↔
      HaltsCfg (parseRLE rleD0) (F0Pure 39 0) := by
  rw [parsed_D1_eq, parsed_D0_eq]
  exact D1_root_halts_iff_I39

/-- Exact Busy Beaver halting-time offsets from the literal machine code. -/
theorem parsed_D3_haltsAt_iff_I5 (n : Nat) :
    haltsAt (parseRLE rleD3) (0:State) (15+n) ↔
      HaltsAtCfg (parseRLE rleD0) (F0Pure 5 0) n := by
  rw [parsed_D3_eq,parsed_D0_eq]
  exact D3_haltsAt_iff_I5 n

theorem parsed_D2_haltsAt_iff_I15 (n : Nat) :
    haltsAt (parseRLE rleD2) (0:State) (92+n) ↔
      HaltsAtCfg (parseRLE rleD0) (F0Pure 15 0) n := by
  rw [parsed_D2_eq,parsed_D0_eq]
  exact D2_haltsAt_iff_I15 n

theorem parsed_D1_haltsAt_iff_I39 (n : Nat) :
    haltsAt (parseRLE rleD1) (0:State) (403+n) ↔
      HaltsAtCfg (parseRLE rleD0) (F0Pure 39 0) n := by
  rw [parsed_D1_eq,parsed_D0_eq]
  exact D1_haltsAt_iff_I39 n

#print axioms parsed_D1_halts_iff_I39
#print axioms parsed_D2_halts_iff_I15
#print axioms parsed_D3_halts_iff_I5
#print axioms parsed_D1_haltsAt_iff_I39
#print axioms parsed_D2_haltsAt_iff_I15
#print axioms parsed_D3_haltsAt_iff_I5
end BB6.Portfolio
