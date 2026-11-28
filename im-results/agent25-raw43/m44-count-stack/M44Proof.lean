import M44Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25M44
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

theorem allChecks : (List.range 378).all (stateCheck cert) = true := by
  rw [show List.range 378 = (List.range' 0 8) ++ (List.range' 8 8) ++ (List.range' 16 8) ++ (List.range' 24 8) ++ (List.range' 32 8) ++ (List.range' 40 8) ++ (List.range' 48 8) ++ (List.range' 56 8) ++ (List.range' 64 8) ++ (List.range' 72 8) ++ (List.range' 80 8) ++ (List.range' 88 8) ++ (List.range' 96 8) ++ (List.range' 104 8) ++ (List.range' 112 8) ++ (List.range' 120 8) ++ (List.range' 128 8) ++ (List.range' 136 8) ++ (List.range' 144 8) ++ (List.range' 152 8) ++ (List.range' 160 8) ++ (List.range' 168 8) ++ (List.range' 176 8) ++ (List.range' 184 8) ++ (List.range' 192 8) ++ (List.range' 200 8) ++ (List.range' 208 8) ++ (List.range' 216 8) ++ (List.range' 224 8) ++ (List.range' 232 8) ++ (List.range' 240 8) ++ (List.range' 248 8) ++ (List.range' 256 8) ++ (List.range' 264 8) ++ (List.range' 272 8) ++ (List.range' 280 8) ++ (List.range' 288 8) ++ (List.range' 296 8) ++ (List.range' 304 8) ++ (List.range' 312 8) ++ (List.range' 320 8) ++ (List.range' 328 8) ++ (List.range' 336 8) ++ (List.range' 344 8) ++ (List.range' 352 8) ++ (List.range' 360 8) ++ (List.range' 368 8) ++ (List.range' 376 2) by decide]
  simp only [List.all_append, check0, check8, check16, check24, check32, check40, check48, check56, check64, check72, check80, check88, check96, check104, check112, check120, check128, check136, check144, check152, check160, check168, check176, check184, check192, check200, check208, check216, check224, check232, check240, check248, check256, check264, check272, check280, check288, check296, check304, check312, check320, check328, check336, check344, check352, check360, check368, check376, Bool.and_true]

theorem cert_valid : Valid cert := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · unfold Safe
    decide
  · intro s hs
    exact List.all_eq_true.mp allChecks s (List.mem_range.mpr hs)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := arbitrary_live cert_valid n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some z :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
      have H := zrun_sound table m hm t s z' hZ
      have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
      rw [hb] at H
      rw [show t=n+(t-n) by omega,run_append] at H
      cases he : run m n blank with
      | none => simp [he] at H
      | some c => rfl

#print axioms cert_valid
#print axioms never
end BB6.Agent25M44
