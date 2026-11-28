import Leaf2265TracePart00
import Leaf2265TracePart01
import Leaf2265TracePart02
import Leaf2265TracePart03
import Leaf2265TracePart04
import Leaf2265TracePart05
import Leaf2265TracePart06
import Leaf2265TracePart07
import Leaf2265TracePart08
import Leaf2265TracePart09
import Leaf2265TracePart10

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
Exact symbolic source trace from the genuine blank-entry section S(3,blank).
Every segment uses a parameter-uniform, source-derived counted transition
theorem. The untrusted arithmetic generator selects instances only; the
Lean kernel verifies every intermediate state and count. Chunking avoids
a single enormous elaboration term.

IMPORTANT: No assertion of accepted Lean compilation is made by this file's
presence; check the pinned full-closure CI and #print axioms before promotion.
-/

theorem traceSections : Runs 808309055302710301732399105636921133919495108874980019743107699471600464749233442847378894817095810992429166948706064271645074660649753624345057674686030606018039074854823170989150187051918441908053811822579105479622289846530543 (S 3 blank) (S 752207643348495370241292769519379283747494948193658040502867944510301233975370603709175630633053833395134977514029 (pre [false,false,true,true,true,false,true,true,true] blank)) := by
  have h := (chain traceChunk0 (chain traceChunk1 (chain traceChunk2 (chain traceChunk3 (chain traceChunk4 (chain traceChunk5 (chain traceChunk6 (chain traceChunk7 (chain traceChunk8 (chain traceChunk9 (chain traceChunk10 (chain traceChunk11 (chain traceChunk12 (chain traceChunk13 (chain traceChunk14 (chain traceChunk15 (chain traceChunk16 (chain traceChunk17 (chain traceChunk18 (chain traceChunk19 (chain traceChunk20 (chain traceChunk21 (chain traceChunk22 (chain traceChunk23 (chain traceChunk24 (chain traceChunk25 (chain traceChunk26 (chain traceChunk27 (chain traceChunk28 (chain traceChunk29 (chain traceChunk30 (chain traceChunk31 (chain traceChunk32 (chain traceChunk33 (chain traceChunk34 (chain traceChunk35 (chain traceChunk36 (chain traceChunk37 (chain traceChunk38 (chain traceChunk39 (chain traceChunk40 (chain traceChunk41 (chain traceChunk42 traceChunk43)))))))))))))))))))))))))))))))))))))))))))
  simpa only [Nat.reduceAdd, pre] using h

def terminalCfg : Cfg := E (rep Q 752207643348495370241292769519379283747494948193658040502867944510301233975370603709175630633053833395134977514029 blank)
  (pre [false,false,false,false]
    (rep G 0 (pre [true,true,true] (pre [true,true,true] blank))))

theorem terminalRead : terminalCfg.q = 4 ∧ terminalCfg.r 0 = false := by
  constructor <;> rfl

theorem terminalRun : Runs 808309055302710301732399105636921133919495108874980019743107699471600464749233442847378894817095810992429166948707568686931771651390236209884096433253525595914426390935828906878170789519869183115472163083845213146412559801558627 blankCfg terminalCfg := by
  have hTerm : Runs 1504415286696990740482585539038758567494989896387316081005735889020602467950741207418351261266107666790269955028071 (S 752207643348495370241292769519379283747494948193658040502867944510301233975370603709175630633053833395134977514029 (pre [false,false,true,true,true,false,true,true,true] blank)) terminalCfg := by
    simpa [pre, G, O, P, terminalCfg] using
      (terminal3 752207643348495370241292769519379283747494948193658040502867944510301233975370603709175630633053833395134977514029 0 (pre [true,true,true] blank))
  have h := chain seed (chain traceSections hTerm)
  simpa only [Nat.reduceAdd] using h

#print axioms terminalRun
#print axioms terminalRead
end BB6.Agent3Leaf2265
