import CSourceBridge16

#check CCert.S
#check CCert.Reach
#check CCert.qMap
#check CCert.seen
#check CCert.reachable_seen
#check CCert.published_next_agrees16
#check CCert.published_reset_unreachable16

namespace CCert

theorem source_reachable_embeds16_agent13 {s : S}
    (h : BB6CLine.Reach s) : Reach s := by
  induction h with
  | init => exact Reach.init
  | next s t _ ht ih =>
      exact Reach.step ih (by rw [published_next_agrees16]; exact ht)

end CCert

#print axioms CCert.source_reachable_embeds16_agent13
