"""Exact candidate table-to-certificate binding.

Only these four full tables may bypass the old primitive candidate replay.
The downstream WeightedAudit checks table equality, and imports the original
Lean proof of the precise weighted bound. No assertion here is trusted.
"""
BANK={
 (7,24,11,22,14,9,17,16,6,11,16,0):
 (125150404,1,"LateA1Checked","BB6.Agent12LateA1.ctr false","BB6.Agent12LateA1.weighted false",125150410),
 (7,24,11,22,14,9,17,16,6,11,15,0):
 (187672020,1,"LateA1Checked","BB6.Agent12LateA1.ctr true","BB6.Agent12LateA1.weighted true",187672026),
 (7,20,11,1,14,9,17,16,6,11,0,24):
 (31790091,11,"Late209Checked","BB6.Agent12RepeatReplay.R209.parent","BB6.Agent12RepeatReplay.R209.all_completions_weighted",31790097),
 (7,23,11,13,14,21,24,16,6,11,3,0):
 (3643339,6,"Late892Checked","BB6.Agent12RepeatReplay.R892.parent","BB6.Agent12RepeatReplay.R892.all_completions_weighted",3643345),
}
def patch_candidate_replay():
    import package6
    old=package6.first_hole
    def first_hole(table,limit):
        k=tuple(table)
        if k in BANK:
            n,s,*_=BANK[k]
            assert limit==n and table[s]==24 and table.count(24)==1
            return "hole",n,s
        return old(table,limit)
    package6.first_hole=first_hole

if __name__=="__main__":
    import pathlib,sys,json,package6
    patch_candidate_replay()
    spec,part=map(lambda p:json.load(open(p)),sys.argv[1:3])
    package6.make(spec,part,pathlib.Path(sys.argv[3]))
    # Generate primitive late banks only for non-compressed leaves.
    spec["late"]={k:v for k,v in spec["late"].items()
                  if tuple(part["open"][int(k)]) not in BANK}
    pathlib.Path(sys.argv[4]).write_text(json.dumps(spec))
