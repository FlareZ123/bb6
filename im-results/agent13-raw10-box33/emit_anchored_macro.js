// Emit exact Lean certificates from discovery data.
function emit(records){
 const bits=s=>"["+[...s].map(x=>x==="1"?"true":"false").join(",")+"]";
 const llist=(s,p)=>"["+s.map(x=>"."+p+x).join(",")+"]";
 let txt=`import Box33ExactMacro\n\nnamespace BB6.Agent13.Box33D17V23Anchored\nopen C9Pair\nopen BB6.Agent13.Box33PrefixMacro BB6.Agent13.Box33ExactMacro\nopen BB6.Agent13.Box33D14Growth (z word)\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\n`;
 for(const [id,c] of Object.entries(records)){
 const con=(name,p,n)=>`inductive ${name} where\n  | ${Array.from({length:n},(_,i)=>p+i).join(" | ")}\n`;
 txt+=`\nnamespace M${id}\n`+con("Mode","m",c.modes.length)+con("L","l",c.B.length)+con("D","d",c.D.length);
 txt+=`def shape : Mode → Shape\n`+c.modes.map((m,i)=>`  | .m${i} => ⟨.${"ABCDEF"[m.q]},${!!m.a},${bits(m.l)},${bits(m.r)}⟩`).join("\n")+"\n";
 txt+=`def leftWord : L → List Bool\n`+c.B.map((b,i)=>`  | .l${i} => ${bits(b)}`).join("\n")+"\n";
 txt+=`def rightWord : D → List Bool\n`+c.D.map((b,i)=>`  | .d${i} => ${bits(b)}`).join("\n")+"\n";
 txt+=`def rule : Mode → Option L → Option D → Rule Mode L D\n`+c.rules.flatMap((rs,i)=>rs.map((r,j)=>{const a=c.cases[j];return `  | .m${i},${a.ld<0?"none":`some .l${a.ld}`},${a.rd<0?"none":`some .d${a.rd}`} => ⟨${r.t},.m${r.j},${llist(r.ls,"l")},${llist(r.rs,"d")}⟩`})).join("\n")+"\n";
 txt+=`def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word ${bits(c.Lbase||"")} z,word ${bits(c.Rbase||"")} z,.m0,rule⟩\n`;
 txt+=`def step (c : C9Pair.Config) : Option C9Pair.Config :=\n  match c.q,c.a with\n`+c.machine.map((v,i)=>{const x=v-1;return `  | .${"ABCDEF"[i>>1]},${!!(i&1)} => ${v===0?"none":`some (${x&1?"right":"left"} .${"ABCDEF"[x>>2]} ${!!(x>>1&1)} c)`}`}).join("\n")+"\n";
 txt+=`theorem positive : ExactPositive spec := by
  intro m a d
  cases a with
  | none =>
    cases d with
    | none => cases m <;> decide
    | some d => cases m <;> cases d <;> decide
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> decide
    | some d => cases m <;> cases a <;> cases d <;> decide

theorem sound : ExactSound spec step := by
  intro m a d l r
  cases a with
  | none =>
    cases d with
    | none => cases m <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases a <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [${c.machine.join(",")}]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  let k : Nat := ${c.initial?.t||0}
  have hi : Box33PrefixMacro.run step k (project BB6Coverage.blank) =
      some (exactPhase spec spec.initial ${llist(c.initial?.ls||[],"l")} ${llist(c.initial?.rs||[],"d")}) := by
    simp [k,project,Box33Source.project,BB6Coverage.blank,Box33Source.q,Box33Source.perm,exactPhase,spec,shape,atShape,blocks,leftWord,rightWord,word,Box33PrefixMacro.run,step,left,right]
  intro h
  have hc := exactNever spec step sound positive (n-k) spec.initial ${llist(c.initial?.ls||[],"l")} ${llist(c.initial?.rs||[],"d")}
  by_cases hn : n≤k
  · rw [←show n+(k-n)=k by omega,Box33PrefixMacro.run_add,h] at hi
    contradiction
  · rw [←show k+(n-k)=n by omega,Box33PrefixMacro.run_add,hi,Option.bind_some] at h
    exact hc h

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M${id}\n`;
 }
 return txt+"end BB6.Agent13.Box33D17V23Anchored\n";
}

module.exports={emit};
