// Emit exact Lean certificates from discovery data.
function emit(records){
 const bits=s=>"["+[...s].map(x=>x==="1"?"true":"false").join(",")+"]";
 const llist=(s,p)=>"["+s.map(x=>"."+p+x).join(",")+"]";
 let txt=`import Box33PrefixMacro\n\nnamespace BB6.Agent13.Box33D17V22PrefixFamily\nopen C9Pair\nopen BB6.Agent13.Box33PrefixMacro\nopen BB6.Agent13.Box33D14Growth (z word)\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedSimpArgs false\n`;
 for(const [id,c] of Object.entries(records)){
 const con=(name,p,n)=>`inductive ${name} where\n  | ${Array.from({length:n},(_,i)=>p+i).join(" | ")}\n`;
 txt+=`\nnamespace M${id}\n`+con("Mode","m",c.modes.length)+con("L","l",c.B.length)+con("D","d",c.D.length);
 txt+=`def shape : Mode → Shape\n`+c.modes.map((m,i)=>`  | .m${i} => ⟨.${"ABCDEF"[m.q]},${!!m.a},${bits(m.l)},${bits(m.r)}⟩`).join("\n")+"\n";
 txt+=`def leftWord : L → List Bool\n`+c.B.map((b,i)=>`  | .l${i} => ${bits(b)}`).join("\n")+"\n";
 txt+=`def rightWord : D → List Bool\n`+c.D.map((b,i)=>`  | .d${i} => ${bits(b)}`).join("\n")+"\n";
 txt+=`def rule : Mode → Option L → D → Rule Mode L D\n`+c.rules.flatMap((rs,i)=>rs.map((r,j)=>{const a=c.cases[j];return `  | .m${i},${a.ld<0?"none":`some .l${a.ld}`},.d${a.rd} => ⟨${r.t},.m${r.j},${llist(r.ls,"l")},${llist(r.rs,"d")}⟩`})).join("\n")+"\n";
 txt+=`def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d${c.D.findIndex(x=>!x.includes("1"))},rule⟩\n`;
 txt+=`def step (c : C9Pair.Config) : Option C9Pair.Config :=\n  match c.q,c.a with\n`+c.machine.map((v,i)=>{const x=v-1;return `  | .${"ABCDEF"[i>>1]},${!!(i&1)} => ${v===0?"none":`some (${x&1?"right":"left"} .${"ABCDEF"[x>>2]} ${!!(x>>1&1)} c)`}`}).join("\n")+"\n";
 txt+=`theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

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
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M${id}\n`;
 }
 return txt+"end BB6.Agent13.Box33D17V22PrefixFamily\n";
}
const fs=require("fs"),path=require("path");
const d=JSON.parse(fs.readFileSync(path.join(__dirname,"d17v22-prefix-certificates.json"),"utf8"));
process.stdout.write(emit(d));
