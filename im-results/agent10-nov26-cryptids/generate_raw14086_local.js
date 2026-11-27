// Generate exact original-source local-path theorems from checked recipes.
const fs=require("fs"),path=require("path");
const {rule}=require("./generate_raw140_variant_transfer.js");
const {execFileSync}=require("child_process");
execFileSync("python3",[path.join(__dirname,"raw14086_local.py")],{stdio:"inherit"});
const recipes=JSON.parse(fs.readFileSync(path.join(__dirname,"raw14086-recipes.json"),"utf8"));
function token([move,[a,b]]){
  if(a===0)return move+(b===1?"":"^"+b);
  if(a!==1)throw Error("nonunit parameter coefficient");
  return move+"^p"+(b===0?"":"+"+b);
}
let out="import Raw140ExtraCore\nnamespace Raw14086Local\nopen BB6BlockFAR Raw140Orbit Raw140Extra\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
out+="def M86 : Table := fill (some ⟨true,true,5⟩) (some ⟨true,true,2⟩)\n";
for(const [name,{start,end,path:steps}] of Object.entries(recipes)){
 const [q,d,L,R]=start,[q1,d1,L1,R1]=end;
 out+=rule(name,86,L,R,q,d,L1,R1,q1,d1,steps.map(token).join(" "))+"\n";
}
out+=Object.keys(recipes).map(k=>"#print axioms "+k).join("\n")+"\nend Raw14086Local\n";
fs.writeFileSync(path.join(__dirname,"Raw14086Local.lean"),out);
