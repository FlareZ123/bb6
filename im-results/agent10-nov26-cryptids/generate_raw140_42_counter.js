// Symbolic local certificates for sibling42's low-bank / right-counter phase.
// All finite paths are replayed on an opaque suffix and checked by Lean.
const fs=require("fs"),path=require("path");
const {rule,exits}=require("./generate_raw140_variant_transfer.js");
const repeated=(x,n)=>Array(n).fill(x).join(" ");
function seed(){
  const E=exits(42),L=[8,...Array(7).fill(3)],R=[];
  let q=0,d=1,cost=0,seq=[];
  for(let j=0;j<2000;j++){
    if(q===4&&d===1&&L.slice().reverse().join("")==="278"&&R.slice().reverse().join("")==="3222222231"){
      if(cost!==635)throw Error("seed cost "+cost);
      return seq.join(" ");
    }
    const S=d?R:L,b=S.at(-1)||0;
    if(b===8)throw Error("seed reads opaque X");
    const e=E[[q,d,b]];
    if(!e)throw Error("seed undefined");
    seq.push("ABCDEF"[q]+(d?"R":"L")+b);
    S.pop();let [r,z,v,k]=e;q=r;d=z;cost+=k;const D=d?L:R;
    if(D.length||v)D.push(v);
  }
  throw Error("seed target not reached");
}
const fwd="ER3 DR2 BL6 BL2 CR2 DR3 EL6";
const prep=[
["31","32","ER3 DR3 EL6 ER3 DR1 EL6 ER1 EL2 BL2 CR1 CR5 BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["32","315","ER3 DR3 EL6 ER3 DR2 BL6 BL2 CR2 DR3 EL6 ER3 DR0 BL6 BL2 CR2 DR1 EL6 ER1 EL2 BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["315","325","ER3 DR3 EL6 ER3 DR1 EL6 ER1 EL2 BL2 CR1 CR5 BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["325","3242","ER3 DR3 EL6 ER3 DR2 BL6 BL2 CR2 DR3 EL6 ER3 DR5 EL6 ER5 ER0 BL1 CR0 DL5 DL2 BL2 CR5 BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["3242","35221","ER3 DR3 EL6 ER3 DR2 BL6 BL2 CR2 DR3 EL6 ER3 DR4 BL6 BL2 CR2 DR5 EL6 ER5 ER2 BL1 CR2 DR0 BL6 BL5 DL2 BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["35221","32231","ER3 DR3 EL6 ER3 DR5 EL6 ER5 ER2 BL1 CR2 DR2 BL6 BL5 DL2 BL2 CR5 BL6 BL2 CR2 DR2 BL6 BL6"]
];
const rules=[
["low542",42,"3^p+1 2","1 1 5 5 4 2",0,1,"3^p+13 2","",0,1,
 "AR1 BR1 DL6 ER0 BL0 CR0 DL4 ER2 BL1 CR2 DR5 EL6 ER5^2 ER4 BL1 CR4 DL5 DL1 AR4 AR6 EL3^2 EL2 BL5 DL3 EL3^p EL2 BL0 CR1^p+1 CR5 BL6^p+1 BL4 BR2^p+3 BR1 DL5^p+4 DL0 AR4^p+4 AR0 DR1 EL7 ER1 EL3^p+5 EL2 BL0 CR1^p+6 CR5 BL6^p+6 BL4 BR2^p+7 BR1 DL5^p+8 DL0 AR4^p+8 AR0 DR5 EL7 ER5 ER2 BL1 CR2 DR0 BL6 BL5 DL3 EL3^p+8 EL2 BL0 CR1^p+9 CR5 BL6^p+9 BL4 BR2^p+12 BR1 DL5^p+13 DL0 AR4^p+13"],
["seedCounter",42,"3^7 X","",0,1,"2 7 X","3 2^7 3 1",4,1,seed()],
["forwardOne","base","2 X","3 2 Y",4,1,"2 6 X","3 Y",4,1,fwd],
["forwardTrip","base","2 X","3 3 2 2 Y",4,1,"2 6 6 2 X","3 Y",4,1,"ER3 DR3 EL6 "+fwd+" "+fwd],
...prep.map(([s,t,p])=>["prep"+s,"base","2 X","3 "+s.split("").join(" "),4,1,"X","2 2 "+t.split("").join(" "),1,0,p]),
["backTrip","base","6 6 2 X","2 2 3 Y",1,0,"X","2 2 3 2 2 3 Y",1,0,"BL6 BL6 BL2 CR2 DR2 BL6 BL6"],
["finishStep","base","7 3 X","2 2 Y",1,0,"2 7 X","3 2 Y",4,1,"BL7 DR2 BL6 BL3 CR2 DR3 EL6"],
["finishZero","base","7 2","2 2 Y",1,0,"2 6","3 2 Y",4,1,"BL7 DR2 BL6 BL2 CR2 DR3 EL6"],
["initTwos","base","","2 2 Y",1,0,"3 3 2","2 Y",0,1,"BL0 CR2 DR2 BL6 BL4 BR2 BR3 DL5^2 DL0 AR4^2"],
["twoPump","base","3^p 2","2 2 2 Y",0,1,"3^p+4 2","2 Y",0,1,
 "AR2 EL3^p EL2 BL0 CR1^p+2 CR2 DR2 BL6^p+3 BL4 BR2^p+3 BR3 DL5^p+4 DL0 AR4^p+4"],
["boundaryOne",42,"3^p 2","2 3 Y",0,1,"4 6^p+2 4","Y",0,1,"AR2 EL3^p EL2 BL0 CR1^p+2 CR3"]
];
let out="import Raw140VariantTransfer\nnamespace Raw14042CounterLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
out+=rules.map(x=>rule(...x)).join("\n")+"\n"+rules.map(x=>"#print axioms "+x[0]).join("\n")+"\nend Raw14042CounterLocal\n";
fs.writeFileSync(path.join(__dirname,"Raw14042CounterLocal.lean"),out);
