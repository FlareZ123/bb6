// Local exact paths for the second bank direction of M42.
const fs=require("fs"),path=require("path");
const {rule,exits}=require("./generate_raw140_variant_transfer.js");
const E=exits(42);
function seed(){
 let q=1,d=1,L=[8],R=[9,...("6446446".split("").map(Number).reverse())],seq=[];
 for(let i=0;i<500;i++){
  if(q===2&&d===1&&L.slice().reverse().join("")==="4555258"&&R.slice().reverse().join("")==="69")return seq.join(" ");
  const S=d?R:L,a=S.pop();
  if(a===8||a===9||a===undefined)throw Error("seed read marker "+[q,d,a,L,R]);
  const e=E[[q,d,a]];if(!e)throw Error("seed undefined");
  seq.push("ABCDEF"[q]+(d?"R":"L")+a);let [r,z,b,k]=e;q=r;d=z;(d?L:R).push(b);
 }
 throw Error("seed limit");
}
let rules=[
 ["rightStart",42,"X","6 4 4 6 4 4 6 Y",1,1,"4 5 5 5 2 5 X","6 Y",2,1,seed()],
 ["rightScanOne","base","4 X","6 4 4 6 Y",2,1,"4 5 5 4 X","6 Y",2,1,"CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER6 BL0"],
 ["rightPumpOne","base","5 5 5 4 X","Y",3,0,"5 X","6 4 4 Y",3,0,"DL5^3 DL4 ER4 BL1 CR4"],
 ["rightFinish","base","5^4 2 5^p+1","Y",3,0,"5^p+12","Y",1,1,
 "DL5^4 DL2 BL5 DL5^p DL0 AR4^p AR2 EL3^p EL2 BL0 CR1^p+2 CR5 BL6^p+2 BL4 BR2^p+3 BR4 ER4 BL1 CR4 DL5^p+5 DL0 AR4^p+5 AR6 EL3^p+5 EL2 BL0 CR1^p+6 CR5 BL6^p+6 BL4 BR2^p+7 BR4 ER4 BL1 CR4 DL5^p+9 DL0 AR4^p+9 AR6 EL3^p+9 EL2 BL0 CR1^p+10 CR5 BL6^p+10 BL4 BR2^p+11"]
];
let out="import Raw140VariantTransfer\nnamespace Raw14042RightLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
out+=rules.map(x=>rule(...x)).join("\n")+"\n"+rules.map(x=>"#print axioms "+x[0]).join("\n")+"\nend Raw14042RightLocal\n";
fs.writeFileSync(path.join(__dirname,"Raw14042RightLocal.lean"),out);
