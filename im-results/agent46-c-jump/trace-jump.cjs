"use strict";
const {createHash}=require("node:crypto");
const {jump}=require("./jump-step.cjs");
/** Trace Machine C from its exact first zero-c section.
 * @param {number} start @param {number} end
 * @param {[number,number]} initial @param {bigint} rawSteps */
function trace(start,end,initial,rawSteps){
  let [a,k]=initial;
  const hash=createHash("sha256");
  for(let i=start;i<end;i++){
    let state=[a,k,0];
    const limit=4*k+5;
    let used=0;
    for(let j=0;used<limit;j++){
      const r=jump(state);
      used+=r.steps;
      if(r.state===null){
        console.log("HALT",i,String(rawSteps+BigInt(used)));
        return;
      }
      state=r.state;
      if(state[2]===0)break;
    }
    if(state[2]!==0)throw Error("Section budget exhausted");
    [a,k]=state;
    rawSteps+=BigInt(used);
    if((i+1)%10000===0)hash.update(`${i+1},${a},${k},${rawSteps}\n`);
  }
  console.log(JSON.stringify({start,end,a,k,rawSteps:String(rawSteps),checkpointSHA256:hash.digest("hex")}));
}
if(require.main===module){
  const [start="0",end="10000000",a="5",k="1",raw="1"]=process.argv.slice(2);
  trace(Number(start),Number(end),[Number(a),Number(k)],BigInt(raw));
}
module.exports={trace};
