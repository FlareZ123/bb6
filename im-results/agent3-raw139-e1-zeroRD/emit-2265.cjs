/* Generate a proof by applying all-parameter counted lemmas, not by
   reducing run at a huge numeral. All concrete Nat arithmetic and finite
   suffix normalization are checked by Lean. */
const x=require("./leaf2265.cjs");
const bits=w=>"["+[...w].map(x=>x==="1"?"true":"false").join(",")+"]";
const ray=w=>"(pre "+bits(w)+" blank)";
const S=(k,w)=>"(S "+k+" "+ray(w)+")";
const lines=["import Leaf2265Compress","namespace BB6.Agent3Leaf2265","set_option maxRecDepth 1000000","set_option maxHeartbeats 0"];
function cmd(x){lines.push("  "+x)}
for(let i=0;i<x.sections;i++){
 const {k,w,T}=x.trace[i],v=x.trace[i+1],dt=v.T-T;
 lines.push("theorem hop"+i+" : Runs "+dt+" "+S(k,w)+" "+S(v.k,v.w)+" := by");
 let rawK,rawW,rawIn=w;
 if(w.startsWith("1")){
  cmd("have g := one "+k+" "+ray(w.slice(1)));
  rawK=k+1n;rawW="0"+w.slice(1);
 }else{
  let z=w+"000",m=0;while(z[2+m]==="1")m++;
  let u=z.slice(3+m).replace(/0+$/,""),r=Math.floor(m/4),j=m%4;
  rawIn="00"+"1".repeat(m)+"0"+u;
  if(j===1&&r===0){
   cmd("have g := one0010 "+k+" "+ray(u));rawK=k+4n;rawW=u;
  }else if(j===1){
   cmd("have h := ret1 "+k+" "+r+" "+ray(u));
   let rest="100"+"1100".repeat(r-1)+"111"+u;
   cmd("change Runs "+(4n*k+10n+10n*BigInt(r))+" "+S(k,rawIn)+" (S "+(k+1n)+" (pre P "+ray(rest)+")) at h");
   cmd("rw [S_push] at h");
   cmd("have g := chain h (one "+(k+2n)+" "+ray(rest.slice(1))+")");
   rawK=k+3n;rawW="0"+rest.slice(1);
  }else if(j===0||j===2){
   let b=j===0?k-1n:k,t=b/2n,a=2n+5n*t,V,cost=4n*k+13n+10n*BigInt(r);
   if(j===0&&r===0){cmd("have h := ret0 "+(k-1n)+" "+ray(u));V="00101"+u}
   else if(j===0){cmd("have h := ret4 "+(k-1n)+" "+(r-1)+" "+ray(u));V="001000"+"1100".repeat(r-1)+"111"+u}
   else {cmd("have h := ret2 "+k+" "+r+" "+ray(u));V="00"+"1100".repeat(r)+"111"+u}
   cmd("change Runs "+cost+" "+S(k,rawIn)+" (S 0 (pre [false,true,true] (rep P "+b+" "+ray(V)+"))) at h");
   if(b%2n===0n){
    cmd("have g := chain h (drain "+t+" 0 "+ray(V)+")");rawK=a;rawW="0"+V;
   }else{
    cmd("have h2 := chain h (drainOdd "+t+" "+ray(V.slice(1))+")");
    let h2c=cost+6n+30n*t*t+32n*t+8n*a+20n;
    rawK=a+4n;rawW=V.slice(1);
    if(j===2){
     if(!rawW.startsWith("01"))throw Error("odd ret2 normalization");
     let rest=rawW.slice(2);
     cmd("change Runs "+h2c+" "+S(k,rawIn)+" (S "+rawK+" (pre P "+ray(rest)+")) at h2");
     cmd("rw [S_push] at h2");
     if(!rest.startsWith("1"))throw Error("odd ret2 exit");
     rawK++;cmd("have g := chain h2 (one "+rawK+" "+ray(rest.slice(1))+")");rawK++;rawW="0"+rest.slice(1);
    }else cmd("have g := h2");
   }
  }else throw Error("terminal before final");
 }
 let k0=rawK,w0=rawW;
 cmd("change Runs "+dt+" "+S(k,rawIn)+" "+S(k0,w0)+" at g");
 while(w0.startsWith("01")){
  let w1=w0.slice(2);
  cmd("change Runs "+dt+" "+S(k,rawIn)+" (S "+k0+" (pre P "+ray(w1)+")) at g");
  cmd("rw [S_push] at g");k0++;w0=w1;
 }
 if(k0!==v.k||w0.replace(/0+$/,"")!==v.w)throw Error("endpoint "+i+" "+k0+" "+w0);
 cmd("simp only [pre, zero_blank] at g ⊢");
 cmd("exact g");
 lines.push("theorem path"+(i+1)+" : Runs "+v.T+" blankCfg "+S(v.k,v.w)+" := by");
 cmd("exact chain "+(i===0?"seed":"path"+i)+" hop"+i);
}
const {k,w,T}=x.trace.at(-1),N=x.firstE0;
if(w!=="001110111")throw Error("unexpected endpoint");
lines.push("def terminalCfg : Cfg := E (rep Q "+k+" blank) (pre [false,false,false,false,true,true,true,true,true,true] blank)");
lines.push("theorem terminalRun : Runs "+N+" blankCfg terminalCfg := by");
cmd("exact chain path"+x.sections+" (terminal3 "+k+" 0 "+ray("111")+")");
lines.push("theorem terminalRead : terminalCfg.q = 4 ∧ terminalCfg.r 0 = false := by exact ⟨rfl,rfl⟩");
lines.push("#print axioms terminalRun","#print axioms terminalRead","end BB6.Agent3Leaf2265");
console.log(lines.join("\n"));
