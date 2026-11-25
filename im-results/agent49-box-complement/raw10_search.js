// Deterministic first-hole candidate generator. Untrusted data only.
const MAX=256, LOOKBACK=64;
function classify(rows) {
  let q=0,h=0,ones=new Set(),history=[];
  for(let t=0;t<=MAX;t++){
    let c={q,h,ones:new Set(ones)};history.push(c);
    let mn=h,mx=h;
    for(let j=t-1;j>=0&&j>=t-LOOKBACK;j--){
      let a=history[j];mn=Math.min(mn,a.h);mx=Math.max(mx,a.h);
      if(a.q!==q) continue;
      let delta=h-a.h;
      for(let right of [true,false]){
        if(right?delta<0:delta>0) continue;
        let boundary=right?mn:mx;
        let side=x=>right?x>=boundary:x<=boundary;
        if([...a.ones].every(x=>!side(x)||ones.has(x+delta))&&
           [...ones].every(y=>!side(y-delta)||a.ones.has(y-delta)))
          return {type:"side",entry:j,period:t-j,right,boundary};
      }
    }
    let slot=2*q+Number(ones.has(h)),v=rows[slot];
    if(v===0)return {type:"hole",steps:t,slot};
    if(v===25)return {type:"halt",steps:t,slot};
    if(t===MAX)return {type:"long",steps:t};
    --v;if((v>>1)&1)ones.add(h);else ones.delete(h);
    h+=(v&1)?1:-1;q=v>>2;
  }
  throw new Error("unreachable");
}
function generate(depthLimit=2) {
  const side=[],halt=[],front=[];
  let root=[8,0,11,0,0,0,0,0,0,0,0,0];
  halt.push({rows:root.slice(),steps:2,slot:5});
  function visit(rows,cut,depth){
    let a=classify(rows);
    if(a.type==="side"){side.push({rows:rows.slice(),...a});return;}
    if(a.type!=="hole"){front.push({rows:rows.slice(),...a});return;}
    halt.push({rows:rows.slice(),steps:a.steps,slot:a.slot});
    if(depth===depthLimit){front.push({rows:rows.slice(),...a});return;}
    for(let v=1;v<=4*Math.min(cut+1,6);v++){
      rows[a.slot]=v;visit(rows,Math.max(cut,((v-1)>>2)+1),depth+1);
    }
    rows[a.slot]=0;
  }
  for(let v=1;v<=16;v++){
    root[5]=v;visit(root,Math.max(3,((v-1)>>2)+1),1);root[5]=0;
  }
  return {side,halt,front};
}
if(typeof module!=="undefined"){module.exports={classify,generate};if(require.main===module)console.log(JSON.stringify(generate(),null,2));}
