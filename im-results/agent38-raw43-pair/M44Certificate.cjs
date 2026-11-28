'use strict';
// Deterministic finite abstraction of Raw43 M44's proved packet parser.
// No search cap or randomized choice is used in the final certificate.
// Run: node M44Certificate.cjs --check
//      node M44Certificate.cjs --lean > M44Data.lean
const END=17, MAX=16;
const side=q=>q===10||q===11?0:1;
function action(q,b){
 let n,L=[],R=[];
 switch(q){
 case 0: if(b===END){n=10;L=[2]}else if(b===0){n=0;L=[0]}else if(b===1)n=1;else if(b===2)n=2;else{n=10;L=[2];R=[b-3]}break;
 case 1: if(b===END){n=10;L=[5]}else if(b===0)n=3;else if(b===1){n=0;L=[3]}else if(b===2)n=4;else if(b===3)n=5;else{n=10;L=[5];R=[b-4]}break;
 case 3: if(b!==END)R=[b+3];n=10;break;
 case 4: if(b===1){n=0;L=[6]}break;
 case 5: if(b===1)n=6;break;
 case 6: if(b===2)n=7;break;
 case 7: if(b===1){n=0;L=[3,0,7]}break;
 case 2: if(b===1)n=8;break;
 case 8: if(b===0){n=0;L=[5]}else if(b===1){n=0;L=[0,0,4]}else if(b===2)n=9;break;
 case 9: if(b===1){n=0;L=[3,0,4]}break;
 case 10: if(b===END)n=12;else if(b===0)n=11;else if(b>=2){n=10;R=[b-2,1]}break;
 case 11: if(b!==END){n=0;L=[b+1]}break;
 case 12: if(b===6)n=13;break;
 case 13: if(b===1){n=0;L=[3,0,7]}break;
 }
 if(n===undefined||b>END||b<0||[...L,...R].some(x=>x<0||x>MAX))return null;
 return {q:n,L,R};
}
function rightDfa(){
 const states=[{h:[],base:[],lost:false}],delta=[new Int32Array(MAX+1).fill(-1)],keys=new Map([['|0|0|',0]]);
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];let {h,base,lost}=states[i];h=h.slice();base=base.slice();
  if(base.length<1)base.push(b);
  else if(b===1){let n=h.at(-1);if(n<0){let v=-n+1;if(v===6)v=2;h[h.length-1]=-v}else h.push(-1)}
  else h.push(b+1);
  let non=h.filter(x=>x>0).length;if(non>3){let j=0;while(non>3){let x=h[j++];if(x>0)non--}h=h.slice(j);lost=true}
  let key=base.join(',')+'|0|'+(lost?1:0)+'|'+h.join(','),t=keys.get(key);if(t===undefined){t=states.length;keys.set(key,t);states.push({h,base,lost});delta.push(new Int32Array(MAX+1).fill(-1))}delta[i][b]=t;return t;
 }
 return {push,states,delta};
}
function leftDfa(){
 const states=[{h:[],lost:false}],keys=new Map([['0|',0]]),delta=[new Int32Array(MAX+1).fill(-1)];
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];let {h,lost}=states[i];h=h.slice();if(b===3||b===5){
  let a=h.at(-1);if(typeof a==='string'){let [n,f,w]=a.split(':');n=+n+1;if(n===3)n=2;w=(w+String.fromCharCode(65+b)).slice(-2);h[h.length-1]=[n,f,w].join(':')}
  else h.push([1,'',String.fromCharCode(65+b)].join(':'));
 }else h.push(b);
 let n=h.filter(x=>typeof x==='number').length;if(n>5){let j=0;while(n>5){let x=h[j++];if(typeof x==='number')n--}h=h.slice(j);lost=true}
 let key=(lost?'1':'0')+'|'+h.join(',');let t=keys.get(key);if(t===undefined){t=states.length;keys.set(key,t);states.push({h,lost});delta.push(new Int32Array(MAX+1).fill(-1))}return delta[i][b]=t;
 }
 return {push,states,delta};
}
const W0=[0,1,0,1,1,1,1,1,0,1,0,1];
function build(){
 const d=[leftDfa(),rightDfa()],edges=[new Map(),new Map()],waiting=[new Map(),new Map()],seen=new Set(),todo=[],work=[];
 const key=(q,l,r)=>q+','+l+','+r;
 function add(q,l,r){let x=key(q,l,r);if(!seen.has(x)){seen.add(x);todo.push([q,l,r])}}
 function get(m,i){let a=m.get(i);if(!a){a=[];m.set(i,a)}return a}
 function push(s,i,b){let j=d[s].push(i,b),es=get(edges[s],j);if(!es.some(e=>e[0]===b&&e[1]===i)){let e=[b,i];es.push(e);for(let t of get(waiting[s],j))work.push([t,e])}return j}
 function put(s,i,a){for(let k=a.length-1;k>=0;k--)i=push(s,i,a[k]);return i}
 function pop(t,e){let [q,l,r]=t,[b,j]=e,a=action(q,b);if(!a)throw Error('undefined abstract action '+JSON.stringify({t,e}));if(side(q)===0)l=j;else r=j;l=put(0,l,a.L);r=put(1,r,a.R);add(a.q,l,r)}
 for(let s=0;s<2;s++)edges[s].set(0,[[END,0]]);
 add(0,put(0,0,[3,0,7]),put(1,0,W0));
 let i=0,j=0;
 while(i<todo.length||j<work.length){
  if(j<work.length){let [t,e]=work[j++];pop(t,e);if(j>100000&&j===work.length){work.length=0;j=0}continue}
  let t=todo[i++],s=side(t[0]),x=t[s+1];get(waiting[s],x).push(t);for(let e of get(edges[s],x))work.push([t,e]);
 }
 return {states:todo,edges:edges.map(m=>Array.from({length:Math.max(...m.keys())+1},(_,i)=>m.get(i)||[])),delta:d.map(x=>x.delta.map(y=>Array.from(y))),nl:d[0].states.length,nr:d[1].states.length};
}
// Independent checker: accepts only explicit inverse edges, checks every
// possible actual pop and every pushed edge, and checks root membership.
function verify(c){
 const key=(q,l,r)=>q+','+l+','+r;
 const all=new Set(c.states.map(x=>key(...x)));
 const has=(s,j,b,i)=>c.edges[s][j]?.some(e=>e[0]===b&&e[1]===i)===true;
 function put(s,i,w){for(let k=w.length-1;k>=0;k--){const b=w[k],j=c.delta[s][i]?.[b];if(!(b>=0&&b<=MAX&&Number.isInteger(j)&&j>=0&&has(s,j,b,i)))throw Error('missing push edge');i=j}return i}
 if(!has(0,0,END,0)||!has(1,0,END,0))throw Error('missing empty edge');
 if(!all.has(key(0,put(0,0,[3,0,7]),put(1,0,W0))))throw Error('missing root');
 let checked=0;
 for(const [q,l,r]of c.states){
  if(!(q>=0&&q<14&&l>=0&&l<c.nl&&r>=0&&r<c.nr))throw Error('bad triple');
  const s=side(q),i=s===0?l:r;
  for(const [b,j]of c.edges[s][i]||[]){
   const a=action(q,b);if(!a)throw Error('uncovered action');
   const L=put(0,s===0?j:l,a.L),R=put(1,s===1?j:r,a.R);
   if(!all.has(key(a.q,L,R)))throw Error('missing successor');
   checked++;
  }
 }
 return {states:all.size,left:c.nl,right:c.nr,edges:c.edges.map(x=>x.reduce((n,a)=>n+a.length,0)),checked};
}
function leanData(c){
 const nl=c.nl,nr=c.nr,rows=Array.from({length:14*nl},()=>[]);
 for(const [q,l,r]of c.states)rows[q*nl+l].push(r);
 function tree(xs,empty){if(!xs.length)return '.leaf '+empty;if(xs.every(x=>x===xs[0]))return '.leaf '+xs[0];return '.branch ('+tree(xs.filter((_,i)=>i%2===0),empty)+') ('+tree(xs.filter((_,i)=>i%2===1),empty)+')'}
 let s='import M44Checker\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 10000\nnamespace BB6.Agent38M44\n';
 const rownames=rows.map((xs,i)=>{if(!xs.length)return 'emptyRow';xs.sort((a,b)=>a-b);let mask=xs.reduce((m,x)=>m|(1n<<BigInt(x)),0n);s+='def row'+i+' : Row := row ['+xs+'] '+mask+' (by decide)\n';return 'row'+i});
 for(let side=0;side<2;side++){
  let n=side===0?nl:nr,pred=Array.from({length:n},(_,j)=>c.edges[side][j]||[]);
  s+='def pred'+side+' : Lookup (List (Nat × Nat)) :=\n'+tree(pred.map(es=>'['+es.map(([b,i])=>'('+b+','+i+')').join(',')+']'),'[]')+'\n';
  let delta=c.delta[side].map(xs=>xs.reduce((m,j,b)=>m|(BigInt(j+1)<<BigInt(11*b)),0n).toString());
  s+='def delta'+side+' : Lookup Nat :=\n'+tree(delta,'0')+'\n';
 }
 s+='def allRows : Lookup Row :=\n'+tree(rownames,'emptyRow')+'\ndef cert : Cert := ⟨'+nl+','+nr+',⟨pred0,delta0⟩,⟨pred1,delta1⟩,allRows⟩\n';
 s+='theorem initLeft : pushWord cert.left [3,0,7] 0 = some '+c.states[0][1]+' := by decide\n';
 s+='theorem initRight : pushWord cert.right W0 0 = some '+c.states[0][2]+' := by decide\n';
 s+='theorem initGood : cert.good 0 '+c.states[0][1]+' '+c.states[0][2]+' = true := by decide\n';
 s+='theorem emptyL : (17,0) ∈ cert.left.pred.get 0 := by decide\ntheorem emptyR : (17,0) ∈ cert.right.pred.get 0 := by decide\n';
 for(let q=0;q<14;q++)s+='theorem closed'+q+' : checkQ cert '+q+' = true := by decide\n';
 s+='theorem certClosed : closed cert := by\n  intro q hq\n  have h : '+Array.from({length:14},(_,i)=>'q='+i).join(' ∨ ')+' := by omega\n  rcases h with '+Array(14).fill('rfl').join(' | ')+'\n'+Array.from({length:14},(_,i)=>'  · exact closed'+i).join('\n')+'\n#print axioms certClosed\nend BB6.Agent38M44\n';
 return s;
}
if(typeof process!=='undefined'&&typeof require!=='undefined'&&require.main===module){
 const c=build(),summary=verify(c);
 if(process.argv.includes('--lean'))process.stdout.write(leanData(c));
 else if(process.argv.includes('--json'))process.stdout.write(JSON.stringify(c));
 else console.log(JSON.stringify(summary));
}
