// Tracks aligned block types from the outermost nonblank, plus a local window.
function gramDfa({win,width,mode,mod=1,skip=0}){
 const W=2**win,B=2**width,states=[[0,0,0,0,0,0]],ids=new Map([["empty",0]]),delta=[[-1,-1]];
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];if(i===0&&!b)return delta[i][b]=0;
 let [phase,top,mask,c,last,short]=states[i],p=(phase+1)%width,t=(top*2+b)%W,z=mask,k=c,la=last,sh=Math.min(short+1,skip);
 if(p===0&&sh===skip){let v=t%B;if(mode===0)z|=1<<v;else if(mode===1){z|=1<<v;k=(k+(v===B-1))%mod}else if(mode===2){if(v===B-1)k=Math.min(k+1,mod);else z|=1<<v}else if(mode===3){z|=1<<v;if(v===B-1)k=Math.min(k+1,mod);la=v}else if(mode===4){z|=1<<v;if(v===B-1)k=(k+1)%mod;la=v}}
 let x=[p,t,z,k,la,sh],key=x.join(","),j=ids.get(key);if(j===undefined){j=states.length;states.push(x);ids.set(key,j);delta.push([-1,-1])}delta[i][b]=j;return j
 }
 return {push,finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>states.length}
}
