function make(a,f){const t=[7,a,11,12,15,1,6,18,4,17,f,24];let E=[];for(let q=0;q<6;q++)for(let d=0;d<2;d++)for(let b=0;b<8;b++){let p=d?0:2,r=q,k=0,s=b;while(p>=0&&p<3&&k<145){let c=t[2*r+((s>>p)&1)];if(c===24)break;s=(s&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=(c&1)?1:-1;k++}E[(q*2+d)*8+b]=p<0||p>=3?[r,+(p>=3),s,k]:null}return E}
function comp(x){let s=x.slice().reverse().join("");return s.replace(/(.{1,3}?)\1{3,}/g,m=>{for(let j=1;j<=3;j++)if(m.length%j===0&&m.slice(0,j).repeat(m.length/j)===m)return "("+m.slice(0,j)+")^"+m.length/j+" ";return m})}
function sim(a,f,m,z,c,k,lim,threshold=1e14){let E=make(a,f),L=m===null?[6]:("5".repeat(6*k+7)+"4".repeat(z)+"5".repeat(3*k+2)+"6".repeat(c+1)+"4").split("").map(Number).reverse(),R=m===null?[]:("232".repeat(m)+"231").split("").map(Number).reverse(),q=m===null?2:3,d=m===null?1:0,t=m===null?2:0,rows=[],last=0,prev="",er=0,rot=0,ar=0,events=0;
const info=()=>[q,d,comp(L).slice(0,250),comp(R).slice(0,250)];
const take=(S,pat)=>pat.every((v,i)=>v===S[S.length-1-i]);
const runlen=(S,b)=>{let p=0;while(S[S.length-1-p]===b)p++;return p};
for(let j=0;j<lim&&t<threshold;j++){
if(q===3&&d===0&&L.at(-1)===5&&take(R,[2,3,2])){let ls=L.slice().reverse().join(""),rs=R.slice().reverse().join("");let lm=ls.match(/^(5+)(4+)(5+)(6+)4$/),rm=rs.match(/^(232)*231$/);if(lm&&rm){let o=[lm[1].length,lm[2].length,lm[3].length,lm[4].length-1,(rs.length-3)/3];if(JSON.stringify(o)!==prev){rows.push([j,t,"M",o]);prev=JSON.stringify(o);if(rows.length>=25)return rows}}}
if(t>last*2+1000000){rows.push([j,t,"sample",...info()]);last=t;if(rows.length>25)return rows}
if(L.length+R.length>1000000)return {rows,limit:"tape",t,j,er,rot,ar,events};
if(q===4&&d===1&&L.at(-1)===1&&(R.at(-1)===1||R.at(-1)===5)){while(R.at(-1)===1||R.at(-1)===5){let x=R.pop();if(x===1){L.pop();L.push(3,1);t+=19}else{L.push(1);t+=7}er++}continue}
if(q===4&&d===1&&R.at(-1)===1&&L.at(-1)===3){let p=1;while(L[L.length-1-p]===3||L[L.length-1-p]===1)p++;if(L[L.length-1-p]===5){L[L.length-1-p]=3;L.pop();L.push(1,1);R.pop();t+=22*p+15;rot++;continue}}
if(q===4&&d===1&&take(R,[1,1,1])&&L.at(-1)===3&&L[0]===2){let p=runlen(L,3);if(p===L.length-1){let n=runlen(R,1),v=Math.floor((n-1)/2);R.length-=2*v;L.length=1;for(let i=0;i<p+4*v;i++)L.push(3);t+=v*(18*p+60)+36*v*(v-1);er+=v;continue}}
if(q===0&&d===1&&take(R,[1,1,5])&&L[0]===2){let p=runlen(L,3);if(p===L.length-1){let n=0;while(R.length>=3*(n+1)&&[1,1,5].every((x,i)=>R[R.length-1-3*n-i]===x))n++;let dlt=0,cc=0,coef=0,unit=1;if(a===21&&f===0||a===23&&(f===17||f===11)){dlt=5;cc=f===11?81:83;coef=18}else if(a===21&&f===6||a===23&&f===1){dlt=12;cc=f===1?382:384;coef=54;unit=2;if(p===0)dlt=0}else if(a===23&&f===19){dlt=10;cc=254;coef=36;unit=2}
let v=Math.floor(n/unit);if(v&&dlt){R.length-=3*v*unit;L.length=1;for(let i=0;i<p+dlt*v;i++)L.push(3);t+=v*(coef*p+cc)+coef*dlt*v*(v-1)/2;ar+=v;continue}}}
let S=d?R:L,b=S.at(-1)||0,Z=E[(q*2+d)*8+b];if(!Z)return {rows,halt:[j,t,q,d,b],L:comp(L),R:comp(R)};if(q===0&&(d&&b%2||!d&&b>=4)||q===1&&d&&b===6||q===2&&d&&(b===3||b===7)||q===5){events++}
let n=1,pat=[b],out=[Z[2]],Q=Z[0],cost=Z[3];if(Z[1]===d&&S.length){while(Q!==q&&pat.length<6&&pat.length<S.length){let v=S[S.length-1-pat.length],w=E[(Q*2+d)*8+v];if(!w||w[1]!==d)break;pat.push(v);out.push(w[2]);Q=w[0];cost+=w[3]}if(Q===q){while((n+1)*pat.length<=S.length&&pat.every((v,i)=>v===S[S.length-1-n*pat.length-i]))n++;if(n>1){S.length-=n*pat.length;let D=d?L:R;for(let i=0;i<n;i++)for(let x of out)if(D.length||x)D.push(x);t+=n*cost;continue}}}S.pop();[q,d,b]=Z;t+=Z[3];let D=d?L:R;if(D.length||b)D.push(b)}return {rows,t,now:info(),er,rot,ar,events}}

if(typeof module!=='undefined')module.exports={sim,make};
