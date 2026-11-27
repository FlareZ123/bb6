// Prepared nonbinary G cylinder: exact original-source-clause comparisons.
const m=require("./affine_stack_replay.js")();
function protectedGood(X){
 if(!X.length||X[0]<=0||X[0]===2)return false;
 for(let i=1;i<X.length;i++){
  if(X[i]===0)return true;
  if(X[i]===2&&(i<2||X[i-1]!==1))return false;
 }return true;
}
function arithmetic(X,L){
 X=X.slice();L=L.slice();let t=0;
 for(let i=0;i<10000;i++){
  if(!protectedGood(X))throw Error("invariant "+JSON.stringify(X));
  if(L[0]>=2)return t+2;
  if(L[0]===0){L.shift();X[0]+=2;t+=2;continue}
  if(L[1]===0){L.splice(0,2);X[0]+=3;X.unshift(1);t+=5;continue}
  if(L[1]!==1)throw Error("unexpected left");
  let d=0;while(X[d]===1)d++;
  if(X[d]>=3){
   const a=X[d]-3,c=L[2];t+=41+6*d;
   if(c>=1)return t+2;
   L.splice(0,3,1);X=[...Array(d+4).fill(1),a,...X.slice(d+1)];continue;
  }
  let b=0,b1=0,b2=0,z=0;
  while(X[b]===1||X[b]===2){if(X[b]===1){b1++;z++}else{b2++;z=0}b++}
  return t+(X[b]>=3?40+4*b1+10*b2+2*z:32+4*b1+10*b2);
 }throw Error("timeout");
}
function run(s){
 let t=0n;for(let i=0;i<10000;i++){let a=m.advance(s);s=a.s;t+=a.cost;if(a.halt)return Number(t)}
 throw Error("timeout");
}
function check(){
 let ncases=0,nonpaired=0,max=0;
 for(let n=3;n<=8;n++)for(let i=0;i<2**n;i++){
  let w=i.toString(2).padStart(n,"0");if(!w.includes("111"))continue;
  let W=w.split("").map(Number);
  for(let M of [1,5])for(let z of [0,1,3])for(let x of [2,3,4,5,9])
  for(let T of [[],[1],[1,1],[0,1],[4,0,1,3],[1,1,9],[0,1,1],[3,1],[9,2,7],[0,1,0,1]]){
   const X=[...Array(z+3).fill(1),x-2,...T.map(a=>a+1)];
   if(!protectedGood(X))continue;
   const L=[0,...W.slice().reverse(),...Array(M+1).fill(0),1];
   const expected=2*M+42+W.reduce((a,b)=>a+(b?7:2),0)+6*z+arithmetic(X,L);
   const got=run({q:"CR",L:m.rle([0]),R:m.rle([...Array(M).fill(0),...W,1,...Array(z).fill(0),x,...T]),K:[]});
   if(got!==expected)throw Error(JSON.stringify({w,M,z,x,T,expected,got}));
   ncases++;if(x===2&&T.some((a,j)=>a===1&&(j===0||T[j-1]!==0)))nonpaired++;
   max=Math.max(max,got);
  }
 }
 console.log(JSON.stringify({ncases,nonpaired,max}));
}
if(require.main===module)check();
module.exports={protectedGood,arithmetic};
