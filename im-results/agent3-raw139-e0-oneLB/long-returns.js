// Exact return-map discovery and primitive replay. Node.js or Code Mode.
// 24 means final hole, not a defined transition.
const tables=[[7,20,11,1,14,9,17,16,6,11,0,24],[7,24,11,22,14,9,17,16,6,11,16,0],[7,24,11,22,14,9,17,16,6,11,15,0],[7,23,11,13,14,21,24,16,6,11,3,0]];
function ret(u){let i=1,phi="",a=0,b=0;while(true){if(u[i]==="1"){i++;phi+="0";b++}else if(u[i+1]==="0"){i+=2;return {u:("10"+phi+"101"+u.slice(i)).replace(/0+$/,"")+"0".repeat(40),a,b,stop:0}}else if(u[i+2]==="0"){i+=3;phi+="100";a++}else if(u[i+3]==="0"){i+=4;return {u:("10"+phi+"10011"+u.slice(i)).replace(/0+$/,"")+"0".repeat(40),a,b,stop:1}}else return {a,b,stop:2,i}}}
function exactMap(){let u="11"+"0".repeat(40),n=[2,2],totalA=0,totalB=0,stats=[0,0];for(let k=0;k<10000;k++){let z=ret(u);if(z.stop===2)return {k,frontier:n,query:[n[0]+5+3*z.a+3*z.b,n[1]+5+7*z.a+3*z.b],a:z.a,b:z.b,totalA,totalB,stats};stats[z.stop]++;totalA+=z.a;totalB+=z.b;for(let j=0;j<2;j++)n[j]+=12+(8+4*j)*z.a+4*z.b+4*z.stop;u=z.u}throw Error("no final delimiter")}
function direct(p,limit){let a=new Uint8Array(1048576),off=524288,h=off,q=0,n=0;while(n<limit){if(h<0||h>=a.length)throw Error("tape bounds");let v=p[2*q+a[h]];if(v===24)return {n,s:2*q+a[h],h:h-off};a[h]=(v>>1)&1;h+=v&1?1:-1;q=v>>2;n++}throw Error("no query")}
if(typeof console!=="undefined"){console.log(exactMap());for(let t of tables)console.log(t,direct(t,200000000))}
