const assert=require("node:assert/strict");
const ts=["1RB0LE_1RC0RC_0RD0RA_1LD1LB_0LF---_1LA1LB","1RB1RE_1RC0RC_0RD0RA_1LD1LB_---0RF_0RC0RE","1RB0LF_1RC0RC_0RD0RA_1LD1LB_1LA1LB_0LE---","1RB1RF_1RC0RC_0RD0RA_1LD1LB_0RC0RF_---0RE"];
const dec=s=>s.replace(/_/g,"").match(/.../g);
function run(t,L,R,n,q=4,closed=false,firstReturn=false){
 const p=dec(t),tape=new Map();let h=0;
 for(let i=0;i<L.length;i++)tape.set(-1-i,+L[i]);for(let i=0;i<R.length;i++)tape.set(i,+R[i]);
 const read=i=>tape.get(i)||0;
 for(let k=0;k<n;k++){if(!closed)assert.equal(tape.has(h),true);const m=p[2*q+read(h)];assert.notEqual(m,"---");tape.set(h,+m[0]);h+=m[1]==="R"?1:-1;q=m.charCodeAt(2)-65;if(firstReturn&&k<n-1)assert.notEqual(q,4)}
 assert.equal(q,4);
 return {h,check(l,r){for(const [i,v] of tape){const x=i-h;assert.equal(v,+(x<0?l[-x-1]||0:r[x]||0))}for(let i=0;i<l.length;i++)assert.equal(read(h-i-1),+l[i]);for(let i=0;i<r.length;i++)assert.equal(read(h+i),+r[i])}}
}
const rules=[["001","00","0","0011",12],["010","0","","0010",3],["11","0010011","1101100","00",11],["000","00","1","0011",12],["10","0011","1101","00",8],["11","0010000","001100","001",16],["11","0011","1100","00",8]];
for(const [l,r,L,R,n] of rules){const x=run(ts[0],l,r,n,4,false,true);assert.equal(x.h,L.length-l.length);assert.equal(L.length+R.length,l.length+r.length);x.check(L,R)}
run(ts[0],"","",9,0,true).check("","001");run(ts[1],"","",9,0,true).check("10","1");
const swap=q=>q===4?5:q===5?4:q;
for(let i=0;i<2;i++){const p=dec(ts[i]),a=dec(ts[i+2]);for(let q=0;q<6;q++)for(let b=0;b<2;b++){const m=p[2*q+b];assert.equal(a[2*swap(q)+b],m==="---"?m:m.slice(0,2)+String.fromCharCode(65+swap(m.charCodeAt(2)-65)))}}
const right=n=>"001"+"00111".repeat(n);
for(let n=0;n<64;n++){run(ts[0],"1101",right(n),52*n+148,4,true).check("11011",right(n+2));run(ts[0],"11011",right(n),26*n+66,4,true).check("1101",right(n+2));run(ts[1],"10"+"1".repeat(n),"1".repeat(2*n+1),4*n+11,4,true).check("10"+"1".repeat(n+1),"1".repeat(2*n+3))}
console.log("7 arbitrary-tail rewrites; 2 blank entries; 2 conjugacies; 192 parametric boundary instances passed.");
