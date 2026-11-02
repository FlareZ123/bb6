"use strict";
/** One exact accelerated Machine C transition.
 * @param {[number,number,number]} s
 * @returns {{steps:number,state:[number,number,number]|null}} */
function jump(s) {
  const [a,k,c]=s;
  if(a>0 && c>=4) {
    const n=Math.min(a,c-3);
    return {steps:n,state:[a-n,k+n,c-n]};
  }
  if(c===1)return {steps:1,state:[a,k+1,0]};
  if(c===2)return {steps:1,state:null};
  if(c===3)return {steps:1,state:[a,k+2,1]};
  if(c===0) {
    if(a===0)return {steps:1,state:[1,0,2*k+2]};
    if(a===1)return {steps:1,state:k===0?[5,0,1]:[2,2,2*k-1]};
    return {steps:1,state:[a-2,1,2*k+1]};
  }
  return {steps:1,state:k%2===0?[2*k+2,2,c-3]:[2*k+3,0,c]};
}
module.exports={jump};
