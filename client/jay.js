// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if(a != null)
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
}

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}
if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+this.DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { this.fromRadix(s,b); return; }
  this.t = 0;
  this.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      this[this.t++] = x;
    else if(sh+k > this.DB) {
      this[this.t-1] |= (x&((1<<(this.DB-sh))-1))<<sh;
      this[this.t++] = (x>>(this.DB-sh));
    }
    else
      this[this.t-1] |= x<<sh;
    sh += k;
    if(sh >= this.DB) sh -= this.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    this.s = -1;
    if(sh > 0) this[this.t-1] |= ((1<<(this.DB-sh))-1)<<sh;
  }
  this.clamp();
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  if(this.s < 0) return "-"+this.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return this.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = this.t;
  var p = this.DB-(i*this.DB)%k;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (this[i]&((1<<p)-1))<<(k-p);
        d |= this[--i]>>(p+=this.DB-k);
      }
      else {
        d = (this[i]>>(p-=k))&km;
        if(p <= 0) { p += this.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return (this.s<0)?-r:r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/this.DB), c = (this.s<<bs)&this.DM, i;
  for(i = this.t-1; i >= 0; --i) {
    r[i+ds+1] = (this[i]>>cbs)|c;
    c = (this[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = this.t+ds+1;
  r.s = this.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  r.s = this.s;
  var ds = Math.floor(n/this.DB);
  if(ds >= this.t) { r.t = 0; return; }
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = this[ds]>>bs;
  for(var i = ds+1; i < this.t; ++i) {
    r[i-ds-1] |= (this[i]&bm)<<cbs;
    r[i-ds] = this[i]>>bs;
  }
  if(bs > 0) r[this.t-ds-1] |= (this.s&bm)<<cbs;
  r.t = this.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]-a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c -= a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = this.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = this.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) this.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = this.s, ms = m.s;
  var nsh = this.DB-nbits(pm[pm.t-1]);	// normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<this.F1)+((ys>1)?y[ys-2]>>this.F2:0);
  var d1 = this.FV/yt, d2 = (1<<this.F1)/yt, e = 1<<this.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y);	// "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?this.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	// Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);	// Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;		// y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;	// y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;	// y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	// y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;		// y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)	// pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;

// public
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);

// Copyright (c) 2005-2009  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Extended JavaScript BN functions, required for RSA private ops.

// Version 1.1: new BigInteger("0", 10) returns "proper" zero
// Version 1.2: square() API, isProbablePrime fix

// (public)
function bnClone() { var r = nbi(); this.copyTo(r); return r; }

// (public) return value as integer
function bnIntValue() {
  if(this.s < 0) {
    if(this.t == 1) return this[0]-this.DV;
    else if(this.t == 0) return -1;
  }
  else if(this.t == 1) return this[0];
  else if(this.t == 0) return 0;
  // assumes 16 < DB < 32
  return ((this[1]&((1<<(32-this.DB))-1))<<this.DB)|this[0];
}

// (public) return value as byte
function bnByteValue() { return (this.t==0)?this.s:(this[0]<<24)>>24; }

// (public) return value as short (assumes DB>=16)
function bnShortValue() { return (this.t==0)?this.s:(this[0]<<16)>>16; }

// (protected) return x s.t. r^x < DV
function bnpChunkSize(r) { return Math.floor(Math.LN2*this.DB/Math.log(r)); }

// (public) 0 if this == 0, 1 if this > 0
function bnSigNum() {
  if(this.s < 0) return -1;
  else if(this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
  else return 1;
}

// (protected) convert to radix string
function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

// (protected) convert from radix string
function bnpFromRadix(s,b) {
  this.fromInt(0);
  if(b == null) b = 10;
  var cs = this.chunkSize(b);
  var d = Math.pow(b,cs), mi = false, j = 0, w = 0;
  for(var i = 0; i < s.length; ++i) {
    var x = intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-" && this.signum() == 0) mi = true;
      continue;
    }
    w = b*w+x;
    if(++j >= cs) {
      this.dMultiply(d);
      this.dAddOffset(w,0);
      j = 0;
      w = 0;
    }
  }
  if(j > 0) {
    this.dMultiply(Math.pow(b,j));
    this.dAddOffset(w,0);
  }
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) alternate constructor
function bnpFromNumber(a,b,c) {
  if("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if(a < 2) this.fromInt(1);
    else {
      this.fromNumber(a,c);
      if(!this.testBit(a-1))	// force MSB set
        this.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,this);
      if(this.isEven()) this.dAddOffset(1,0); // force odd
      while(!this.isProbablePrime(b)) {
        this.dAddOffset(2,0);
        if(this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a-1),this);
      }
    }
  }
  else {
    // new BigInteger(int,RNG)
    var x = new Array(), t = a&7;
    x.length = (a>>3)+1;
    b.nextBytes(x);
    if(t > 0) x[0] &= ((1<<t)-1); else x[0] = 0;
    this.fromString(x,256);
  }
}

// (public) convert to bigendian byte array
function bnToByteArray() {
  var i = this.t, r = new Array();
  r[0] = this.s;
  var p = this.DB-(i*this.DB)%8, d, k = 0;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) != (this.s&this.DM)>>p)
      r[k++] = d|(this.s<<(this.DB-p));
    while(i >= 0) {
      if(p < 8) {
        d = (this[i]&((1<<p)-1))<<(8-p);
        d |= this[--i]>>(p+=this.DB-8);
      }
      else {
        d = (this[i]>>(p-=8))&0xff;
        if(p <= 0) { p += this.DB; --i; }
      }
      if((d&0x80) != 0) d |= -256;
      if(k == 0 && (this.s&0x80) != (d&0x80)) ++k;
      if(k > 0 || d != this.s) r[k++] = d;
    }
  }
  return r;
}

function bnEquals(a) { return(this.compareTo(a)==0); }
function bnMin(a) { return(this.compareTo(a)<0)?this:a; }
function bnMax(a) { return(this.compareTo(a)>0)?this:a; }

// (protected) r = this op a (bitwise)
function bnpBitwiseTo(a,op,r) {
  var i, f, m = Math.min(a.t,this.t);
  for(i = 0; i < m; ++i) r[i] = op(this[i],a[i]);
  if(a.t < this.t) {
    f = a.s&this.DM;
    for(i = m; i < this.t; ++i) r[i] = op(this[i],f);
    r.t = this.t;
  }
  else {
    f = this.s&this.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(this.s,a.s);
  r.clamp();
}

// (public) this & a
function op_and(x,y) { return x&y; }
function bnAnd(a) { var r = nbi(); this.bitwiseTo(a,op_and,r); return r; }

// (public) this | a
function op_or(x,y) { return x|y; }
function bnOr(a) { var r = nbi(); this.bitwiseTo(a,op_or,r); return r; }

// (public) this ^ a
function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

// (public) this & ~a
function op_andnot(x,y) { return x&~y; }
function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

// (public) ~this
function bnNot() {
  var r = nbi();
  for(var i = 0; i < this.t; ++i) r[i] = this.DM&~this[i];
  r.t = this.t;
  r.s = ~this.s;
  return r;
}

// (public) this << n
function bnShiftLeft(n) {
  var r = nbi();
  if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
  return r;
}

// (public) this >> n
function bnShiftRight(n) {
  var r = nbi();
  if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
  return r;
}

// return index of lowest 1-bit in x, x < 2^31
function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

// (public) returns index of lowest 1-bit (or -1 if none)
function bnGetLowestSetBit() {
  for(var i = 0; i < this.t; ++i)
    if(this[i] != 0) return i*this.DB+lbit(this[i]);
  if(this.s < 0) return this.t*this.DB;
  return -1;
}

// return number of 1 bits in x
function cbit(x) {
  var r = 0;
  while(x != 0) { x &= x-1; ++r; }
  return r;
}

// (public) return number of set bits
function bnBitCount() {
  var r = 0, x = this.s&this.DM;
  for(var i = 0; i < this.t; ++i) r += cbit(this[i]^x);
  return r;
}

// (public) true iff nth bit is set
function bnTestBit(n) {
  var j = Math.floor(n/this.DB);
  if(j >= this.t) return(this.s!=0);
  return((this[j]&(1<<(n%this.DB)))!=0);
}

// (protected) this op (1<<n)
function bnpChangeBit(n,op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r,op,r);
  return r;
}

// (public) this | (1<<n)
function bnSetBit(n) { return this.changeBit(n,op_or); }

// (public) this & ~(1<<n)
function bnClearBit(n) { return this.changeBit(n,op_andnot); }

// (public) this ^ (1<<n)
function bnFlipBit(n) { return this.changeBit(n,op_xor); }

// (protected) r = this + a
function bnpAddTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]+a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c += a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c += a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += a.s;
  }
  r.s = (c<0)?-1:0;
  if(c > 0) r[i++] = c;
  else if(c < -1) r[i++] = this.DV+c;
  r.t = i;
  r.clamp();
}

// (public) this + a
function bnAdd(a) { var r = nbi(); this.addTo(a,r); return r; }

// (public) this - a
function bnSubtract(a) { var r = nbi(); this.subTo(a,r); return r; }

// (public) this * a
function bnMultiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

// (public) this^2
function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

// (public) this / a
function bnDivide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

// (public) this % a
function bnRemainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

// (public) [this/a,this%a]
function bnDivideAndRemainder(a) {
  var q = nbi(), r = nbi();
  this.divRemTo(a,q,r);
  return new Array(q,r);
}

// (protected) this *= n, this >= 0, 1 < n < DV
function bnpDMultiply(n) {
  this[this.t] = this.am(0,n-1,this,0,0,this.t);
  ++this.t;
  this.clamp();
}

// (protected) this += n << w words, this >= 0
function bnpDAddOffset(n,w) {
  if(n == 0) return;
  while(this.t <= w) this[this.t++] = 0;
  this[w] += n;
  while(this[w] >= this.DV) {
    this[w] -= this.DV;
    if(++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
}

// A "null" reducer
function NullExp() {}
function nNop(x) { return x; }
function nMulTo(x,y,r) { x.multiplyTo(y,r); }
function nSqrTo(x,r) { x.squareTo(r); }

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo;

// (public) this^e
function bnPow(e) { return this.exp(e,new NullExp()); }

// (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.
function bnpMultiplyLowerTo(a,n,r) {
  var i = Math.min(this.t+a.t,n);
  r.s = 0; // assumes a,this >= 0
  r.t = i;
  while(i > 0) r[--i] = 0;
  var j;
  for(j = r.t-this.t; i < j; ++i) r[i+this.t] = this.am(0,a[i],r,i,0,this.t);
  for(j = Math.min(a.t,n); i < j; ++i) this.am(0,a[i],r,i,0,n-i);
  r.clamp();
}

// (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.
function bnpMultiplyUpperTo(a,n,r) {
  --n;
  var i = r.t = this.t+a.t-n;
  r.s = 0; // assumes a,this >= 0
  while(--i >= 0) r[i] = 0;
  for(i = Math.max(n-this.t,0); i < a.t; ++i)
    r[this.t+i-n] = this.am(n-i,a[i],r,0,0,this.t+i-n);
  r.clamp();
  r.drShiftTo(1,r);
}

// Barrett modular reduction
function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
  else if(x.compareTo(this.m) < 0) return x;
  else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
}

function barrettRevert(x) { return x; }

// x = x mod m (HAC 14.42)
function barrettReduce(x) {
  x.drShiftTo(this.m.t-1,this.r2);
  if(x.t > this.m.t+1) { x.t = this.m.t+1; x.clamp(); }
  this.mu.multiplyUpperTo(this.r2,this.m.t+1,this.q3);
  this.m.multiplyLowerTo(this.q3,this.m.t+1,this.r2);
  while(x.compareTo(this.r2) < 0) x.dAddOffset(1,this.m.t+1);
  x.subTo(this.r2,x);
  while(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = x^2 mod m; x != r
function barrettSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = x*y mod m; x,y != r
function barrettMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo;

// (public) this^e % m (HAC 14.85)
function bnModPow(e,m) {
  var i = e.bitLength(), k, r = nbv(1), z;
  if(i <= 0) return r;
  else if(i < 18) k = 1;
  else if(i < 48) k = 3;
  else if(i < 144) k = 4;
  else if(i < 768) k = 5;
  else k = 6;
  if(i < 8)
    z = new Classic(m);
  else if(m.isEven())
    z = new Barrett(m);
  else
    z = new Montgomery(m);

  // precomputation
  var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
  g[1] = z.convert(this);
  if(k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1],g2);
    while(n <= km) {
      g[n] = nbi();
      z.mulTo(g2,g[n-2],g[n]);
      n += 2;
    }
  }

  var j = e.t-1, w, is1 = true, r2 = nbi(), t;
  i = nbits(e[j])-1;
  while(j >= 0) {
    if(i >= k1) w = (e[j]>>(i-k1))&km;
    else {
      w = (e[j]&((1<<(i+1))-1))<<(k1-i);
      if(j > 0) w |= e[j-1]>>(this.DB+i-k1);
    }

    n = k;
    while((w&1) == 0) { w >>= 1; --n; }
    if((i -= n) < 0) { i += this.DB; --j; }
    if(is1) {	// ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    }
    else {
      while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
      if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
      z.mulTo(r2,g[w],r);
    }

    while(j >= 0 && (e[j]&(1<<i)) == 0) {
      z.sqrTo(r,r2); t = r; r = r2; r2 = t;
      if(--i < 0) { i = this.DB-1; --j; }
    }
  }
  return z.revert(r);
}

// (public) gcd(this,a) (HAC 14.54)
function bnGCD(a) {
  var x = (this.s<0)?this.negate():this.clone();
  var y = (a.s<0)?a.negate():a.clone();
  if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
  var i = x.getLowestSetBit(), g = y.getLowestSetBit();
  if(g < 0) return x;
  if(i < g) g = i;
  if(g > 0) {
    x.rShiftTo(g,x);
    y.rShiftTo(g,y);
  }
  while(x.signum() > 0) {
    if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
    if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
    if(x.compareTo(y) >= 0) {
      x.subTo(y,x);
      x.rShiftTo(1,x);
    }
    else {
      y.subTo(x,y);
      y.rShiftTo(1,y);
    }
  }
  if(g > 0) y.lShiftTo(g,y);
  return y;
}

// (protected) this % n, n < 2^26
function bnpModInt(n) {
  if(n <= 0) return 0;
  var d = this.DV%n, r = (this.s<0)?n-1:0;
  if(this.t > 0)
    if(d == 0) r = this[0]%n;
    else for(var i = this.t-1; i >= 0; --i) r = (d*r+this[i])%n;
  return r;
}

// (public) 1/this % m (HAC 14.61)
function bnModInverse(m) {
  var ac = m.isEven();
  if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(), v = this.clone();
  var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
  while(u.signum() != 0) {
    while(u.isEven()) {
      u.rShiftTo(1,u);
      if(ac) {
        if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
        a.rShiftTo(1,a);
      }
      else if(!b.isEven()) b.subTo(m,b);
      b.rShiftTo(1,b);
    }
    while(v.isEven()) {
      v.rShiftTo(1,v);
      if(ac) {
        if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
        c.rShiftTo(1,c);
      }
      else if(!d.isEven()) d.subTo(m,d);
      d.rShiftTo(1,d);
    }
    if(u.compareTo(v) >= 0) {
      u.subTo(v,u);
      if(ac) a.subTo(c,a);
      b.subTo(d,b);
    }
    else {
      v.subTo(u,v);
      if(ac) c.subTo(a,c);
      d.subTo(b,d);
    }
  }
  if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if(d.compareTo(m) >= 0) return d.subtract(m);
  if(d.signum() < 0) d.addTo(m,d); else return d;
  if(d.signum() < 0) return d.add(m); else return d;
}

var lowprimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997];
var lplim = (1<<26)/lowprimes[lowprimes.length-1];

// (public) test primality with certainty >= 1-.5^t
function bnIsProbablePrime(t) {
  var i, x = this.abs();
  if(x.t == 1 && x[0] <= lowprimes[lowprimes.length-1]) {
    for(i = 0; i < lowprimes.length; ++i)
      if(x[0] == lowprimes[i]) return true;
    return false;
  }
  if(x.isEven()) return false;
  i = 1;
  while(i < lowprimes.length) {
    var m = lowprimes[i], j = i+1;
    while(j < lowprimes.length && m < lplim) m *= lowprimes[j++];
    m = x.modInt(m);
    while(i < j) if(m%lowprimes[i++] == 0) return false;
  }
  return x.millerRabin(t);
}

// (protected) true if probably prime (HAC 4.24, Miller-Rabin)
function bnpMillerRabin(t) {
  var n1 = this.subtract(BigInteger.ONE);
  var k = n1.getLowestSetBit();
  if(k <= 0) return false;
  var r = n1.shiftRight(k);
  t = (t+1)>>1;
  if(t > lowprimes.length) t = lowprimes.length;
  var a = nbi();
  for(var i = 0; i < t; ++i) {
    //Pick bases at random, instead of starting at 2
    a.fromInt(lowprimes[Math.floor(Math.random()*lowprimes.length)]);
    var y = a.modPow(r,this);
    if(y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
      var j = 1;
      while(j++ < k && y.compareTo(n1) != 0) {
        y = y.modPowInt(2,this);
        if(y.compareTo(BigInteger.ONE) == 0) return false;
      }
      if(y.compareTo(n1) != 0) return false;
    }
  }
  return true;
}

// protected
BigInteger.prototype.chunkSize = bnpChunkSize;
BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.fromRadix = bnpFromRadix;
BigInteger.prototype.fromNumber = bnpFromNumber;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
BigInteger.prototype.changeBit = bnpChangeBit;
BigInteger.prototype.addTo = bnpAddTo;
BigInteger.prototype.dMultiply = bnpDMultiply;
BigInteger.prototype.dAddOffset = bnpDAddOffset;
BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
BigInteger.prototype.modInt = bnpModInt;
BigInteger.prototype.millerRabin = bnpMillerRabin;

// public
BigInteger.prototype.clone = bnClone;
BigInteger.prototype.intValue = bnIntValue;
BigInteger.prototype.byteValue = bnByteValue;
BigInteger.prototype.shortValue = bnShortValue;
BigInteger.prototype.signum = bnSigNum;
BigInteger.prototype.toByteArray = bnToByteArray;
BigInteger.prototype.equals = bnEquals;
BigInteger.prototype.min = bnMin;
BigInteger.prototype.max = bnMax;
BigInteger.prototype.and = bnAnd;
BigInteger.prototype.or = bnOr;
BigInteger.prototype.xor = bnXor;
BigInteger.prototype.andNot = bnAndNot;
BigInteger.prototype.not = bnNot;
BigInteger.prototype.shiftLeft = bnShiftLeft;
BigInteger.prototype.shiftRight = bnShiftRight;
BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
BigInteger.prototype.bitCount = bnBitCount;
BigInteger.prototype.testBit = bnTestBit;
BigInteger.prototype.setBit = bnSetBit;
BigInteger.prototype.clearBit = bnClearBit;
BigInteger.prototype.flipBit = bnFlipBit;
BigInteger.prototype.add = bnAdd;
BigInteger.prototype.subtract = bnSubtract;
BigInteger.prototype.multiply = bnMultiply;
BigInteger.prototype.divide = bnDivide;
BigInteger.prototype.remainder = bnRemainder;
BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
BigInteger.prototype.modPow = bnModPow;
BigInteger.prototype.modInverse = bnModInverse;
BigInteger.prototype.pow = bnPow;
BigInteger.prototype.gcd = bnGCD;
BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

// JSBN-specific extension
BigInteger.prototype.square = bnSquare;

// BigInteger interfaces not implemented in jsbn:

// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

/*
 *  jssha256 version 0.1  -  Copyright 2006 B. Poettering
 *
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 *  02111-1307 USA
 */

/*
 * http://point-at-infinity.org/jssha256/
 *
 * This is a JavaScript implementation of the SHA256 secure hash function
 * and the HMAC-SHA256 message authentication code (MAC).
 *
 * The routines' well-functioning has been verified with the test vectors 
 * given in FIPS-180-2, Appendix B and IETF RFC 4231. The HMAC algorithm 
 * conforms to IETF RFC 2104. 
 *
 * The following code example computes the hash value of the string "abc".
 *
 *    SHA256_init();
 *    SHA256_write("abc");
 *    digest = SHA256_finalize();  
 *    digest_hex = array_to_hex_string(digest);
 * 
 * Get the same result by calling the shortcut function SHA256_hash:
 * 
 *    digest_hex = SHA256_hash("abc");
 * 
 * In the following example the calculation of the HMAC of the string "abc" 
 * using the key "secret key" is shown:
 * 
 *    HMAC_SHA256_init("secret key");
 *    HMAC_SHA256_write("abc");
 *    mac = HMAC_SHA256_finalize();
 *    mac_hex = array_to_hex_string(mac);
 *
 * Again, the same can be done more conveniently:
 * 
 *    mac_hex = HMAC_SHA256_MAC("secret key", "abc");
 *
 * Note that the internal state of the hash function is held in global
 * variables. Therefore one hash value calculation has to be completed 
 * before the next is begun. The same applies the the HMAC routines.
 *
 * Report bugs to: jssha256 AT point-at-infinity.org
 *
 */

/******************************************************************************/

/* Two all purpose helper functions follow */

/* string_to_array: convert a string to a character (byte) array */

function string_to_array(str) {
  var len = str.length;
  var res = new Array(len);
  for(var i = 0; i < len; i++)
    res[i] = str.charCodeAt(i);
  return res;
}

/* array_to_hex_string: convert a byte array to a hexadecimal string */

function array_to_hex_string(ary) {
  var res = "";
  for(var i = 0; i < ary.length; i++)
    res += SHA256_hexchars[ary[i] >> 4] + SHA256_hexchars[ary[i] & 0x0f];
  return res;
}

/******************************************************************************/

/* The following are the SHA256 routines */

/* 
   SHA256_init: initialize the internal state of the hash function. Call this
   function before calling the SHA256_write function.
*/

 var SHA256_buf = new Array();
  var SHA256_len = 0;
var SHA256_H = new Array();

SHA256_init = function SHA256_init() {	
  SHA256_H = new Array(0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19);
	
  SHA256_buf = new Array();
  SHA256_len = 0;
}

/*
   SHA256_write: add a message fragment to the hash function's internal state. 
   'msg' may be given as string or as byte array and may have arbitrary length.

*/

function SHA256_write(msg) {	
  if (typeof(msg) == "string")
    SHA256_buf = SHA256_buf.concat(string_to_array(msg));
  else
    SHA256_buf = SHA256_buf.concat(msg);
                    
  for(var i = 0; i + 64 <= SHA256_buf.length; i += 64)
    SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf.slice(i, i + 64));
        
  SHA256_buf = SHA256_buf.slice(i);
        
  SHA256_len += msg.length;
}

/*
   SHA256_finalize: finalize the hash value calculation. Call this function
   after the last call to SHA256_write. An array of 32 bytes (= 256 bits) 
   is returned.
*/

function SHA256_finalize() {
  SHA256_buf[SHA256_buf.length] = 0x80;

  if (SHA256_buf.length > 64 - 8) {
    for(var i = SHA256_buf.length; i < 64; i++)
      SHA256_buf[i] = 0;
    SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf);
    SHA256_buf.length = 0;
  }

  for(var i = SHA256_buf.length; i < 64 - 5; i++)
    SHA256_buf[i] = 0;
  SHA256_buf[59] = (SHA256_len >>> 29) & 0xff;
  SHA256_buf[60] = (SHA256_len >>> 21) & 0xff;
  SHA256_buf[61] = (SHA256_len >>> 13) & 0xff;
  SHA256_buf[62] = (SHA256_len >>> 5) & 0xff;
  SHA256_buf[63] = (SHA256_len << 3) & 0xff;
  SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf);

  var res = new Array(32);
  for(var i = 0; i < 8; i++) {
    res[4 * i + 0] = SHA256_H[i] >>> 24;
    res[4 * i + 1] = (SHA256_H[i] >> 16) & 0xff;
    res[4 * i + 2] = (SHA256_H[i] >> 8) & 0xff;
    res[4 * i + 3] = SHA256_H[i] & 0xff;
  }

  delete SHA256_H;
  delete SHA256_buf;
  delete SHA256_len;
  
  return res;
}

/*
   SHA256_hash: calculate the hash value of the string or byte array 'msg' 
   and return it as hexadecimal string. This shortcut function may be more 
   convenient than calling SHA256_init, SHA256_write, SHA256_finalize 
   and array_to_hex_string explicitly.
*/

function SHA256_hash(msg, no_hex) {
  var res;
  SHA256_init();
   
  SHA256_write(msg);
  
  res = SHA256_finalize();
    
  if (no_hex) {
	  return res;
  }
  
  return array_to_hex_string(res);
}

/******************************************************************************/

/* The following are the HMAC-SHA256 routines */

/*
   HMAC_SHA256_init: initialize the MAC's internal state. The MAC key 'key'
   may be given as string or as byte array and may have arbitrary length.
*/

function HMAC_SHA256_init(key) {
  if (typeof(key) == "string")
    HMAC_SHA256_key = string_to_array(key);
  else
    HMAC_SHA256_key = new Array().concat(key);

  if (HMAC_SHA256_key.length > 64) {
    SHA256_init();
    SHA256_write(HMAC_SHA256_key);
    HMAC_SHA256_key = SHA256_finalize();
  }

  for(var i = HMAC_SHA256_key.length; i < 64; i++)
    HMAC_SHA256_key[i] = 0;
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] ^=  0x36;
  SHA256_init();
  SHA256_write(HMAC_SHA256_key);
}

/*
   HMAC_SHA256_write: process a message fragment. 'msg' may be given as 
   string or as byte array and may have arbitrary length.
*/

function HMAC_SHA256_write(msg) {
  SHA256_write(msg);
}

/*
   HMAC_SHA256_finalize: finalize the HMAC calculation. An array of 32 bytes
   (= 256 bits) is returned.
*/

function HMAC_SHA256_finalize() {
  var md = SHA256_finalize();
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] ^= 0x36 ^ 0x5c;
  SHA256_init();
  SHA256_write(HMAC_SHA256_key);
  SHA256_write(md);
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] = 0;
  delete HMAC_SHA256_key;
  return SHA256_finalize();
}

/*
   HMAC_SHA256_MAC: calculate the HMAC value of message 'msg' under key 'key'
   (both may be of type string or byte array); return the MAC as hexadecimal 
   string. This shortcut function may be more convenient than calling 
   HMAC_SHA256_init, HMAC_SHA256_write, HMAC_SHA256_finalize and 
   array_to_hex_string explicitly.
*/

function HMAC_SHA256_MAC(key, msg) {
  var res;
  HMAC_SHA256_init(key);
  HMAC_SHA256_write(msg);
  res = HMAC_SHA256_finalize();
  return array_to_hex_string(res);
}

/******************************************************************************/

/* The following lookup tables and functions are for internal use only! */

SHA256_hexchars = new Array('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 
  'a', 'b', 'c', 'd', 'e', 'f');

SHA256_K = new Array(
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 
);

function SHA256_sigma0(x) {
  return ((x >>> 7) | (x << 25)) ^ ((x >>> 18) | (x << 14)) ^ (x >>> 3);
}

function SHA256_sigma1(x) {
  return ((x >>> 17) | (x << 15)) ^ ((x >>> 19) | (x << 13)) ^ (x >>> 10);
}

function SHA256_Sigma0(x) {
  return ((x >>> 2) | (x << 30)) ^ ((x >>> 13) | (x << 19)) ^ 
    ((x >>> 22) | (x << 10));
}

function SHA256_Sigma1(x) {
  return ((x >>> 6) | (x << 26)) ^ ((x >>> 11) | (x << 21)) ^ 
    ((x >>> 25) | (x << 7));
}

function SHA256_Ch(x, y, z) {
  return z ^ (x & (y ^ z));
}

function SHA256_Maj(x, y, z) {
  return (x & y) ^ (z & (x ^ y));
}

function SHA256_Hash_Word_Block(H, W) {	
  for(var i = 16; i < 64; i++)
    W[i] = (SHA256_sigma1(W[i - 2]) +  W[i - 7] + 
      SHA256_sigma0(W[i - 15]) + W[i - 16]) & 0xffffffff;
  var state = new Array().concat(H);
    
  for(var i = 0; i < 64; i++) {
    var T1 = state[7] + SHA256_Sigma1(state[4]) + 
      SHA256_Ch(state[4], state[5], state[6]) + SHA256_K[i] + W[i];
    var T2 = SHA256_Sigma0(state[0]) + SHA256_Maj(state[0], state[1], state[2]);
    state.pop();
    state.unshift((T1 + T2) & 0xffffffff);
    state[4] = (state[4] + T1) & 0xffffffff;
  }
    
  for(var i = 0; i < 8; i++)
    H[i] = (H[i] + state[i]) & 0xffffffff;
}

function SHA256_Hash_Byte_Block(H, w) {	
  var W = new Array(16);
  for(var i = 0; i < 16; i++)
    W[i] = w[4 * i + 0] << 24 | w[4 * i + 1] << 16 | 
      w[4 * i + 2] << 8 | w[4 * i + 3];
      
  SHA256_Hash_Word_Block(H, W);
}

(function(){var DEFAULT_NODE = "jnxt.org";

var _hash = {
		init: SHA256_init,
		update: SHA256_write,
		getBytes: SHA256_finalize
	};

function byteArrayToBigInteger(byteArray, startIndex) {
		var value = new BigInteger("0", 10);
		var temp1, temp2;
		for (var i = byteArray.length - 1; i >= 0; i--) {
			temp1 = value.multiply(new BigInteger("256", 10));
			temp2 = temp1.add(new BigInteger(byteArray[i].toString(10), 10));
			value = temp2;
		}

		return value;
	}

function simpleHash(message) {
		_hash.init();
		_hash.update(message);
		return _hash.getBytes();
	}


	 function getPublicKey(secretPhrase) {
		
			var secretPhraseBytes = converters.stringToByteArray(secretPhrase);
			var digest = simpleHash(secretPhraseBytes);
			return curve25519.keygen(digest).p;
	}


	 function getAccountIdFromPublicKey(publicKey, RSFormat) {
		var hex = converters.hexStringToByteArray(publicKey);

		_hash.init();
		_hash.update(hex);

		var account = _hash.getBytes();

		account = converters.byteArrayToHexString(account);

		var slice = (converters.hexStringToByteArray(account)).slice(0, 8);

		var accountId = byteArrayToBigInteger(slice).toString();

		if (RSFormat) {
			var address = new NxtAddress();

			if (address.set(accountId)) {
				return address.toString();
			} else {
				return "";
			}
		} else {
			return accountId;
		}
	}

	function areByteArraysEqual(bytes1, bytes2) {
		if (bytes1.length !== bytes2.length)
			return false;

		for (var i = 0; i < bytes1.length; ++i) {
			if (bytes1[i] !== bytes2[i])
				return false;
		}

		return true;
	}

	
	 function verifyBytes(signature, message, publicKey) {
		var signatureBytes = signature;
		var messageBytes = message;
		var publicKeyBytes = publicKey;
		var v = signatureBytes.slice(0, 32);
		var h = signatureBytes.slice(32);
		var y = curve25519.verify(v, h, publicKeyBytes);

		var m = simpleHash(messageBytes);

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h2 = _hash.getBytes();

		return areByteArraysEqual(h, h2);
	}

	 function signBytes(message, secretPhrase) {
		var messageBytes = message;
		var secretPhraseBytes = converters.stringToByteArray(secretPhrase);

		var digest = simpleHash(secretPhraseBytes);
		var s = curve25519.keygen(digest).s;

		var m = simpleHash(messageBytes);

		_hash.init();
		_hash.update(m);
		_hash.update(s);
		var x = _hash.getBytes();

		var y = curve25519.keygen(x).p;

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h = _hash.getBytes();

		var v = curve25519.sign(h, x, s);

		return (v.concat(h));
	}

	function toByteArray(long) {
    // we want to represent the input as a 8-bytes array
    var byteArray = [0, 0, 0, 0];

    for ( var index = 0; index < byteArray.length; index ++ ) {
        var byte = long & 0xff;
        byteArray [ index ] = byte;
        long = (long - byte) / 256 ;
    }

    return byteArray;
};

function toIntVal(byteArray) {
    // we want to represent the input as a 8-bytes array
    var intval = 0;

    for ( var index = 0; index < byteArray.length; index ++ ) {
    	var byt = byteArray[index] & 0xFF;
    	var value = byt * Math.pow(256, index);
    	intval += value;
    }

    return intval;
};

function generateToken(websiteString, secretPhrase)
{
		//alert(converters.stringToHexString(websiteString));
		var hexwebsite = converters.stringToHexString(websiteString);
        var website = converters.hexStringToByteArray(hexwebsite);
        var data = [];
        data = website.concat(getPublicKey(secretPhrase));
        var unix = Math.round(+new Date()/1000);
        var timestamp = unix-epochNum;
        var timestamparray = toByteArray(timestamp);
        data = data.concat(timestamparray);

        var token = [];
        token = getPublicKey(secretPhrase).concat(timestamparray);

        var sig = signBytes(data, secretPhrase);

        token = token.concat(sig);
        var buf = "";

        for (var ptr = 0; ptr < 100; ptr += 5) {

        	var nbr = [];
        	nbr[0] = token[ptr] & 0xFF;
        	nbr[1] = token[ptr+1] & 0xFF;
        	nbr[2] = token[ptr+2] & 0xFF;
        	nbr[3] = token[ptr+3] & 0xFF;
        	nbr[4] = token[ptr+4] & 0xFF;
        	var number = byteArrayToBigInteger(nbr);

            if (number < 32) {
                buf+="0000000";
            } else if (number < 1024) {
                buf+="000000";
            } else if (number < 32768) {
                buf+="00000";
            } else if (number < 1048576) {
                buf+="0000";
            } else if (number < 33554432) {
                buf+="000";
            } else if (number < 1073741824) {
                buf+="00";
            } else if (number < 34359738368) {
                buf+="0";
            }
            buf +=number.toString(32);

        }
        return buf;

    }

function parseToken(tokenString, website)
{
 		var websiteBytes = converters.stringToByteArray(website);
        var tokenBytes = [];
        var i = 0;
        var j = 0;

        for (; i < tokenString.length; i += 8, j += 5) {

        	var number = new BigInteger(tokenString.substring(i, i+8), 32);
            var part = converters.hexStringToByteArray(number.toRadix(16));

            tokenBytes[j] = part[4];
            tokenBytes[j + 1] = part[3];
            tokenBytes[j + 2] = part[2];
            tokenBytes[j + 3] = part[1];
            tokenBytes[j + 4] = part[0];

        }

        if (i != 160) {
            new Error("tokenString parsed to invalid size");
        }
        var publicKey = [];
        publicKey = tokenBytes.slice(0, 32);
        var timebytes = [tokenBytes[32], tokenBytes[33], tokenBytes[34], tokenBytes[35]];

        var timestamp = toIntVal(timebytes);
        var signature = tokenBytes.slice(36, 100);

        var data = websiteBytes.concat(tokenBytes.slice(0, 36));
       	
        var isValid = verifyBytes(signature, data, publicKey);

        var ret = {};
        ret.isValid = isValid;
        ret.timestamp = timestamp;
        ret.publicKey = converters.byteArrayToHexString(publicKey);

        return ret;

}


function pad(length, val) {
    var array = [];
    for (var i = 0; i < length; i++) {
        array[i] = val;
    }
    return array;
}

function timeago(timestamp)
{
	var fromnow =  currentNxtTime() - timestamp;
		
	var days =  Math.floor(fromnow/86400);
	var hours = Math.floor((fromnow%86400)/3600);
	var minutes = Math.floor((fromnow%3600)/60);
	var seconds = Math.floor(fromnow&60);
	var acc = "";
	if(days != 0 && days != 1) acc = days + " days ago";
	else if(days == 1) acc = " 1 day ago";
	else if(hours != 0 && hours != 1) acc = hours + " hours ago";
	else if(hours == 1) acc = "1 hour ago";
	else if(minutes != 0 && minutes != 1) acc = minutes + " minutes ago";
	else if(minutes == 1) acc = "1 minute ago";
	else if(seconds != 0 && seconds != 1) acc = seconds + " seconds ago";
	else if(seconds == 1) acc = "1 second ago";
	else acc = "just now";
		
	return acc;
}

function esc(str)
{
	return str.replace("&", "&amp").replace("<", "&lt").replace(">", "&gt").replace("\"", "&quot").replace("'", "&#x27;").replace("/", "&#x2F");
}


// 48 -> 57
// 65 -> 90
// 97 -> 122

	/**
	 * Encoders and decoders for base-62 formatted data. Uses the alphabet 0..9 a..z
	 * A..Z, e.g. '0' => 0, 'a' => 10, 'A' => 35 and 'Z' => 61.
	 * 
	 */
	 	var BASE62 = new BigInteger("62");

	  function valueForByte(key) {
	  	var p = key;
		if(p >= 48 && p <= 57)
		{
			return p - 48;
		}
		else if(p >= 65 && p <= 90)
		{
			return p - 65 + 10;
		}
		else if(p >= 97 && p <= 122)
		{
			return p - 97 + 10 + 26;
		}
	    new Error("base62 digit not found");
	    return -1;
	  }

	  /**
	   * Convert a base-62 string known to be a number.
	   * 
	   * @param s
	   * @return
	   */
		function base62Decode(s) {
	    return base62DecodeBytes(converters.stringToByteArray(s));
	  }

	  /**
	   * Convert a base-62 string known to be a number.
	   * 
	   * @param s
	   * @return
	   */
	  	function base62DecodeBytes(bytes) {
	    var res = new BigInteger("0");
	    var multiplier = new BigInteger("1");

	    for (var i = bytes.length - 1; i >= 0; i--) {
	      res = res.add(multiplier.multiply(new BigInteger(valueForByte(bytes[i]).toString())));
	      multiplier = multiplier.multiply(BASE62);
	    }
	    var btr = res.toByteArray();
	    return positiveByteArray(btr);
	  }

function rndstr(len)
{
	var letters = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
	var ret = "";
	var nums = window.crypto.getRandomValues(new Uint32Array(len));

	for(var a=0;a<len;a++)
	{
		ret += letters[nums[a]%letters.length];
	}
	return ret;
}

function generateSecretPhrase()
{
	return rndstr(6) + "_" + rndstr(6) +  "_" + rndstr(6) + "_" + rndstr(6) + "_" + rndstr(6);
}

function encryptSecretPhrase(phrase, key)
{
	var rkey = prepKey(key);
	return CryptoJS.AES.encrypt(phrase, rkey);
}

function decryptSecretPhrase(cipher, key, checksum)
{
	var rkey = prepKey(key);
	var data = CryptoJS.AES.decrypt(cipher, rkey);

	if(converters.byteArrayToHexString(simpleHash(converters.hexStringToByteArray(data.toString()))) == checksum)
	 return converters.hexStringToString(data.toString());
	else return false;
}

function prepKey(key)
{
	var rounds = 1000;
	var digest = key;
	for(var i=0;i<rounds;i++)
	{
		digest = converters.byteArrayToHexString(simpleHash(digest));
	}
	return digest;
}

function newAccount(secretPhrase, key)
{
	var accountData = {};
	accountData["secretPhrase"] = secretPhrase;
	accountData["publicKey"] = converters.byteArrayToHexString(getPublicKey(accountData["secretPhrase"]));
	accountData["accountRS"] = getAccountIdFromPublicKey(accountData["publicKey"], true);
	accountData["key"] = key;
	accountData["cipher"] = encryptSecretPhrase(accountData["secretPhrase"], key).toString();
	accountData["checksum"] = converters.byteArrayToHexString(simpleHash(converters.stringToByteArray(accountData["secretPhrase"])));
	return accountData;
}

function storeAccount(account)
{ 
	var sto = [];
	if(localStorage["accounts"])
	{
		sto = JSON.parse(localStorage["accounts"]);
	}
	var acc = {};
	acc["accountRS"] = account["accountRS"];
	acc["publicKey"] = account["publicKey"];
	acc["cipher"] = account["cipher"];
	acc["checksum"] = account["checksum"];
	sto.push(acc);

	localStorage["accounts"] = JSON.stringify(sto);
}

var epochNum = 1385294400;
var noAccountsMessage = "No Accounts Added";
var accounts;
var pendingAccount;

function popoutOpen()
{
	if(!localStorage.hasOwnProperty("node"))
	{
		localStorage["node"] = DEFAULT_NODE;
		localStorage["isTestnet"] = false;
	}
	if (!localStorage.hasOwnProperty("isAlwaysSend")) {
	    localStorage["isAlwaysSend"] = true;
	}
	// ok lets deal with any popup setup thats needed.
	if(!localStorage["accounts"] || JSON.parse(localStorage["accounts"]).length == 0)
	{
		// no accounts, take us to the accounts tab first..
		$("#popout_tabs a[href='#accounts']").tab("show");
		addAccountOption(noAccountsMessage);
	}
	else
	{
		loadAccounts();
	}

}	

function loadAccounts()
{
	clearAccountOptions();
	var accounts = JSON.parse(localStorage["accounts"]);
	if(accounts && accounts.length > 0)
	{
		for(var a=0;a<accounts.length;a++)
		{
			addAccountOption(accounts[a]["accountRS"]);
		}
	}
	else
	{
		addAccountOption(noAccountsMessage);
	}
}

function addAccountOption(option)
{
	if($("#transact_account").html().indexOf(noAccountsMessage) > -1)
	{
		clearAccountOptions();
	}
	$("#transact_account").append("<option>"+option+"</option>");
	$("#token_account").append("<option>"+option+"</option>");
	$("#message_account").append("<option>"+option+"</option>");
	$("#accounts_account").append("<option>"+option+"</option>");
}

function clearAccountOptions()
{
	$("#transact_account").html("");
	$("#token_account").html("");
	$("#message_account").html("");
	$("#accounts_account").html("");
}

function broadcastTransaction(nd, bytes)
{
	var params = {requestType: "broadcastTransaction", transactionBytes: bytes};
	$.ajax(nd, {
		url: nd,
		data: params,
		type: "POST",
		success: transactionBroadcasted,
		timeout: 2000,
		fail: transactionBroadcasted
	});
}

function transactionBroadcasted(resp, state)
{
	var response = JSON.parse(resp);
	$("#modal_signed").modal("hide");
	$("#modal_quick_sure").modal("hide");
	if(state != "success")
	{
		infoModal("Couldn't reach server");
	}
	if(response.errorCode != undefined)
	{
		$("#modal_tx_response_title").text("Transaction Error");
		$("#modal_tx_response_key_1").text("Error Code");
		$("#modal_tx_response_value_1").text(response.errorCode);
		$("#modal_tx_response_key_2").text("Error Description");
		$("#modal_tx_response_value_2").text(response.errorDescription); 
		$("#modal_tx_response").modal("show");

	}
	if(response.transaction != undefined)
	{
		$("#modal_tx_response_title").text("Transaction Successful");
		$("#modal_tx_response_key_1").text("Transaction Id");
		$("#modal_tx_response_value_1").text(response.transaction);
		$("#modal_tx_response_key_2").text("Full Hash");
		$("#modal_tx_response_value_2").text(response.fullHash);
		$("#modal_tx_response").modal("show");
	}
}

function setBroadcastNode(node, isTestnet, isAlwaysSend)
{
    if (node) {
        localStorage["node"] = node;
    }
	localStorage["isTestnet"] = (isTestnet === true);
	Jay.isTestnet = (isTestnet === true);
	localStorage["isAlwaysSend"] = (isAlwaysSend === true);
}

function getBroadcastNode()
{
	var node = "http://";
	if(localStorage["node"] == undefined)
	{
		node += DEFAULT_NODE;
		localStorage["node"] = DEFAULT_NODE;
	}
	else node += localStorage["node"];
	if(localStorage["isTestnet"] == "true") node += ":6876";
	else node += ":7876";
	return node + "/nxt";
}

function pinHandler(source, pin)
{
	if(source == "accounts_new")
	{
		accountsNewHandler(pin);
	}
	else if(source == "change")
	{
		changePinHandler(pin);
	}
	else if(source == "newpin")
	{
		newPinHandler(pin);
	}
	else if(source == "export")
	{
		exportHandler(pin);
	}
	else if(source == "delete")
	{
		deleteHandler(pin);
	}
	else if(source == "import")
	{
		importHandler(pin);
	}
	else if(source == "token")
	{
		tokenHandler(pin);
	}
	else if(source == "quicksend")
	{
		quicksendHandler(pin);
	}
	else if(source == "review")
	{
		reviewHandler(pin);
	}

}

function accountsNewHandler(pin)
{
	$("#modal_accounts_new").modal("show");
	var account = newAccount(generateSecretPhrase(), pin);
	pendingAccount = account;
	$("#modal_accounts_new_address").text(account["accountRS"]);
	$("#modal_accounts_new_recovery").val(account["secretPhrase"]);
}

function changePinHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	var account = findAccount(address);
	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		$("#modal_basic_info").modal("show");
		$("#modal_basic_info_title").text("Incorrect PIN");
	}
	else
	{
		data = undefined;
		$("#modal_enter_pin").data("source", "newpin");
		$("#modal_enter_pin").data("pin", pin);
		setTimeout(function() {$("#modal_enter_pin").modal("show");}, 600);
	}
}

function newPinHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	var accounts = JSON.parse(localStorage["accounts"]);
	var oldpin = $("#modal_enter_pin").data("pin");
	$("#modal_enter_pin").removeAttr("data-pin");


	for(var a=0;a<accounts.length;a++)
	{
		if(accounts[a]["accountRS"] == address)
		{
			// now lets handle...
			var sec = decryptSecretPhrase(accounts[a]["cipher"], oldpin, accounts[a]["checksum"]).toString();
			var newcipher = encryptSecretPhrase(sec, pin).toString();
			accounts[a]["cipher"] = newcipher;
		}
	}
	localStorage["accounts"] = JSON.stringify(accounts);
	infoModal("PIN Change Successful");
}

function exportHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);
	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		$("#modal_export").modal("show");
		$("#modal_export_address").text(account["accountRS"]);
		$("#modal_export_key").val(data);
		data = undefined;
	}
}

function deleteHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);

	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		$("#modal_delete").modal("show");
		$("#modal_delete_address").text(account["accountRS"]);
		data = undefined;
	}
}

function importHandler(pin)
{
	var secretPhrase = $("#modal_import").data("import");
	$("#modal_import").data("import", "");
	var account = newAccount(secretPhrase, pin);
	storeAccount(account);
	loadAccounts();
	infoModal("Account Successfully Imported");
}

function tokenHandler(pin)
{
	var address = $("#token_account option:selected").text();
	var account = findAccount(address);
	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);
	var websiteString = $("#token_data").val();

	if(secretPhrase === false)
	{
		infoModal("Incorrect PIN");
	}
	else
	{
		var token = generateToken(websiteString, secretPhrase);
		$("#modal_token_box").val(token);
		$("#modal_token").modal("show");
	}
}

function isHex(hex)
{
	for(var a=0;a<hex.length;a++)
	{
		var p = hex.charCodeAt(a)
		if((p < 48) || (p > 57 && p < 65) || (p > 70 && p < 97) || (p > 102))
		{
			return false;
		}
	}
	return true;
}

function startTransact()
{
	var account = $("#transact_account option:selected").val();
	var tx = $("#transact_transaction").val();
	// decide what kind of tx it is
	if(tx.indexOf("NXT-") == 0)
	{
		// nxt addy, quicksend format...
		startQuicksend(account, tx);
	}
	else if(tx.indexOf("TX_") == 0)
	{
		// TRF
		startTRF(account, tx);
	}
	else
	{
		if(isHex(tx))
		{
			// its hex
			if(tx.length == 64)
			{
				startQuicksend(account, tx, true);
			}
			else
			{
				startHex(account, tx);
			}
		}
		else
		{
			infoModal("Transaction Format Unrecognized")
		}
	}
}

function startQuicksend(sender, recipient, pub)
{
	$("#modal_quicksend").modal("show");
	if(pub == undefined || pub == false)
	{
		$("#modal_quicksend_address").val(recipient);
	}
	else if(pub == true)
	{
		var accid = getAccountIdFromPublicKey(recipient, true);
		$("#modal_quicksend_address").val(accid);
	}
	$("#modal_quicksend").data("sender", sender);
	$("#modal_quicksend").data("recipient", recipient);
}

/*255 here..


29 bytes normal tx...
*/

// 0100101234123412341234010000000000000000e1f5050000000000000000
// TX_3YoYmaTiHaxe7ApnLdGR JWnLUnmbB4r9lSsr5pudM

function currentNxtTime()
{
	return Math.floor(Date.now() / 1000) - 1385294400;
}

function nxtTimeBytes()
{
	return converters.int32ToBytes(currentNxtTime());
}

function positiveByteArray(byteArray)
{
	return converters.hexStringToByteArray(converters.byteArrayToHexString(byteArray));
}

function startTRF(sender, trfBytes)
{
	var bytes = base62Decode(trfBytes.substring(3));
	console.log(JSON.stringify(bytes));
	if(bytes[0] == '1')
	{
		bytes = bytes.slice(1);
		if(bytes.length == 31) bytes = bytes.slice(0, 30);

		var collect = [];
		collect = [bytes[0],bytes[1]]; // type ver & subtype
		collect = collect.concat(nxtTimeBytes()); // timestamp
		collect = collect.concat(wordBytes(1440)); // deadline
		var senderPubKey = converters.hexStringToByteArray(findAccount(sender).publicKey);
		collect = collect.concat(senderPubKey);
		collect = collect.concat(bytes.slice(2, 2+8)); // recipient/genesis
		collect = collect.concat(bytes.slice(10, 10+8)); // amount
		collect = collect.concat(bytes.slice(18, 18+8)); // fee
		collect = collect.concat(pad(32, 0)); // reftxhash
		collect = collect.concat(pad(64, 0)); // signature bytes
		collect = collect.concat(bytes.slice(26, 26+4)); // flags
		collect = collect.concat(pad(4, 0)); // EC blockheight
		collect = collect.concat(pad(8, 0)); // EC blockid
		if(bytes.length > 30) collect = collect.concat(bytes.slice(30)); // attachment/appendages
		startHex(converters.byteArrayToHexString(collect));
	}


}

function startHex(hex)
{
	// now we have hex bytes, lets deal with them...
	var bytes = converters.hexStringToByteArray(hex);

	// get important things from this, verify it?..
	extractBytesData(bytes);
}

function clearReview()
{
	setReview(1, "", "");
	setReview(2, "", "");
	setReview(3, "", "");
	setReview(4, "", "");
	setReview(5, "", "");
	setReview(6, "", "");

	$("#tx_desc").html("");
	$("#tx_sender_title").text("");
	$("#tx_fee").text("");
	$("#tx_sender").text("");

	$("#detailtx_loading").hide();
	$("#detailtx_button").hide();
	$("#detailtx_button").unbind("click");
}

function extractBytesData(bytes)
{
	// lets think here.
	// first we take out the version and subversion, and then think from there
	// have about 8 different places to put data, then account for all possible types
	// appendages will have dropdowns with their content and won't take up much room.
	// the 8 zones will need to be really small.
	// type sender amount recip extra for attachment...
	clearReview();
	$("#modal_review_description").attr("disabled", "true");
	$("#modal_review_description").attr("data-content", "");
	$("#modal_review").data("bytes", converters.byteArrayToHexString(bytes));
	var type = bytes[0];
	var subtype = bytes[1] % 16;
	var sender = getAccountIdFromPublicKey(converters.byteArrayToHexString(bytes.slice(8, 8+32)), true);
	var r = new NxtAddress();
	r.set(byteArrayToBigInteger(bytes.slice(40, 48)).toString());
	var recipient = r.toString();
	var amount = byteArrayToBigInteger(bytes.slice(48, 48+8));
	var fee = byteArrayToBigInteger(bytes.slice(56, 56+8));
	var flags = converters.byteArrayToSignedInt32(bytes.slice(160, 160+4));
	rest = [];
	if(bytes.length > 176) rest = bytes.slice(176);
	var msg = [];
	if(type == 0)
	{
		if(subtype == 0)
		{
		    $("#tx_desc").html("Send <b>" + amount / 100000000 + " NXT</b> to <b>" + recipient + "</b>");
		    $("#tx_sender_title").text("Sender");
		    
			typeName = "Ordinary Payment";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			setReview(4, "Amount", amount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length) msg = rest;
		}
	}
	else if(type == 1)
	{
		if(subtype == 0)
		{
		    $("#tx_desc").html("Send message to <b>" + recipient + "</b>");
		    $("#tx_sender_title").text("Sender");

			typeName = "Arbitrary Message";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length) msg = rest;
		}
		else if(subtype == 1) 
		{
			typeName = "Alias Assignment";
			setReview(1, "Type", typeName);
			setReview(2, "Registrar", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(3, "Alias Name", alias);
			setReview(4, "Fee", fee/100000000 + " nxt");
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			if(rest.length > 2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1]))) msg = rest.slice(2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1])));

			$("#tx_desc").html("Create/update alias <b>" + alias + "</b>");
			$("#tx_sender_title").text("Registrar");
		}
		else if(subtype == 2)
		{
			typeName = "Poll Creation"; //  not yet
		}
		else if(subtype == 3) 
		{
			typeName = "Vote Casting"; // not yet
		}
		else if(subtype == 4)
		{
			typeName = "Hub Announcement"; //  what even is this?
		}
		else if(subtype == 5) 
		{
			typeName = "Account Info";
			setReview(1, "Type", typeName);
			setReview(2, "Account", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(3, "Name", alias);
			setReview(4, "Fee", fee/100000000 + " nxt");
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			if(rest.length > 2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1]))) msg = rest.slice(2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1])));

			$("#tx_desc").html("Set <b>" + alias + "</b> as your account's name");
			$("#tx_sender_title").text("Account");
		}
		else if(subtype == 6) 
		{
			typeName = "Alias Sell";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			var target = "";
			if (recipient == "NXT-MRCC-2YLS-8M54-3CMAJ") { setReview(3, "Buyer", "Anyone"); target = "anyone"; }
			else { setReview(3, "Buyer", recipient); target = recipient; }
			setReview(4, "Alias Name", alias);
			var price = byteArrayToBigInteger(rest.slice(2 + rest[1], 10 + rest[1])).toString();
			price = price/100000000;
			setReview(5, "Sell Price", price);
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 10+rest[1]) msg = rest.slice(10+rest[1]);

			$("#tx_desc").html("Sell alias <b>" + alias + "</b> to <b>" + target + "</b> for <b>" + price + " NXT</b>");
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 7) 
		{
			typeName = "Alias Buy";
			setReview(1, "Type", typeName);
			setReview(2, "Buyer", sender);
			setReview(3, "Seller", recipient);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(4, "Alias", alias);
			setReview(5, "Buy Price", amount/100000000 + " nxt");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 2+rest[1]) msg = rest.slice(2+rest[1]);

			$("#tx_desc").html("Buy alias <b>" + alias + "</b> from <b>" + recipient + "</b> for <b>" + amount/100000000 + " NXT</b>");
			$("#tx_sender_title").text("Buyer");
		}
	}
	else if(type == 2)
	{
		if(subtype == 0) 
		{
			typeName = "Asset Issuance";
			setReview(1, "Type", typeName);
			setReview(2, "Issuer", sender);
			var name = converters.byteArrayToString(rest.slice(2,rest[1]+2));
			setReview(3, "Asset Name", name);
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			var newpos = 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]]);
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			var units = byteArrayToBigInteger(rest.slice(newpos, newpos+8));
			var decimals = rest[newpos+8];
			units = units/Math.pow(10, decimals);
			setReview(4, "Units", units);
			setReview(5, "Decimals", decimals);
			setReview(6, "Fee", fee/100000000 + " nxt");

			$("#tx_desc").html("Issue <b>" + units + " units</b> asset <b>" + name + "</b>, with decimal <b>" + decimals + "</b>");
			$("#tx_sender_title").text("Issuer");
		}
		else if(subtype == 1) 
		{
			typeName = "Asset Transfer";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(5, "Amount", amount + " QNT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);

			function assetTransfer_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount/Math.pow(10, data.decimals);
			            $("#tx_desc").html("Transfer <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> to <b>" + recipient + "</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, assetTransfer_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Transfer <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> to <b>" + recipient + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, assetTransfer_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Sender");
		}
		else if(subtype == 2) 
		{
			typeName = "Ask Order Placement";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount", amount + " QNT");
			var price = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(5, "Price", price + " NQT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 25) msg = rest.slice(25);

			function askOrderPlacement_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount / Math.pow(10, data.decimals);
			            price = price / Math.pow(10, 8 - data.decimals);
			            $("#tx_desc").html("Sell <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, askOrderPlacement_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Sell <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> at <b>" + price +" NQT </b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, askOrderPlacement_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 3) 
		{
			typeName = "Bid Order Placement";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount", amount + " QNT");
			var price = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(5, "Price", price + " NQT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 25) msg = rest.slice(25);

			function bidOrderPlacement_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount / Math.pow(10, data.decimals);
			            price = price / Math.pow(10, 8 - data.decimals);
			            $("#tx_desc").html("Buy <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, bidOrderPlacement_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Buy <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> at <b>" + price + " NQT </b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, bidOrderPlacement_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 4) 
		{
			typeName = "Ask Order Cancellation";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Order Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			var quantityQNT, priceNQT;
			function getAskOrder_OnSuccess(data, status, xhr) {
			    try {
			        if (data.hasOwnProperty('asset')) {
			            quantityQNT = data.quantityQNT;
			            priceNQT = data.priceNQT;
			            getDetailTx("getAsset", { "asset": data.asset }, getAskOrderGetAsset_OnSuccess);
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			function getAskOrderGetAsset_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            var quantity = quantityQNT / Math.pow(10, Number(data.decimals));
			            var price = priceNQT / Math.pow(10, 8 - Number(data.decimals));
			            $("#tx_desc").html("Cancel ask order <b>" + order + "</b> - " + "Sell <b>" + quantity + " </b> asset <b>" + esc(data.name) + "</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAskOrder", { "order": order }, getAskOrder_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Cancel ask order <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAskOrder", { "order": order }, getAskOrder_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 5)
		{
			typeName = "Bid Order Cancellation";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Order Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			var quantityQNT, priceNQT;
			function getBidOrder_OnSuccess(data, status, xhr) {
			    try {
			        if (data.hasOwnProperty('asset')) {
			            quantityQNT = Number(data.quantityQNT);
			            priceNQT = Number(data.priceNQT);
			            getDetailTx("getAsset", { "asset": data.asset }, getBidOrderGetAsset_OnSuccess);
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			function getBidOrderGetAsset_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            var quantity = quantityQNT / Math.pow(10, Number(data.decimals));
			            var price = priceNQT / Math.pow(10, 8 - Number(data.decimals));
			            $("#tx_desc").html("Cancel bid order <b>" + order + "</b> - " + "Buy <b>" + quantity + " </b> asset <b>" + esc(data.name) + "</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getBidOrder", { "order": order }, getBidOrder_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Cancel bid order <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getBidOrder", { "order": order }, getBidOrder_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
	}
	else if(type == 3)
	{
		if(subtype == 0) 
		{
			typeName = "Goods Listing";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var name = converters.byteArrayToString(rest.slice(3,rest[1]+2));
			setReview(3, "Good Name", name);
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			var newpos = 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]]);
			var tags = converters.byteArrayToString(rest.slice(newpos+2, newpos+2+bytesWord([rest[newpos],rest[newpos+1]])));
			newpos = newpos+2+bytesWord([rest[newpos],rest[newpos+1]]);
			setReview(4, "Tags", tags);
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			var amount = converters.byteArrayToSignedInt32(rest.slice(newpos, newpos+4));
			var price = byteArrayToBigInteger(rest.slice(newpos+4, newpos+12)).toString();
			setReview(5, "Amount (price)", amount + "(" + price/100000000 + " nxt)");
			setReview(6, "Fee", fee/100000000 + " nxt");
		}
		else if(subtype == 1) 
		{
			typeName = "Goods Delisting";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			function goodDelisting_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            var price = Number(data.priceNQT) / 100000000;
			            $("#tx_desc").html("Delete marketplace product <b>" + order + "</b> : <br/><br/>" + '<table class="table table-striped"><tbody><tr><th style="width:85px"><strong>Product</strong>:</th><td>' + esc(data.name) + '</td></tr><tr><th><strong>Price</strong>:</th><td>' + price + ' NXT</td></tr><tr><th><strong>Quantity</strong>:</th><td>' + data.quantity + '</td></tr></tbody></table>').show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": order }, goodDelisting_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Delete marketplace product <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": order }, goodDelisting_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 2) 
		{
			typeName = "Price Change";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var newprice = byteArrayToBigInteger(rest.slice(1+8, 1+8+8)).toString();
			setReview(4, "New Price", newprice/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8+8) msg = rest.slice(17);

			function dgsPriceChange_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            var price = Number(data.priceNQT) / 100000000;
			            $("#tx_desc").html("Change price to <b>" + newprice / 100000000 + " NXT</b> for marketplace product <b>" + esc(data.name) + " (" + goodid + ")</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsPriceChange_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Change price to <b>" + newprice / 100000000 + " NXT</b> for marketplace product <b>" + goodid + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsPriceChange_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 3) 
		{
			typeName = "Quantity Change";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var chg = converters.byteArrayToSignedInt32(rest.slice(1+8, 1+8+4));
			if(chg < 0) setReview(4, "Decrease By", -chg);
			else setReview(4, "Increase By", chg);
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8+4) msg = rest.slice(13);

			function dgsQuantityChange_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            $("#tx_desc").html("Change quantity to <b>" + chg + "</b> for marketplace product <b>" + esc(data.name) + " (" + goodid + ")</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsQuantityChange_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Change quantity to <b>" + chg + "</b> for marketplace product <b>" + goodid + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsQuantityChange_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 4)
		{
			typeName = "Purchase";
			setReview(1, "Type", typeName);
			setReview(2, "Buyer", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var qnt = byteArrayToBigInteger(rest.slice(1+8, 1+8+4)).toString();
			setReview(4, "Quantity", qnt);
			var price = byteArrayToBigInteger(rest.slice(1+8+4, 1+16+4)).toString();
			setReview(5, "Price", price/100000000 + " nxt");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+16+8) msg = rest.slice(25);

			function dgsPurchase_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            $("#tx_desc").html("Purchase <b>" + qnt + "</b> product <b>" + esc(data.name) + " (" + goodid + ")</b> at <b>" + price / 100000000 + " NXT</b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsPurchase_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Purchase <b>" + qnt + "</b> product <b>" + goodid + "</b> at <b>" + price / 100000000 + " NXT</b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsPurchase_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 5)
		{
			typeName = "Delivery";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var discount = byteArrayToBigInteger(rest.slice(rest.length-8)).toString();
			setReview(4, "Discount", discount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8) msg = rest.slice(9);
		
		}
		else if(subtype == 6) 
		{
			typeName = "Feedback";
			setReview(1, "Type", typeName);
			setReview(2, "User", sender);
			setReview(3, "Seller", recipient);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Item Id", goodid);
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8) msg = rest.slice(9);
		}
		else if(subtype == 7) 
		{
			typeName = "Refund";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Purchase Id", goodid);
			var discount = byteArrayToBigInteger(rest.slice(1+8,1+16)).toString();
			setReview(4, "Refund Amount", discount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+16) msg = rest.slice(17);
		}
	}
	else if(type == 4)
	{
		if(subtype == 0)
		{
			typeName = "Balance Leasing";
			setReview(1, "Type", typeName);
			setReview(2, "Lessor", sender);
			var lease = bytesWord(rest.slice(1,3));
			setReview(3, "Length", lease + " blocks");
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 3) msg = rest.slice(3);

			$("#tx_desc").html("Lease balance to <b>" + recipient + "</b> for <b>" + lease + " blocks</b>");
			$("#tx_sender_title").text("Sender");
		} 
	}
	else if(type == 5)
	{
		if(subtype == 0)
		{
			typeName = "Issue Currency";
		}
		else if(subtype == 1)
		{
			typeName = "Reserve Increase";
			setReview(1, "Type", typeName);
			setReview(2, "Reserver", sender);
			var assetid = converters.byteArrayToString(rest.slice(1, 1+8));
			setReview(3, "Currency Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount per Unit", amount + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);
		}
		else if(subtype == 2)
		{
			typeName = "Reserve Claim";
		}
		else if(subtype == 3)
		{
			typeName = "Currency Transfer";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			var ms = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Currency Id", ms);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(5, "Amount", amount + " QNT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);
		}
		else if(subtype == 4)
		{
			typeName = "Exchange Offer";
		}
		else if(subtype == 5)
		{
			typeName = "Exchange Buy";
		}
		else if(subtype == 6)
		{
			typeName = "Exchange Sell";
		}
		else if(subtype == 7)
		{
			typeName = "Mint Currency";
			setReview(1, "Type", typeName);
			setReview(2, "Minter", sender);
			var assetid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Currency Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(4, "Amount To Mint", amount + " Units");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 16+16+1) msg = rest.slice(33);
		}
		else if(subtype == 8)
		{
			typeName = "Delete Currency";
		}
	}

	$("#tx_fee").text(fee / 100000000);
	$("#tx_sender").text(sender);

	var message = getModifierBit(flags, 0);
	var publicKey = getModifierBit(flags, 2);
	if(message && msg.length)
	{
		$("#modal_review_message").removeAttr("disabled");
		var len = bytesWord([msg[1],msg[2]]);
		var str = converters.byteArrayToString(msg.slice(5,5+len));
		$("#modal_review_message").attr("data-content", str);
		msg = msg.slice(3+len);
	}
	else $("#modal_review_message").attr("disabled", "true");
	if(publicKey && msg.length)
	{
		$("#modal_review_public_key").removeAttr("disabled");
		var str = converters.byteArrayToHexString(msg.slice(1,65));
		$("#modal_review_public_key").attr("data-content", str);
		msg = msg.slice(65);
	}
	else $("#modal_review_public_key").attr("disabled","true");

	// appendages... ugh... and no icons, how will I do this..

	$("#modal_review").modal("show");
}

function getModifierBit(target, position)
{
	return (target >> position)%2;
}

function setReview(number, key, value)
{
	$("#modal_review_key_"+number).text(key);
	$("#modal_review_value_"+number).text(value);
}


function quicksendHandler(pin)
{
	var amount = $("#modal_enter_pin").data("amount");
	$("#modal_enter_pin").removeAttr("data-amount");
	var recipient = $("#modal_enter_pin").data("recipient");
	$("#modal_enter_pin").removeAttr("data-recipient");
	var sender = $("#modal_enter_pin").data("sender");
	$("#modal_enter_pin").removeAttr("data-sender");
	var account = findAccount(sender)

	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);

	if(secretPhrase === false)
	{
		infoModal("Incorrect PIN");
	}
	else
	{
		var quickbytes = createQuicksend(recipient, amount, secretPhrase);
		$("#modal_quick_sure").data("tx", converters.byteArrayToHexString(quickbytes));
		$("#modal_quick_sure_sender").text(sender);
		if(recipient.indexOf("NXT-") == 0)
		{
			$("#modal_quick_sure_recipient").text(recipient);
		}
		else
		{
			$("#modal_quick_sure_recipient").text(getAccountIdFromPublicKey(recipient, true) + " (with Public Key)");
		}
		$("#modal_quick_sure_amount").text(amount + " NXT");
		$("#modal_quick_sure").modal("show");

		// now we open the "are you sure" modal...tomorrow..
	}
}

function createQuicksend(recipient, amount, secretPhrase)
{
	var txbytes = [];
	txbytes.push(0) // type
	txbytes.push(0 + (1 << 4)); // version/type
	txbytes = txbytes.concat(nxtTimeBytes()); // timestmp
	txbytes = txbytes.concat(wordBytes(1440)); // deadline
	txbytes = txbytes.concat(getPublicKey(secretPhrase)); // public Key

	if(recipient.indexOf("NXT-") == 0)
	{
		recipientRS = recipient;
	}
	else
	{
		recipientRS = getAccountIdFromPublicKey(recipient, true);
	}
	var rec = new NxtAddress();
	rec.set(recipientRS);
	var recip = (new BigInteger(rec.account_id())).toByteArray().reverse();
	if(recip.length == 9) recip = recip.slice(0, 8);
	while(recip.length < 8) recip = recip.concat(pad(1, 0));
	txbytes = txbytes.concat(recip);

	var amt = ((new BigInteger(String(parseInt(amount*100000000))))).toByteArray().reverse();
	if(amt.length == 9) amt = amt.slice(0, 8);
	while(amt.length < 8) amt = amt.concat(pad(1, 0));
	txbytes = txbytes.concat(amt); 

	var fee = (converters.int32ToBytes(100000000));
	while(fee.length < 8) fee = fee.concat(pad(1, 0));
	txbytes = txbytes.concat(fee);

	txbytes = txbytes.concat(pad(32, 0)); // ref full hash
	txbytes = txbytes.concat(pad(64, 0)); // signature

	if(recipient.indexOf("NXT-") == 0)
	{
		txbytes = txbytes.concat(pad(16, 0)); // ignore everything else
	}
	else
	{
		txbytes.push(4);
		txbytes = txbytes.concat(pad(3, 0));
		txbytes = txbytes.concat(pad(12, 0));
		txbytes = txbytes.concat([1]);
		txbytes = txbytes.concat(converters.hexStringToByteArray(recipient));
	}

	txbytes = positiveByteArray(txbytes);
	var sig = signBytes(txbytes, secretPhrase);

	signable = txbytes.slice(0, 96);
	signable = signable.concat(sig);
	signable = signable.concat(txbytes.slice(96+64));

	// now we have a full tx...
	return signable;
}

function wordBytes(word)
{
	return [(word%256), Math.floor(word/256)];
}

function bytesWord(bytes)
{
	return bytes[1]*256+bytes[0];
}

function infoModal(message)
{
	$("#modal_basic_info").modal("show");
	$("#modal_basic_info_title").text(message);
}

function reviewHandler(pin)
{
	var bytes = converters.hexStringToByteArray($("#modal_enter_pin").data("bytes"));
	$("#modal_enter_pin").removeAttr("data-bytes");
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);
	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(secretPhrase === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		var sig = signBytes(bytes, secretPhrase);
		var signed = bytes.slice(0,96);
		signed = signed.concat(sig);
		signed = signed.concat(bytes.slice(96+64));
		$("#modal_signed_box").val(converters.byteArrayToHexString(signed));
		$("#modal_signed").modal("show");
	}
}

function verifyToken()
{
	var token = $("#modal_verify_token_token").val();
	var websiteString = $("#token_data").val();
	var resp = parseToken(token, websiteString);

	if(token.length == 160)
	{
		if(resp.isValid)
		{
			$("#modal_verify_token_group").removeClass("has-error");
			$("#modal_verify_token_group").addClass("has-success");
			$("#modal_verify_token_insert").text("(valid)");
		}
		else
		{
			$("#modal_verify_token_group").addClass("has-error");
			$("#modal_verify_token_group").removeClass("has-success");
			$("#modal_verify_token_insert").text("(invalid)");
		}
		$("#modal_verify_token_address").text(getAccountIdFromPublicKey(resp.publicKey, true));
		$("#modal_verify_token_timestamp").text(timeago(resp.timestamp));
	}
	else if(token.length == 0)
	{
		$("#modal_verify_token_group").removeClass("has-error");
		$("#modal_verify_token_group").removeClass("has-success");
		$("#modal_verify_token_insert").text("");	
		$("#modal_verify_token_address").text("N/A");
		$("#modal_verify_token_timestamp").text("N/A");
	}
	else
	{
		$("#modal_verify_token_group").addClass("has-error");
		$("#modal_verify_token_group").removeClass("has-success");
		$("#modal_verify_token_insert").text("(invalid)");	
		$("#modal_verify_token_address").text("Token Length Incorrect");
		$("#modal_verify_token_timestamp").text("N/A");
	}
}


function findAccount(address)
{
	var accounts = JSON.parse(localStorage["accounts"]);
	if(accounts && accounts.length > 0)
	{
		for(var a=0;a<accounts.length;a++)
		{
			if(accounts[a]["accountRS"] == address) return accounts[a];
		}
	}
	return false;
}

function getDetailTx(requestType, parameters, onSuccess) {
    var requestMethod;
    if (localStorage["isTestnet"] == "true") {
        requestMethod = Jay.requestMethods.single;
        Jay.singleNode = Jay.commonTestnetNodes[0];
    }
    else {
        requestMethod = Jay.requestMethods.validate;
    }
    Jay.request(requestType, parameters, onSuccess, getDetailTx_OnFail, requestMethod);
}

function getDetailTx_OnFail(resp) {
    if (resp) {
        try{
            var data = JSON.parse(resp);
            if (data.errorDescription) {
                alert(data.errorDescription + ". Please try again shortly.");
            }
            else {
                alert("Fail to get transaction details. Please try again shortly.");
            }
        }
        catch (err) {
            if (resp.error) {
                alert(resp.error + ". Please try again shortly.");
            }
            else {
                alert("Fail to get transaction details. Please try again shortly.");
            }
        }
    }
    else {
        alert("Fail to get transaction details. Please try again shortly.");
    }
}

function isGetTxDetails() {
    if (localStorage["isAlwaysSend"] == "true") {
        $("#detailtx_loading").show();
        return true;
    }
    else return false;
}

$("document").ready(function() {

	$("#modal_enter_pin").on("show.bs.modal", function(e) {
		$("#modal_enter_pin_input").val("");

		var source = $(e.relatedTarget).data("source");
		if(source === undefined) source = $("#modal_enter_pin").data("source");

		if(source == "accounts_new")
		{
			$("#modal_enter_pin_title").text("Enter PIN for New Account");
		}
		else if(source == "change")
		{
			$("#modal_enter_pin_title").text("Enter Old PIN");
		}
		else if(source == "newpin")
		{
			$("#modal_enter_pin_title").text("Enter New PIN");
		}
		else if(source =="export")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Export");
		}
		else if(source == "delete")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Delete");
		}
		else if(source == "import")
		{
			$("#modal_enter_pin_title").text("Enter PIN for New Account");
		}
		else if(source == "token")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Create Token");
		}
		else if(source == "quicksend")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Quicksend");
		}
		else if(source == "review")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Sign Transaction");
		}
		$("#modal_enter_pin_accept").data("source", source);
	});

	$("#modal_enter_pin_cancel").click(function() {
		$("#modal_enter_pin_input").val("");
	});
	$("#modal_enter_pin_accept").click(function() {
		$(this).modal("hide");
		pinHandler($("#modal_enter_pin_accept").data("source"), $("#modal_enter_pin_input").val());
	})

	$(".modal_enter_pin_number").click(function() {
		$("#modal_enter_pin_input").val($("#modal_enter_pin_input").val() + $(this).data("number"));
	});
	$("#modal_enter_pin_clear").click(function() {
		$("#modal_enter_pin_input").val("");
	})
	$("#modal_enter_pin_back").click(function() {
		$("#modal_enter_pin_input").val($("#modal_enter_pin_input").val().substring(0, $("#modal_enter_pin_input").val().length-1));
	})

	$(".account_selector").change(function(e) {
		var source = $(this).data("source");
		var account = $("#"+source+"_account option:selected").text();

		$(".account_selector option").removeAttr("selected");
		$(".account_selector option:contains("+account+")").prop("selected", "selected");
	});

	$("#modal_accounts_info").on("show.bs.modal", function(e) {
		var source = $(e.relatedTarget).data("source");
		var address = $("#"+source+"_account option:selected").text();
		var account = findAccount(address);

		if(account === false)
		{
			$("#modal_accounts_info_address").val("Account Not Found");
		}
		else
		{
			$("#modal_accounts_info_address").val(account["accountRS"]);
			$("#modal_accounts_info_public_key").val(account["publicKey"]);
		}
	})

	$("#modal_backup").on("show.bs.modal", function(e) {
		if(localStorage["accounts"] && JSON.parse(localStorage["accounts"]).length != 0)
		{
			$("#modal_backup_box").val(localStorage["accounts"]);
		}
		else 
		{
			$("#modal_backup_box").val("No accounts are added.")
		}
	})

	$("#modal_accounts_new_add").click(function() {
		storeAccount(pendingAccount);
		pendingAccount = undefined;
		loadAccounts();
		$("#modal_accounts_new").modal("hide");
		infoModal("Account Successfully Added");
	});
	$("#modal_accounts_new_cancel").click(function() {
		pendingAccount = undefined;
	})

	$("#modal_delete_delete").click(function(e) {
		// actually delete now
		$("#modal_delete").modal("hide");
		var address = $("#accounts_account option:selected").text();
		var data = localStorage["accounts"];
		var accounts = JSON.parse(localStorage["accounts"]);

		for(var a=0;a<accounts.length;a++)
		{
			if(accounts[a]["accountRS"] == address)
			{
				accounts.splice(a, 1);
			}
		}
		localStorage["accounts"] = JSON.stringify(accounts);
		loadAccounts();
		infoModal("Account Deleted");
	});

	$("#modal_import_add").click(function() {
		$("#modal_import").data("import", $("#modal_import_key").val());
		$("#modal_import").modal("hide");
		$("#modal_import_key").val("");
		$("#modal_enter_pin").data("source", "import");
		$("#modal_enter_pin").modal("show");
	})

	$("#token_form").submit(function(e) {
		e.preventDefault();
		$("#modal_enter_pin").data("source", "token");
		$("#modal_enter_pin").modal("show");
	})

	$("#transact_continue").click(function() {
		startTransact();
	})
	$("#transact_form").submit(function() {
		startTransact();
	})

	$("#modal_quicksend_send").click(function() {
		$("#modal_quicksend").modal("hide");
		var amount = $("#modal_quicksend_amount").val();
		$("#modal_quicksend_amount").val("");
		var sender = $("#modal_quicksend").data("sender");
		var recipient = $("#modal_quicksend").data("recipient");
		$("#modal_enter_pin").data("source", "quicksend");
		$("#modal_enter_pin").data("amount", amount);
		$("#modal_enter_pin").data("sender", sender);
		$("#modal_enter_pin").data("recipient", recipient);
		$("#modal_enter_pin").modal("show");
	})

	$("#modal_review_continue").click(function() {
		var bytes = $("#modal_review").data("bytes");
		$("#modal_review").modal("hide");
		$("#modal_enter_pin").data("source", "review");
		$("#modal_enter_pin").data("bytes", bytes);
		$("#modal_enter_pin").modal("show");
	})

	$("#modal_signed_broadcast").click(function() {
		broadcastTransaction(getBroadcastNode(), $("#modal_signed_box").val());
	});

	$("#modal_quick_sure_send").click(function() {
	    broadcastTransaction(getBroadcastNode(), $("#modal_quick_sure").data("tx"));
	})

	$("#modal_verify_token").on("show.bs.modal", function() {
		verifyToken();
	})

	$("#modal_verify_token_token").on("input propertychange", function() {
		verifyToken();
	})

	$("#modal_broadcast").on("show.bs.modal", function() {
		var old = localStorage["node"];
		if (localStorage["isTestnet"] == "true") {
		    old += " (testnet)";
		    $("#modal_broadcast_testnet").prop('checked', true)
		}
		else {
		    old += " (mainnet)";
		    $("#modal_broadcast_testnet").prop('checked', false);
		}
		if (localStorage["isAlwaysSend"] == "true") $("#modal_broadcast_always_send").prop('checked', true);
		else $("#modal_broadcast_always_send").prop('checked', false);
		$("#modal_broadcast_old").text(old);
		$("#modal_broadcast_node").val("");
	})

	$("#modal_broadcast_save").click(function() {
		var node = $("#modal_broadcast_node").val();
		var isTestnet = $("#modal_broadcast_testnet").is(":checked");
		var isAlwaysSend = $("#modal_broadcast_always_send").is(":checked");
		setBroadcastNode(node, isTestnet, isAlwaysSend);
		$("#modal_broadcast").modal("hide");
	})

	$("#popout_tabs a").click(function (e) {
	    var tab = e.target.attributes.href.value;
	    var focus;
	    if (tab == "#transact") focus = "#transact_transaction";
	    else if (tab == "#token") focus = "#token_data";

	    if (focus) {
	        setTimeout(function () { $(focus).focus(); }, 10);
	    }
	})

	$(".modal").on("shown.bs.modal", function (e) {
	    setTimeout(function () { $("#" + e.target.id).find('input:enabled:not([readonly])').first().focus(); }, 10);
	})

	$("#transact_transaction").keypress(function (e) {
	    if (e.which == "13") {
	        e.preventDefault();
	        if ($(this).val()) {
	            $(this).submit();
	        }
	    }
	});

	Jay.nodeScan(function () { });
	if (localStorage["isTestnet"] == "true") Jay.isTestnet = true;
}) 

})();

/*
 * jQuery.ajaxMultiQueue - A queue for multiple concurrent ajax requests
 * (c) 2013 Amir Grozki
 * Dual licensed under the MIT and GPL licenses.
 *
 * Based on jQuery.ajaxQueue
 * (c) 2011 Corey Frang
 *
 * Requires jQuery 1.5+
 */
(function($) {
	$.ajaxMultiQueue = function(n) {
		return new MultiQueue(~~n);
	};

	function MultiQueue(number) {
		var queues, i,
			current = 0;

		if (!queues) {
			queues = new Array(number);

			for (i = 0; i < number; i++) {
				queues[i] = $({});
			}
		}

		function queue(ajaxOpts) {
			var jqXHR,
				dfd = $.Deferred(),
				promise = dfd.promise();

			queues[current].queue(doRequest);
			current = (current + 1) % number;

			function doRequest(next) {
				if (ajaxOpts.currentPage && ajaxOpts.currentPage != NRS.currentPage) {
					next();
				} else if (ajaxOpts.currentSubPage && ajaxOpts.currentSubPage != NRS.currentSubPage) {
					next();
				} else {
					jqXHR = $.ajax(ajaxOpts);

					jqXHR.done(dfd.resolve)
						.fail(dfd.reject)
						.then(next, next);
				}
			}

			return promise;
		};

		return {
			queue: queue
		};
	}

})(jQuery);

var Jay = {};

	Jay.commonNodes = ["69.163.40.132", "jnxt.org","nxt.noip.me","23.88.59.40","162.243.122.251"];
	Jay.commonTestnetNodes = ["localhost"];

	Jay.msTimeout = 1000;

	Jay.requestMethods = {};
	Jay.requestMethods.single = 0;
	Jay.requestMethods.fastest = 1;
	Jay.requestMethods.validate = 2;
	Jay.requestMethods.cautious = 3;
	Jay.requestMethods.default = Jay.requestMethods.fastest;
	Jay.requestMethod = Jay.requestMethods.default;

	Jay.req = $.ajaxMultiQueue(6);

	Jay.singleNode = "";
	Jay.bestNodes = [];
	Jay.isTestnet = false;

	Jay.queue = function(node, parameters, onSuccess, onFailure)
	{
		var obj = {};
		obj.url = Jay.resolveNode(node);
		obj.data = parameters;
		obj.beforeSend = function(jqxhr, settings) {
			jqxhr.node = node;
			jqxhr.parameters = parameters;
		};
		obj.method = 'POST';
		obj.success = onSuccess;
		if(onFailure != undefined) obj.error = onFailure;
		else obj.error = onSuccess;
		obj.timeout = Jay.msTimeout;
		Jay.req.queue(obj);
	}

	Jay.setNode = function(nodeName)
	{
		Jay.singleNode = nodeName;
	}

	Jay.setRequestMethod = function(requestMethod)
	{
		Jay.requestMethod = requestMethod;
	}

	Jay.resolveNode = function(nodeName)
	{
		var name = "http://";
		name += nodeName;
		if(Jay.isTestnet) name += ":6876";
		else name += ":7876";
		name += "/nxt";
		return name;
	}

	Jay.nodeScan = function(complete)
	{
		var counter = 0;
		for(var a=0;a<Jay.commonNodes.length;a++)
		{
			Jay.queue(Jay.commonNodes[a], {"requestType":"getTime"}, function(resp, status, xhr) {
				if(status == "success")
				{
					Jay.bestNodes.push(xhr.node);
				}
				counter++;
				if(counter == Jay.commonNodes.length)
				{
					complete();
				}
			});
		}
	}

	Jay.request = function(requestType, parameters, onSuccess, onFailure, requestMethod)
	{
		if(requestMethod == undefined) requestMethod = Jay.requestMethod;
		parameters["requestType"] = requestType;

		if(requestMethod == Jay.requestMethods.single)
		{
			var useNode = Jay.singleNode;
			Jay.queue(useNode, parameters, onSuccess, onFailure);
		}
		else if(requestMethod == Jay.requestMethods.fastest)
		{
			if(Jay.bestNodes.length == 0)
			{
					Jay.nodeScan(function() {
						Jay.queue(Jay.bestNodes[0], parameters, onSuccess, onFailure);
					});
			}
			else
			{
				Jay.queue(Jay.bestNodes[0], parameters, onSuccess, onFailure);
			}
		}
		else if(requestMethod == Jay.requestMethods.validate)
		{
			var vld = [];
			for(var a=0;a<3;a++)
			{
				Jay.queue(Jay.bestNodes[a], parameters, function(resp, status, xhr) {
				    try {
				        vld.push(JSON.parse(resp));
				    }
				    catch (err) {
				        onFailure({ "error": "Unable to Validate" }, "error", xhr);
				    }
					if(vld.length == 3)
					{
						// compare
						if(Jay.objectCompare(vld[0], vld[1]))
						{
							onSuccess(vld[0], "success", xhr);
						}
						else if(Jay.objectCompare(vld[1], vld[2]))
						{
							onSuccess(vld[1], "success", xhr);
						}
						else if(Jay.objectCompare(vld[0], vld[2]))
						{
							onSuccess(vld[2], "success", xhr);
						}
						else
						{
							onFailure({"error":"Unable to Validate"}, "error", xhr);
						}
					}
				});
			}
		}
	}

	Jay.objectCompare = function(o1, o2, params)
	{
		if(params === undefined)
		{
			// search for all things
			o1.requestProcessingTime = 0;
			o2.requestProcessingTime = 0;
			return objectEquals(o1, o2);
		}
		else
		{
			// compare only the objects in params..
			for(var b=0;b<params.length;b++)
			{
				if(params[b] in o1 && params[b] in o2)
				{
					if(typeof(o1[params[b]]) == Object)
					{
						if(JSON.stringify(o1[params[b]]) != JSON.stringify(o2[params[b]])) return false;
					}
					else
					{
						if(o1[params[b]] != o[params[b]]) return false;
					}
				}
				else return false;
		 	}
			return true;

		}
	}

	function objectEquals(x, y) {
    'use strict';

    if (x === null || x === undefined || y === null || y === undefined) { return x === y; }
    // after this just checking type of one would be enough
    if (x.constructor !== y.constructor) { return false; }
    // if they are functions they should exactly refer to same one
    if (x instanceof Function) { return x === y; }
    if (x === y || x.valueOf() === y.valueOf()) { return true; }
    if (Array.isArray(x) && x.length !== y.length) { return false; }

    // if they are dates, they must had equal valueOf
    if (x instanceof Date) { return false; }

    // if they are strictly equal, they both need to be object at least
    if (!(x instanceof Object)) { return false; }
    if (!(y instanceof Object)) { return false; }

    // recursive object equality check
    var p = Object.keys(x);
    return Object.keys(y).every(function (i) { return p.indexOf(i) !== -1; }) ?
            p.every(function (i) { return objectEquals(x[i], y[i]); }) :
            false;
	}

	Jay.types = {};
	Jay.subtypes = {};

	Jay.oneNxt = 100000000;	
	Jay.types.payment = 0;
	Jay.types.messaging = 1;
	Jay.types.asset = 2;
	Jay.types.marketplace = 3;
	Jay.types.accountControl = 4;
	Jay.types.monetarySystem = 5;

	Jay.subtypes.ordinaryPayment = 0;
	Jay.subtypes.arbitraryMessage = 0;
	Jay.subtypes.aliasAssignment = 1;
	Jay.subtypes.pollCreation = 2;
	Jay.subtypes.voteCasting = 3;
	Jay.subtypes.hubAnnouncement = 4;
	Jay.subtypes.accountInfo = 5;
	Jay.subtypes.aliasSell = 6;
	Jay.subtypes.aliasBuy = 7;
	Jay.subtypes.aliasDelete = 8;
	Jay.subtypes.assetIssuance = 0;
	Jay.subtypes.assetTransfer = 1;
	Jay.subtypes.askOrderPlacement = 2;
	Jay.subtypes.bidOrderPlacement = 3;
	Jay.subtypes.askOrderCancellation = 4;
	Jay.subtypes.bidOrderCancellation = 5;
	Jay.subtypes.goodsListing = 0;
	Jay.subtypes.goodsDelisting = 1;
	Jay.subtypes.priceChange = 2;
	Jay.subtypes.quantityChange = 3;
	Jay.subtypes.purchase = 4;
	Jay.subtypes.delivery = 5;
	Jay.subtypes.feedback = 6;
	Jay.subtypes.refund = 7;
	Jay.subtypes.balanceLeasing = 0;
	Jay.subtypes.currencyIssuance = 0;
	Jay.subtypes.reserveIncrease = 1;
	Jay.subtypes.reserveClaim = 2;
	Jay.subtypes.currencyTransfer = 3;
	Jay.subtypes.exchangeOffer = 4;
	Jay.subtypes.exchangeBuy = 5;
	Jay.subtypes.exchangeSell = 6;
	Jay.subtypes.currencyMinting = 7;
	Jay.subtypes.currencyDeletion = 8;

	Jay.appendages = {};
	Jay.appendages.none = 0;
	Jay.appendages.message = 1;
	Jay.appendages.encryptedMessage = 2;
	Jay.appendages.publicKeyAnnouncement = 4;
	Jay.appendages.encryptedMessageToSelf = 8;
	Jay.appendages.phasedTransaction = 16;


	Jay.transactionVersion = 1;
	Jay.TRFVersion = 1;
	Jay.genesisRS = "NXT-MRCC-2YLS-8M54-3CMAJ";

	Jay.epoch = 1385294400;

	Jay.getNxtTime = function()
	{
		return Math.floor(Date.now() / 1000) - Jay.epoch;
	}


	Jay.pad = function(length, val) 
	{
    	var array = [];
    	for (var i = 0; i < length; i++) 
    	{
        	array[i] = val;
    	}
    	return array;
	}

	Jay.positiveByteArray = function(byteArray)
	{
		return converters.hexStringToByteArray(converters.byteArrayToHexString(byteArray));
	}

	Jay.rsToBytes = function(rs)
	{
		var rec = new NxtAddress();
		rec.set(rs);
		var recip = (new BigInteger(rec.account_id())).toByteArray().reverse();
		if(recip.length == 9) recip = recip.slice(0, 8);
		while(recip.length < 8) recip = recip.concat(Jay.pad(1, 0));
		return recip;
	}

	Jay.secretPhraseToPublicKey = function(secretPhrase) 
	{
		var secretPhraseBytes = converters.stringToByteArray(secretPhrase);
		var digest = simpleHash(secretPhraseBytes);
		return curve25519.keygen(digest).p;
	}

	Jay.publicKeyToAccountId = function(publicKey, RSFormat)
	{
		var hex = converters.hexStringToByteArray(publicKey);

		_hash.init();
		_hash.update(hex);

		var account = _hash.getBytes();

		account = converters.byteArrayToHexString(account);

		var slice = (converters.hexStringToByteArray(account)).slice(0, 8);

		var accountId = byteArrayToBigInteger(slice).toString();

		if (RSFormat) {
			var address = new NxtAddress();

			if (address.set(accountId)) {
				return address.toString();
			} else {
				return "";
			}
		} else {
			return accountId;
		}
	}

	Jay.numberToBytes = function(num)
	{
		var bytes = (new BigInteger((num).toString())).toByteArray().reverse();
		if(bytes.length == 9) bytes = bytes.slice(0, 8);
		while(bytes.length < 8) bytes = bytes.concat(Jay.pad(1, 0));
		return bytes;
	}

	Jay.createTrfBytes = function(type, subtype, recipient, amount, fee, attachment, appendages)
	{
		var trf = [];
		trf.push(Jay.TRFVersion);
		trf.push(type);
		trf.push((subtype) + (Jay.transactionVersion << 4));
		trf = trf.concat(Jay.rsToBytes(recipient));
		trf = trf.concat(Jay.numberToBytes(Math.round(amount*Jay.oneNxt)));
		trf = trf.concat(Jay.numberToBytes(Math.round(fee*Jay.oneNxt)));
		if(appendages == undefined) trf = trf.concat([0,0,0,0]);
		else trf = trf.concat(appendages.flags);
		if(attachment != undefined) trf = trf.concat(attachment);
		if(appendages != undefined) trf = trf.concat(Jay.combineAppendages(appendages));
		return Jay.positiveByteArray(trf);
	}

	Jay.createTrf = function(type, subtype, recipient, amount, fee, attachment, appendages)
	{
		var trfBytes = Jay.createTrfBytes(type, subtype, recipient, amount, fee, attachment, appendages);
		return Jay.finishTrf(trfBytes);
	}

	Jay.bytesToBigInteger = function(bytes)
	{
		var bi = new BigInteger("0");
		for(var a=0; a<bytes.length; a++)
		{
			bi = bi.multiply(new BigInteger("256"));
			//var term = (new BigInteger(bytes[a].toString())).multiply(multiplier);
			bi = bi.add(new BigInteger(bytes[a].toString()));

		}
		return bi;
	}

	Jay.base62_encode = function(bytes) 
	{
		var value = Jay.bytesToBigInteger(bytes);
	    var buf = "";
	    while ((new BigInteger("0")).compareTo(value) < 0) {
	      	var divRem = value.divideAndRemainder(new BigInteger("62"));
	      	var remainder = divRem[1].intValue();
	      
	      	if (remainder < 10) 
	     	{
	        	buf += String.fromCharCode(remainder + '0'.charCodeAt(0));
	      	}
	      	else if (remainder < 10 + 26) 
	     	{
	      		buf += String.fromCharCode(remainder + 'A'.charCodeAt(0) - 10);
	      	} 
	      	else 
	      	{
	        	buf += String.fromCharCode(remainder + 'a'.charCodeAt(0) - 10 - 26);
	      	}
	      
	      	value = divRem[0];
	    }
	    buf = buf.split("").reverse().join("");
	    return buf;
	  }

	Jay.finishTrf = function(trfBytes)
	{
		return "TX_" + Jay.base62_encode(trfBytes);
	}

	Jay.sendMoney = function(recipient, amount, appendages)
	{
		return Jay.createTrf(Jay.types.payment, Jay.subtypes.ordinaryPayment, recipient, amount, 1, undefined, appendages);
	}

	Jay.sendMessage = function(recipient, message, appendages)
	{
		var appendage = Jay.addAppendage(Jay.appendages.message, message, appendages);
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.arbitraryMessage, recipient, 0, 1, undefined, appendage);
	}

	Jay.setAlias = function(alias, data, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length)
		attachment = attachment.concat(converters.stringToByteArray(alias));
		attachment = attachment.concat(Jay.wordBytes(data.length));
		attachment = attachment.concat(converters.stringToByteArray(data));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasAssignment, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.setAccountInfo = function(name, description, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(name.length);
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.accountInfo, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.sellAlias = function(alias, price, recipient, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(price*Jay.oneNxt)));
		if(recipient == undefined || recipient == "anyone" || recipient == "") return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasSell, [0,0,0,0,0,0,0,0], 0, 1, attachment, appendages);
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasSell, recipient, 0, 1, attachment, appendages);
	}

	Jay.buyAlias = function(alias, amount, recipient, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasBuy, recipient, amount, 1, attachment, appendages);
	}

	Jay.deleteAlias = function(alias)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasDelete, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.issueAsset = function(name, description, quantity, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(name.length);
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(quantity*Math.pow(10,decimals))));
		attachment.push(decimals);
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.assetIssuance, Jay.genesisRS, 0, 1000, attachment, appendages);
	}

	Jay.transferAsset = function(recipient, assetId, quantityQNT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));
		attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.assetTransfer, recipient, 0, 1, attachment, appendages);
	}

	Jay.placeAskOrder = function(assetId, quantityQNT, priceNQT, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));

		if(decimals == undefined || typeof(decimals) != "number")
		{
			attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
			attachment = attachment.concat(Jay.numberToBytes(priceNQT));
			appendages = decimals;
		}
		else
		{
			attachment = attachment.concat(Jay.numberToBytes(Math.round(quantityQNT*Math.pow(10, decimals))));
			attachment = attachment.concat(Jay.numberToBytes(Math.round(priceNQT*Math.pow(10, 8-decimals))));
		}
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.askOrderPlacement, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.placeBidOrder = function(assetId, quantityQNT, priceNQT, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));
		
		if(decimals == undefined || typeof(decimals) != "number")
		{
			attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
			attachment = attachment.concat(Jay.numberToBytes(priceNQT));
			appendages = decimals;
		}
		else
		{
			attachment = attachment.concat(Jay.numberToBytes(Math.round(quantityQNT*Math.pow(10, decimals))));
			attachment = attachment.concat(Jay.numberToBytes(Math.round(priceNQT*Math.pow(10, 8-decimals))));
		}
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.bidOrderPlacement, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.cancelAskOrder = function(orderId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(orderId));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.askOrderCancellation, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.cancelBidOrder = function(orderId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(orderId));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.bidOrderCancellation, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsListing = function(name, description, tags, quantity, price, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.wordBytes(name.length));
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		attachment = attachment.concat(Jay.wordBytes(tags.length));
		attachment = attachment.concat(converters.stringToByteArray(tags));
		attachment = attachment.concat(converters.int32ToBytes(quantity));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(price*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.goodsListing, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsDelisting = function(itemId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.goodsDelisting, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsPriceChange = function(itemId, newPrice, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(newPrice*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.priceChange, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsQuantityChange = function(itemId, deltaQuantity, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(converters.int32ToBytes(deltaQuantity));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.quantityChange, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsPurchase = function(itemId, quantity, priceNQT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion)
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(converters.int32ToBytes(quantity));
		attachment = attachment.concat(Jay.numberToBytes(priceNQT));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.purchase, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsDelivery = function(itemId, discount)
	{
		var attachment = [];
	}

	Jay.dgsFeedback = function(itemId, feedback, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		appendages = Jay.addAppendage(Jay.appendages.message, feedback, appendages);
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.feedback, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsRefund = function(purchaseId, refundAmount, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(purchaseId));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(refundAmount*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.refund, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.leaseBalance = function(recipient, duration, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.wordBytes(duration));
		return Jay.createTrf(Jay.types.accountControl, Jay.subtypes.balanceLeasing, recipient, 0, 1, attachment, appendages);
	}

	Jay.currencyReserveIncrease = function(currencyId, amountPerUnit, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Math.round(amountPerUnit*Jay.oneNxt));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.reserveIncrease, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.transferCurrency = function(recipient, currencyId, amountQNT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Jay.numberToBytes(amountQNT));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.currencyTransfer, recipient, 0, 1, attachment, appendages)
	}

	Jay.currencyMint = function(currencyId, nonce, units, counter, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Jay.numberToBytes(nonce));
		attachment = attachment.concat(Jay.numberToBytes(units));
		attachment = attachment.concat(Jay.numberToBytes(counter));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.currencyMinting, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.wordBytes = function(word)
	{
		return [Math.floor(word%256), Math.floor(word/256)];
	}

	Jay.addAppendage = function(newAppendage, newAppendageData, appendages)
	{
		var flags;
		if(appendages != undefined)
		{
			flags = converters.byteArrayToSignedInt32(appendages.flags);
		}
		else 
		{
			appendages = {};
			flags = 0;
		}

		flags += newAppendage;

		if(newAppendage == Jay.appendages.message)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data.push(0);
			data.push(128);
			data = data.concat(converters.stringToByteArray(newAppendageData));
			appendages.message = data;
		}
		/*else if(newAppendage == Jay.appendages.encryptedMessage)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data = data.concat(converters.stringToByteArray(newAppendageData);
			appendages.encryptedMessage = data;
		}*/
		/*else if(newAppendage == Jay.appendages.encryptedMessageToSelf)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data = data.concat(converters.stringToByteArray(newAppendageData);
			appendages.encryptedMessageToSelf = data;
		}*/
		if(newAppendage == Jay.appendages.publicKeyAnnouncement)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(converters.hexStringToByteArray(newAppendageData));
			appendages.publicKeyAnnouncement = data;
		}
		appendages.flags = converters.int32ToBytes(flags);
		return appendages;
	}

	Jay.combineAppendages = function(appendages)
	{
		var data = [];
		if(appendages.message != undefined)
		{
			data = data.concat(appendages.message);
		}		
		if(appendages.encryptedMessage != undefined)
		{
			data = data.concat(appendages.encryptedMessage)
		}
		if(appendages.encryptedMessageToSelf != undefined)
		{
			data = data.concat(appendages.encryptedMessageToSelf)
		}
		if(appendages.publicKeyAnnouncement != undefined)
		{
			data = data.concat(appendages.publicKeyAnnouncement);
		}
		return data;
	}



var _hash = {
		init: SHA256_init,
		update: SHA256_write,
		getBytes: SHA256_finalize
	};

function byteArrayToBigInteger(byteArray, startIndex) {
		var value = new BigInteger("0", 10);
		var temp1, temp2;
		for (var i = byteArray.length - 1; i >= 0; i--) {
			temp1 = value.multiply(new BigInteger("256", 10));
			temp2 = temp1.add(new BigInteger(byteArray[i].toString(10), 10));
			value = temp2;
		}

		return value;
	}

function simpleHash(message) {
		_hash.init();
		_hash.update(message);
		return _hash.getBytes();
	}

var epochNum = 1385294400;
function getPublicKey(secretPhrase)
{
	SHA256_init();
	SHA256_write(converters.stringToByteArray(secretPhrase));
	var ky = converters.byteArrayToHexString(curve25519.keygen(SHA256_finalize()).p);

	return converters.hexStringToByteArray(ky);
}

function toByteArray(long) {
    // we want to represent the input as a 8-bytes array
    var byteArray = [0, 0, 0, 0];

    for ( var index = 0; index < byteArray.length; index ++ ) {
        var byte = long & 0xff;
        byteArray [ index ] = byte;
        long = (long - byte) / 256 ;
    }

    return byteArray;
};

	function toIntVal(byteArray) {
	    // we want to represent the input as a 8-bytes array
	    var intval = 0;

	    for ( var index = 0; index < byteArray.length; index ++ ) {
	    	var byt = byteArray[index] & 0xFF;
	    	var value = byt * Math.pow(256, index);
	    	intval += value;
	    }

	    return intval;
	};

	Jay.signBytes = function(message, secretPhrase) {
		var messageBytes = message;
		var secretPhraseBytes = converters.stringToByteArray(secretPhrase);

		var digest = simpleHash(secretPhraseBytes);
		var s = curve25519.keygen(digest).s;

		var m = simpleHash(messageBytes);
		_hash.init();
		_hash.update(m);
		_hash.update(s);
		var x = _hash.getBytes();

		var y = curve25519.keygen(x).p;

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h = _hash.getBytes();

		var v = curve25519.sign(h, x, s);


		return v.concat(h);
	}

	function areByteArraysEqual(bytes1, bytes2) {
		if (bytes1.length !== bytes2.length)
			return false;

		for (var i = 0; i < bytes1.length; ++i) {
			if (bytes1[i] !== bytes2[i])
				return false;
		}

		return true;
	}

	Jay.verifyBytes = function(signature, message, publicKey) {
		var signatureBytes = signature;
		var messageBytes = message;
		var publicKeyBytes = publicKey;
		var v = signatureBytes.slice(0, 32);
		var h = signatureBytes.slice(32);
		var y = curve25519.verify(v, h, publicKeyBytes);

		var m = simpleHash(messageBytes);

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h2 = _hash.getBytes();

		return areByteArraysEqual(h, h2);
	}

	Jay.createToken = function(websiteString, secretPhrase)
	{
		//alert(converters.stringToHexString(websiteString));
		var hexwebsite = converters.stringToHexString(websiteString);
        var website = converters.hexStringToByteArray(hexwebsite);
        var data = [];
        data = website.concat(getPublicKey(secretPhrase));
        var unix = Math.round(+new Date()/1000);
        var timestamp = unix-epochNum;
        var timestamparray = toByteArray(timestamp);
        data = data.concat(timestamparray);

        var token = [];
        token = getPublicKey(secretPhrase).concat(timestamparray);

        var sig = Jay.signBytes(data, secretPhrase);

        token = token.concat(sig);
        var buf = "";

        for (var ptr = 0; ptr < 100; ptr += 5) {

        	var nbr = [];
        	nbr[0] = token[ptr] & 0xFF;
        	nbr[1] = token[ptr+1] & 0xFF;
        	nbr[2] = token[ptr+2] & 0xFF;
        	nbr[3] = token[ptr+3] & 0xFF;
        	nbr[4] = token[ptr+4] & 0xFF;
        	var number = byteArrayToBigInteger(nbr);

            if (number < 32) {
                buf+="0000000";
            } else if (number < 1024) {
                buf+="000000";
            } else if (number < 32768) {
                buf+="00000";
            } else if (number < 1048576) {
                buf+="0000";
            } else if (number < 33554432) {
                buf+="000";
            } else if (number < 1073741824) {
                buf+="00";
            } else if (number < 34359738368) {
                buf+="0";
            }
            buf +=number.toString(32);

        }
        return buf;

    }

	Jay.parseToken = function(tokenString, website)
	{
 		var websiteBytes = converters.stringToByteArray(website);
        var tokenBytes = [];
        var i = 0;
        var j = 0;

        for (; i < tokenString.length; i += 8, j += 5) {

        	var number = new BigInteger(tokenString.substring(i, i+8), 32);
            var part = converters.hexStringToByteArray(number.toRadix(16));

            tokenBytes[j] = part[4];
            tokenBytes[j + 1] = part[3];
            tokenBytes[j + 2] = part[2];
            tokenBytes[j + 3] = part[1];
            tokenBytes[j + 4] = part[0];
        }

        if (i != 160) {
            new Error("tokenString parsed to invalid size");
        }
        var publicKey = [];
        publicKey = tokenBytes.slice(0, 32);
        var timebytes = [tokenBytes[32], tokenBytes[33], tokenBytes[34], tokenBytes[35]];

        var timestamp = toIntVal(timebytes);
        var signature = tokenBytes.slice(36, 100);

        var data = websiteBytes.concat(tokenBytes.slice(0, 36));
       	
        var isValid = Jay.verifyBytes(signature, data, publicKey);

        var ret = {};
        ret.isValid = isValid;
        ret.timestamp = timestamp;
        ret.publicKey = converters.byteArrayToHexString(publicKey);
        ret.accountRS = Jay.publicKeyToAccountId(ret.publicKey, true);

        return ret;

	}
