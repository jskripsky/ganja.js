/** Ganja.js - Geometric Algebra - Not Just Algebra.
  * @author Enki
  * @link   https://github.com/enkimute/ganja.js
  */

// Documentation below is for implementors. I'll assume you know about Clifford Algebra's, grades, its products, etc ..
// I'll also assume you are familiar with ES6. My style may feel a bith mathematical, advise is to read slow.

(function (name, context, definition) {
  if (typeof module != 'undefined' && module.exports) module.exports = definition();
  else if (typeof define == 'function' && define.amd) define(name, definition);
  else context[name] = definition();
}('Algebra', this, function () {

/** The 3D PGA Algebra class generator.  **/
  return function Algebra(fu) {
    var p=3, q=0, r=1;
  // total number of dimensions.
    var tot = 4;

  // Unless specified, generate a full set of Clifford basis names. We generate them as an array of strings by starting
  // from numbers in binary representation and changing the set bits into their relative position.
  // Basis names are ordered first per grade, then lexically (not cyclic!).
    var basis=[...Array(2**tot)]           // => [undefined, undefined, undefined, undefined, undefined, undefined, undefined, undefined]
              .map((x,xi)=>(((1<<30)+xi).toString(2)).slice(-tot||-1)                                                           // => ["000", "001", "010", "011", "100", "101", "110", "111"]  (index of array in base 2)
              .replace(/./g,(a,ai)=>a=='0'?'':String.fromCharCode(66+ai-(r!=0))))                                               // => ["", "3", "2", "23", "1", "13", "12", "123"] (1 bits replaced with their positions, 0's removed)
              .sort((a,b)=>(a.toString().length==b.toString().length)?(a>b?1:b>a?-1:0):a.toString().length-b.toString().length) // => ["", "1", "2", "3", "12", "13", "23", "123"] (sorted numerically)
              .map(x=>x&&'e'+(x.replace(/./g,x=>('0'+(x.charCodeAt(0)-65)).slice(tot>9?-2:-1) ))||'1')                          // => ["1", "e1", "e2", "e3", "e12", "e13", "e23", "e123"] (converted to commonly used basis names)

  // See if the basis names start from 0 or 1, store grade per component and lowest component per grade.
    var low=basis.length==1?1:basis[1].match(/\d+/g)[0]*1,
        grades=basis.map(x=>x.length-1),
        grade_start=grades.map((a,b,c)=>c[b-1]!=a?b:-1).filter(x=>x+1).concat([basis.length]);

  // String-simplify a concatenation of two basis blades. (and supports custom basis names e.g. e21 instead of e12)
  // This is the function that implements e1e1 = +1/-1/0 and e1e2=-e2e1. The brm function creates the remap dictionary.
    var simplify = (s,p,q,r)=>{
          var sign=1,c,l,t=[],f=true,ss=s.match(/(\d)/g);
          if (!ss) return s;
          s=ss; l=s.length;

          while (f) {
            f=false;
            // implement Ex*Ex = metric.
            for (var i=0; i<l;) {
              if (s[i]===s[i+1]) {
                if ((s[i]-low)>=(p+r))
                  sign*=-1;
                else if ((s[i]-low)<r)
                  sign=0;i+=2; f=true;
              } else t.push(s[i++]);
            }
            // implement Ex*Ey = -Ey*Ex while sorting basis vectors.
            for (var i=0; i<t.length-1; i++)
              if (t[i]>t[i+1]) {
                c=t[i];t[i]=t[i+1];t[i+1]=c;sign*=-1;f=true; break;
              }
            if (f) { s=t;t=[];l=s.length; }
          }
          var ret=(sign==0)?'0':((sign==1)?'':'-')+(t.length?'e'+t.join(''):'1');
          return (brm&&brm[ret]) || (brm&&brm['-'+ret]&&'-'+brm['-'+ret]) || ret;
        },
        brm=(x=>{ var ret={}; for (var i in basis) ret[basis[i]=='1'?'1':simplify(basis[i],p,q,r)] = basis[i]; return ret; })(basis);

  // As an alternative to the string fiddling, one can also bit-fiddle. In this case the basisvectors are represented by integers with 1 bit per generator set.
    var simplify_bits = (A,B,p2)=>{ var n=p2||(p+q+r),t=0,ab=A&B,res=A^B; if (ab&((1<<r)-1)) return [0,0]; while (n--) t^=(A=A>>1); t&=B; t^=ab>>(p+r); t^=t>>16; t^=t>>8; t^=t>>4; return [1-2*(27030>>(t&15)&1),res]; },
        bc = (v)=>{ v=v-((v>>1)& 0x55555555); v=(v&0x33333333)+((v>>2)&0x33333333); var c=((v+(v>>4)&0xF0F0F0F)*0x1010101)>>24; return c };

  // Faster and degenerate-metric-resistant dualization. (a remapping table that maps items into their duals).
    var drm=basis.map((a,i)=>{ return {a:a,i:i} })
                 .sort((a,b)=>a.a.length>b.a.length?1:a.a.length<b.a.length?-1:(+a.a.slice(1).split('').sort().join(''))-(+b.a.slice(1).split('').sort().join('')) )
                 .map(x=>x.i).reverse(),
        drms=drm.map((x,i)=>(x==0||i==0)?1:simplify(basis[x]+basis[i])[0]=='-'?-1:1);

  /// Store the full metric (also for bivectors etc ..)
    var metric = basis.map((x,xi)=>simplify(x+x,p,q,r)|0); metric[0]=1;

  /// Generate multiplication tables for the outer and geometric products.
    var mulTable   = basis.map(x=>basis.map(y=>(x==1)?y:(y==1)?x:simplify(x+y,p,q,r)));

  /// Convert Cayley table to product matrices. The outer product selects the strict sum of the GP (but without metric), the inner product
  /// is the left contraction.
    var gp=basis.map(x=>basis.map(x=>'0')); // mul, geom. prod.
    var cp=gp.map(x=>gp.map(x=>'0')); // ldot (inner/left contraction)
    var cps=gp.map(x=>gp.map(x=>'0')); // dot (symmetric inner)
    var op=gp.map(x=>gp.map(x=>'0')); // wedge (outer prod)

    // mulTable reversed: map from result (w/o sign, one out of 16) to list of all matching/contributing input indices
    var gpo={};
    basis.forEach((x,xi)=>
      basis.forEach((y,yi)=>{
        var n = mulTable[xi][yi].replace(/^-/,'');
        if (!gpo[n]) gpo[n]=[];
        gpo[n].push([xi,yi]);
      })
    );

    // go base by base, calc all products
    basis.forEach((o,oi)=>{
      // iter over all input indices contributing to this base
      gpo[o].forEach(([xi,yi])=>
        // add if grade sum matches current base
        op[oi][xi]=(grades[oi]==grades[xi]+grades[yi])?((mulTable[xi][yi]=='0')?'0':((mulTable[xi][yi][0]!='-')?'':'-')+'b['+yi+']*this['+xi+']'):'0'
      );
      gpo[o].forEach(([xi,yi])=>{
        gp[oi][xi] =((gp[oi][xi]=='0')?'':gp[oi][xi]+'+')   + ((mulTable[xi][yi]=='0')?'0':((mulTable[xi][yi][0]!='-')?'':'-')+'b['+yi+']*this['+xi+']');
        cp[oi][xi] =((cp[oi][xi]=='0')?'':cp[oi][xi]+'+')   + ((grades[oi]==grades[yi]-grades[xi])?gp[oi][xi]:'0');
        cps[oi][xi]=((cps[oi][xi]=='0')?'':cps[oi][xi]+'+') + ((grades[oi]==Math.abs(grades[yi]-grades[xi]))?gp[oi][xi]:'0');
      });
    });

  /// Flat Algebra Multivector Base Class.
    var generator = class MultiVector extends Float32Array {
    /// constructor - create a floating point array with the correct number of coefficients.
      constructor(a) { super(a||basis.length); return this; }

    /// grade selection - return a only the part of the input with the specified grade.
      Grade(grade,res) { res=res||new this.constructor(); for (var i=0,l=res.length; i<l; i++) if (grades[i]==grade) res[i]=this[i]; else res[i]=0; return res; }
      Even(res) { res=res||new this.constructor(); for (var i=0,l=res.length; i<l; i++) if (grades[i]%2==0) res[i]=this[i]; else res[i]=0; return res; }

    /// grade creation - convert array with just one grade to full multivector.
      nVector(grade,...args) { this.set(args,grade_start[grade]); return this; }

    /// Fill in coordinates (accepts sequence of index,value as arguments)
      Coeff() { for (var i=0,l=arguments.length; i<l; i+=2) this[arguments[i]]=arguments[i+1]; return this; }

    /// Negates specific grades (passed in as args)
      Map(res, ...a) { for (var i=0, l=res.length; i<l; i++) res[i] = (~a.indexOf(grades[i]))?-this[i]:this[i]; return res; }

    /// Returns the vector grade only.
      get Vector ()    { return this.slice(grade_start[1],grade_start[2]); };

      toString() { var res=[]; for (var i=0; i<basis.length; i++) if (Math.abs(this[i])>1e-10) res.push(((this[i]==1)&&i?'':((this[i]==-1)&&i)?'-':(this[i].toFixed(10)*1))+(i==0?'':tot==1&&q==1?'i':basis[i].replace('e','e_'))); return res.join('+').replace(/\+-/g,'-')||'0'; }

    /// Reversion, Involutions, Conjugation for any number of grades, component acces shortcuts.
      get Negative (){ var res = new this.constructor(); for (var i=0; i<this.length; i++) res[i]= -this[i]; return res; };
      get Reverse (){ var res = new this.constructor(); for (var i=0; i<this.length; i++) res[i]= this[i]*[1,1,-1,-1][grades[i]%4]; return res; };
      get Involute (){ var res = new this.constructor(); for (var i=0; i<this.length; i++) res[i]= this[i]*[1,-1,1,-1][grades[i]%4]; return res; };
      get Conjugate (){ var res = new this.constructor(); for (var i=0; i<this.length; i++) res[i]= this[i]*[1,-1,-1,1][grades[i]%4]; return res; };

    /// The Dual, Length, non-metric length and normalized getters.
      get Dual (){ if (r) return this.map((x,i,a)=>a[drm[i]]*drms[i]); var res = new this.constructor(); res[res.length-1]=1; return this.Mul(res); };
      get UnDual (){ if (r) return this.map((x,i,a)=>a[drm[i]]*drms[a.length-i-1]); var res = new this.constructor(); res[res.length-1]=1; return this.Div(res); };
      get Length (){ return Math.sqrt(Math.abs(this.Mul(this.Conjugate).s)); };
      get VLength (){ var res = 0; for (var i=0; i<this.length; i++) res += this[i]*this[i]; return Math.sqrt(res); };
      get Normalized (){
          var sq = this.Mul(this.Reverse), [s,t] = [sq[0], sq[15]];
          if (s==0) return this;
          sq[0] = 1/Math.sqrt(s); sq[15] = -t/(2*Math.pow(Math.sqrt(s),3));
          return this.Mul(sq);
      };
    }

  /// Convert symbolic matrices to code. (skipping zero's on dot and wedge matrices).
  /// These all do straightforward string fiddling. If the 'mix' option is set they reference basis components using e.g. '.e1' instead of eg '[3]' .. so that
  /// it will work for elements of subalgebras etc.
    generator.prototype.Add   = new Function('b,res','res=res||new this.constructor();\n'+basis.map((x,xi)=>'res['+xi+']=b['+xi+']+this['+xi+']').join(';\n').replace(/(b|this)\[(.*?)\]/g,(a,b,c)=>a)+';\nreturn res')
    generator.prototype.Scale = new Function('b,res','res=res||new this.constructor();\n'+basis.map((x,xi)=>'res['+xi+']=b*this['+xi+']').join(';\n').replace(/(b|this)\[(.*?)\]/g,(a,b,c)=>a)+';\nreturn res')
    generator.prototype.Sub   = new Function('b,res','res=res||new this.constructor();\n'+basis.map((x,xi)=>'res['+xi+']=this['+xi+']-b['+xi+']').join(';\n').replace(/(b|this)\[(.*?)\]/g,(a,b,c)=>a)+';\nreturn res')
    generator.prototype.Mul   = new Function('b,res','res=res||new this.constructor();\n'+gp.map((r,ri)=>'res['+ri+']='+r.join('+').replace(/\+\-/g,'-').replace(/(\w*?)\[(.*?)\]/g,(a,b,c)=>a).replace(/\+0/g,'')+';').join('\n')+'\nreturn res;');
    generator.prototype.LDot  = new Function('b,res','res=res||new this.constructor();\n'+cp.map((r,ri)=>'res['+ri+']='+r.join('+').replace(/\+\-/g,'-').replace(/\+0/g,'').replace(/(\w*?)\[(.*?)\]/g,(a,b,c)=>a)+';').join('\n')+'\nreturn res;');
    generator.prototype.Dot   = new Function('b,res','res=res||new this.constructor();\n'+cps.map((r,ri)=>'res['+ri+']='+r.join('+').replace(/\+\-/g,'-').replace(/\+0/g,'').replace(/(\w*?)\[(.*?)\]/g,(a,b,c)=>a)+';').join('\n')+'\nreturn res;');
    generator.prototype.Wedge = new Function('b,res','res=res||new this.constructor();\n'+op.map((r,ri)=>'res['+ri+']='+r.join('+').replace(/\+\-/g,'-').replace(/\+0/g,'').replace(/(\w*?)\[(.*?)\]/g,(a,b,c)=>a)+';').join('\n')+'\nreturn res;');
    generator.prototype.Vee   = new Function('b,res',('res=res||new this.constructor();\n'+op.map((r,ri)=>'res['+drm[ri]+']='+drms[ri]+'*('+r.map(x=>x.replace(/\[(.*?)\]/g,function(a,b){return '['+(drm[b|0])+']'+(drms[b|0]>0?"":"*-1")})).join('+').replace(/\+\-/g,'-').replace(/\+0/g,'').replace(/(\w*?)\[(.*?)\]/g,(a,b,c)=>a)+');').join('\n')+'\nreturn res;').replace(/(b\[)|(this\[)/g,a=>a=='b['?'this[':'b['));

  /// Add getter and setters for the basis vectors/bivectors etc ..
    basis.forEach((b,i)=>Object.defineProperty(generator.prototype, i?b:'s', {
      configurable: true, get(){ return this[i] }, set(x){ this[i]=x; }
    }));

  // Generate a new class for our algebra. It extends the javascript typed arrays (default float32 but can be specified in options).
    var res = class Element extends generator {

    // constructor - create a floating point array with the correct number of coefficients.
      constructor(a) { super(a); if (this.upgrade) this.upgrade(); return this; }

    // Grade selection. (implemented by parent class).
      Grade(grade,res) { res=res||new Element(); return super.Grade(grade,res); }

    // Right and Left divide - Defined on the elements, shortcuts to multiplying with the inverse.
      Div  (b,res) { return this.Mul(b.Inverse,res); }
      LDiv (b,res) { return b.Inverse.Mul(this,res); }

    // Bivector split - we handle all real cases, still have to add the complex cases for those exception scenarios.
      Split () {
        var k = Math.floor((p+q+r)/2), OB = this.map(x=>x), B = this.map(x=>x), m = 1;
        var Wi = [...Array(k)].map((r,i)=>{ m = m*(i+1); var Wi = B.Scale(1/m); B = B.Wedge(OB); return Wi; });
        var TDT    = this.Dot(this).s, TWT = this.Wedge(this);
        if (TWT.VLength < 1E-5) return [this]; // bivector was simple.

        var D      = 0.5*Math.sqrt( TDT**2 - TWT.Mul(TWT).s );
        var eigen  = [0.5*TDT + D, 0.5*TDT - D].sort((a,b)=>Math.abs(a)<Math.abs(b)?-1:1);
        Wi = [Element.Scalar(1),...Wi,Element.Scalar(0)];
        var sum = Element.Scalar(0), res = eigen.slice(1).map(v=>{
          var r = Math.floor(k/2), N = Element.Scalar(0), DN = Element.Scalar(0);
          for (var i=0; i<=r; ++i) { N.Add( Wi[2*i+1].Scale(v**(r-i)), N); DN.Add( Wi[2*i].Scale(v**(r-i)), DN); }
          if (DN.VLength == 0) return Element.Scalar(0);
          var ret = N.Div(DN); sum.Add(ret, sum); return ret;
        });
        return [this.Sub(sum),...res]; // Smallest eigvalue becomes B-rest
      }

    // Factorize a motor
      Factorize () {
        var S = this.Grade(2).Split();
        var P = this.Scale(1);
        var R = S.slice(0,S.length-1).map((Si,i)=>{
          var Mi    = Element.Scalar(P.s).Add(Si);
          var scale = Math.sqrt(Mi.Reverse.Mul(Mi).s);
          return Mi.Scale(1/scale);
        });
        R.push( R.reduce((tot,fact)=>tot.Mul(fact.Reverse), Element.Scalar(1)).Mul(P) );
        return R;
      }

    // exp - closed form exp.
      Exp  (taylor = false) {
        if (Math.abs(this[0])<1E-9 && !taylor) {
           // https://www.researchgate.net/publication/360528787_Normalization_Square_Roots_and_the_Exponential_and_Logarithmic_Maps_in_Geometric_Algebras_of_Less_than_6D
           // 0 1 2 3 4 5
           // 5 6 7 8 9 10
           var l = (this[8]*this[8] + this[9]*this[9] + this[10]*this[10]);
           if (l==0) return new Element([1, 0,0,0,0, this[5], this[6], this[7], 0, 0, 0, 0,0,0,0, 0]);
           var u = Math.sqrt(Math.abs(this.Dot(this).s));
           if (Math.abs(u)<1E-5) return this.Add(Element.Scalar(1));

           var v = this.Wedge(this).Scale(-1/(2*u));
           var res2 = Element.Add(Element.Sub(Math.cos(u),v.Scale(Math.sin(u))),Element.Div(Element.Mul((Element.Add(Math.sin(u),v.Scale(Math.cos(u)))),this),(Element.Add(u,v))));
           return res2;
        }
        if (!taylor && Math.abs(this[0])<1E-9) {
          return this.Grade(2).Split().reduce((total,simple)=>{
            var square = simple.Mul(simple).s, len = Math.sqrt(Math.abs(square));
            if (len <= 1E-5) return total.Mul(Element.Scalar(1).Add(simple));
            if (square <  0) return total.Mul(Element.Scalar(Math.cos(len)).Add(simple.Scale(Math.sin(len)/len)) );
            return total.Mul(Element.Scalar(Math.cosh(len)).Add(simple.Scale(Math.sinh(len)/len)) );
          },Element.Scalar(1));
        }
        var res = Element.Scalar(1), y=1, M= this.Scale(1), N=this.Scale(1); for (var x=1; x<15; x++) { res=res.Add(M.Scale(1/y)); M=M.Mul(N); y=y*(x+1); };
        return res;
      }

    // Log - only for up to 3D PGA for now
      Log (compat = false) {
        if (!compat) {
          // https://www.researchgate.net/publication/360528787_Normalization_Square_Roots_and_the_Exponential_and_Logarithmic_Maps_in_Geometric_Algebras_of_Less_than_6D
          if (Math.abs(this.s)>=.99999) return Element.Bivector(this[5],this[6],this[7],0,0,0).Scale(Math.sign(this.s));
          var a = 1/(1 - this[0]*this[0]), b = Math.acos(this[0])*Math.sqrt(a), c = a*this[15]*(1 - this[0]*b);
          return Element.Bivector( c*this[10] + b*this[5], -c*this[9] + b*this[6], c*this[8] + b*this[7], b*this[8], b*this[9], b*this[10] );
        }
      }

    // Helper for efficient inverses. (custom involutions - negates grades in arguments).
      Map () { var res=new Element(); return super.Map(res,...arguments); }

    // Factories - Make it easy to generate vectors, bivectors, etc when using the functional API. None of the examples use this but
    // users that have used other GA libraries will expect these calls. The Coeff() is used internally when translating algebraic literals.
      static Element()   { return new Element([...arguments]); };
      static Coeff()     { return (new Element()).Coeff(...arguments); }
      static Scalar(x)   { return (new Element()).Coeff(0,x); }
      static Vector()    { return (new Element()).nVector(1,...arguments); }
      static Bivector()  { return (new Element()).nVector(2,...arguments); }
      static Trivector() { return (new Element()).nVector(3,...arguments); }
      static nVector(n)  { return (new Element()).nVector(...arguments); }

    // Static operators. The parser will always translate operators to these static calls so that scalars, vectors, matrices and other non-multivectors can also be handled.
    // The static operators typically handle functions and matrices, calling through to element methods for multivectors. They are intended to be flexible and allow as many
    // types of arguments as possible. If performance is a consideration, one should use the generated element methods instead. (which only accept multivector arguments)
      static toEl(x)        { if (x instanceof Function) x=x(); if (!(x instanceof Element)) x=Element.Scalar(x); return x; }

    // Addition and subtraction. Subtraction with only one parameter is negation.
      static Add(a,b,res)   {
      // Resolve expressions passed in.
        while(a.call)a=a(); while(b.call)b=b(); if (a.Add && b.Add) return a.Add(b,res);
      // If either is a string, the result is a string.
        if ((typeof a=='string')||(typeof b=='string')) return a.toString()+b.toString();
      // If only one is an array, add the other element to each of the elements.
        if ((a instanceof Array && !a.Add)^(b instanceof Array && !b.Add)) return (a instanceof Array)?a.map(x=>Element.Add(x,b)):b.map(x=>Element.Add(a,x));
      // If both are equal length arrays, add elements one-by-one
        if ((a instanceof Array)&&(b instanceof Array)&&a.length==b.length) return a.map((x,xi)=>Element.Add(x,b[xi]));
      // If they're both not elements let javascript resolve it.
        if (!(a instanceof Element || b instanceof Element)) return a+b;
      // Here we're left with scalars and multivectors, call through to generated code.
        a=Element.toEl(a); b=Element.toEl(b); return a.Add(b,res);
      }

      static Sub(a,b,res)   {
      // Resolve expressions passed in.
        while(a.call)a=a(); while(b&&b.call) b=b(); if (a.Sub && b && b.Sub) return a.Sub(b,res);
      // If only one is an array, add the other element to each of the elements.
        if (b&&((a instanceof Array)^(b instanceof Array))) return (a instanceof Array)?a.map(x=>Element.Sub(x,b)):b.map(x=>Element.Sub(a,x));
      // If both are equal length arrays, add elements one-by-one
        if (b&&(a instanceof Array)&&(b instanceof Array)&&a.length==b.length) return a.map((x,xi)=>Element.Sub(x,b[xi]));
      // Negation
        if (arguments.length==1) return Element.Mul(a,-1);
      // If none are elements here, let js do it.
        if (!(a instanceof Element || b instanceof Element)) return a-b;
      // Here we're left with scalars and multivectors, call through to generated code.
        a=Element.toEl(a); b=Element.toEl(b); return a.Sub(b,res);
      }

    // The geometric product. (or matrix*matrix, matrix*vector, vector*vector product if called with 1D and 2D arrays)
      static Mul(a,b,res)   {
      // Resolve expressions
        while(a.call&&!a.length)a=a(); while(b.call&&!b.length)b=b(); if (a.Mul && b.Mul) return a.Mul(b,res);
      // still functions -> experimental curry style (dont use this.)
        if (a.call && b.call) return (ai,bi)=>Element.Mul(a(ai),b(bi));
      // scalar mul.
        if (Number.isFinite(a) && b.Scale) return b.Scale(a); else if (Number.isFinite(b) && a.Scale) return a.Scale(b);
      // Handle matrices and vectors.
        if ((a instanceof Array)&&(b instanceof Array)) {
        // vector times vector performs a dot product. (which internally uses the GP on each component)
          if((!(a[0] instanceof Array) || (a[0] instanceof Element)) &&(!(b[0] instanceof Array) || (b[0] instanceof Element))) { var r=tot?Element.Scalar(0):0; a.forEach((x,i)=>r=Element.Add(r,Element.Mul(x,b[i]),r)); return r; }
        // Array times vector
          if(!(b[0] instanceof Array)) return a.map((x,i)=>Element.Mul(a[i],b));
        // Array times Array
          var r=a.map((x,i)=>b[0].map((y,j)=>{ var r=tot?Element.Scalar(0):0; x.forEach((xa,k)=>r=Element.Add(r,Element.Mul(xa,b[k][j]))); return r; }));
        // Return resulting array or scalar if 1 by 1.
          if (r.length==1 && r[0].length==1) return r[0][0]; else return r;
        }
      // Only one is an array multiply each of its elements with the other.
        if ((a instanceof Array)^(b instanceof Array)) return (a instanceof Array)?a.map(x=>Element.Mul(x,b)):b.map(x=>Element.Mul(a,x));
      // Try js multiplication, else call through to geometric product.
        var r=a*b; if (!isNaN(r)) return r;
        a=Element.toEl(a); b=Element.toEl(b); return a.Mul(b,res);
      }

    // The inner product. (default is left contraction).
      static LDot(a,b,res)   {
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); //if (a.LDot) return a.LDot(b,res);
      // Map elements in array
        if (b instanceof Array && !(a instanceof Array)) return b.map(x=>Element.LDot(a,x));
        if (a instanceof Array && !(b instanceof Array)) return a.map(x=>Element.LDot(x,b));
      // js if numbers, else contraction product.
        if (!(a instanceof Element || b instanceof Element)) return a*b;
        a=Element.toEl(a);b=Element.toEl(b); return a.LDot(b,res);
      }

    // The symmetric inner product. (default is left contraction).
      static Dot(a,b,res)   {
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); //if (a.LDot) return a.LDot(b,res);
      // js if numbers, else contraction product.
        if (!(a instanceof Element || b instanceof Element)) return a|b;
        a=Element.toEl(a);b=Element.toEl(b); return a.Dot(b,res);
      }

    // The outer product. (Grassman product - no use of metric)
      static Wedge(a,b,res) {
      // normal behavior for booleans/numbers
        if (typeof a in {boolean:1,number:1} && typeof b in {boolean:1,number:1}) return a^b;
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); if (a.Wedge) return a.Wedge(Element.toEl(b),res);
      // The outer product of two vectors is a matrix .. internally Mul not Wedge !
        if (a instanceof Array && b instanceof Array) return a.map(xa=>b.map(xb=>Element.Mul(xa,xb)));
      // js, else generated wedge product.
        if (!(a instanceof Element || b instanceof Element)) return a*b;
        a=Element.toEl(a);b=Element.toEl(b); return a.Wedge(b,res);
      }

    // The regressive product. (Dual of the outer product of the duals).
      static Vee(a,b,res) {
      // normal behavior for booleans/numbers
        if (typeof a in {boolean:1,number:1} && typeof b in {boolean:1,number:1}) return a&b;
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); if (a.Vee) return a.Vee(Element.toEl(b),res);
      // js, else generated vee product. (shortcut for dual of wedge of duals)
        if (!(a instanceof Element || b instanceof Element)) return 0;
        a=Element.toEl(a);b=Element.toEl(b); return a.Vee(b,res);
      }

    // The sandwich product. Provided for convenience (>>> operator)
      static sw(a,b) {
      // Skip strings/colors
        if (typeof b == "string" || typeof b =="number") return b;
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); if (a.sw) return a.sw(b);
      // Map elements in array
        if (b instanceof Array && !b.Add) return b.map(x=>Element.sw(a,x));
      // Call through. no specific generated code for it so just perform the muls.
        a=Element.toEl(a); b=Element.toEl(b); return a.Mul(b).Mul(a.Reverse);
      }

    // Division - scalars or cal through to element method.
      static Div(a,b,res) {
      // Expressions
        while(a.call)a=a(); while(b.call)b=b();
      // For DDG experiments, I'll include a quick cholesky on matrices here. (vector/matrix)
        if ((a instanceof Array) && (b instanceof Array) && (b[0] instanceof Array)) {
          // factor
          var R = b.flat(), i, j, k, sum, i_n, j_n, n=b[0].length, s=new Array(n), x=new Array(n), yi;
          for (i=0;i<n;i++) { i_n = i*n;
            for (j=0; j<i; j++) { j_n=j*n;
              s[j] = R[i_n+j];
              for (k=0;k<j;k++) s[j] -= s[k]*R[j_n+k];
              if (R[j_n+j] == 0) return null;
              R[i_n+j] = s[j]/R[j_n+j];
            }
            sum = R[i_n+i];
            for (k=0;k<i; k++)  sum -= s[k]*R[i_n+k];
            R[i_n+i] = sum;
          }
          // subst
          for (i=0; i<n; i++) for (x[i]=a[i],j=0;j<=i-1;j++) x[i]-=R[i*n+j]*x[j];
          for (i=n-1; i>=0; i--) for (x[i] /= R[i*n+i], j=i+1; j<n; j++) x[i] -= R[j*n+i]*x[j];
          return x;
        }
      // js or call through to element divide.
        if (!(a instanceof Element || b instanceof Element)) return a/b;
        a=Element.toEl(a);
        if (Number.isFinite(b)) { return a.Scale(1/b,res); }
        b=Element.toEl(b); return a.Div(b,res);
      }

    // Pow - needs obvious extensions for natural powers. (exponentiation by squaring)
      static Pow(a,b,res) {
      // Expressions
        while(a.call)a=a(); while(b.call)b=b(); if (a.Pow) return a.Pow(b,res);
      // Exponentiation.
        if (a===Math.E && b.Exp) return b.Exp();
      // Squaring
        if (b===2) return this.Mul(a,a,res);
      // No elements, call through to js
        if (!(a instanceof Element || b instanceof Element)) return a**b;
      // Inverse
        if (b===-1) return a.Inverse;
      // Call through to element pow.
        a=Element.toEl(a); return a.Pow(b);
      }

    // Handles scalars and calls through to element method.
      static exp(a) {
      // Expressions.
        while(a.call)a=a();
      // If it has an exp callthrough, use it, else call through to math.
        if (a.Exp) return a.Exp();
        return Math.exp(a);
      }

    // Dual, Involute, Reverse, Conjugate, Normalize and length, all direct call through. Conjugate handles matrices.
      static Dual(a)      { if (typeof a=='boolean' || typeof a=='number') return !a; return Element.toEl(a).Dual; };
      static Involute(a)  { return Element.toEl(a).Involute; };
      static Reverse(a)   { return Element.toEl(a).Reverse; };
      static Conjugate(a) { if (a.Conjugate) return a.Conjugate; if (a instanceof Array) return a[0].map((c,ci)=>a.map((r,ri)=>Element.Conjugate(a[ri][ci]))); return Element.toEl(a).Conjugate; }
      static Normalize(a) { return Element.toEl(a).Normalized; };
      static Length(a)    { return Element.toEl(a).Length };

    // Comparison operators always use length. Handle expressions, then js or length comparison
      static eq(a,b)  { if (!(a instanceof Element)||!(b instanceof Element)) return a==b; while(a.call)a=a(); while(b.call)b=b(); for (var i=0; i<a.length; i++) if (a[i]!=b[i]) return false; return true; }
      static neq(a,b) { if (!(a instanceof Element)||!(b instanceof Element)) return a!=b; while(a.call)a=a(); while(b.call)b=b(); for (var i=0; i<a.length; i++) if (a[i]!=b[i]) return true; return false; }
      static lt(a,b)  { while(a.call)a=a(); while(b.call)b=b(); return (a instanceof Element?a.Length:a)<(b instanceof Element?b.Length:b); }
      static gt(a,b)  { while(a.call)a=a(); while(b.call)b=b(); return (a instanceof Element?a.Length:a)>(b instanceof Element?b.Length:b); }
      static lte(a,b) { while(a.call)a=a(); while(b.call)b=b(); return (a instanceof Element?a.Length:a)<=(b instanceof Element?b.Length:b); }
      static gte(a,b) { while(a.call)a=a(); while(b.call)b=b(); return (a instanceof Element?a.Length:a)>=(b instanceof Element?b.Length:b); }

    // Debug output and printing multivectors.
      static describe(x) { if (x===true) console.log(`Basis\n${basis}\nMetric\n${metric.slice(1,1+tot)}\nCayley\n${mulTable.map(x=>(x.map(x=>('           '+x).slice(-2-tot)))).join('\n')}\nMatrix Form:\n`+gp.map(x=>x.map(x=>x.match(/(-*b\[\d+\])/)).map(x=>x&&((x[1].match(/-/)||' ')+String.fromCharCode(65+1*x[1].match(/\d+/)))||' 0')).join('\n')); return {basis:basisg||basis,metric,mulTable,matrix:gp.map(x=>x.map(x=>x.replace(/\*this\[.+\]/,'').replace(/b\[(\d+)\]/,(a,x)=>(metric[x]==-1||metric[x]==0&&grades[x]>1&&(-1)**grades[x]==(metric[basis.indexOf(basis[x].replace('0',''))]||(-1)**grades[x])?'-':'')+basis[x]).replace('--','')))} }

    // Direct sum of algebras - experimental
      static sum(B){
        var A = Element;
        // Get the multiplication tabe and basis.
        var T1 = A.describe().mulTable, T2 = B.describe().mulTable;
        var B1 = A.describe().basis, B2 = B.describe().basis;
        // Get the maximum index of T1, minimum of T2 and rename T2 if needed.
        var max_T1 = B1.filter(x=>x.match(/e/)).map(x=>x.match(/\d/g)).flat().map(x=>x|0).sort((a,b)=>b-a)[0];
        var max_T2 = B2.filter(x=>x.match(/e/)).map(x=>x.match(/\d/g)).flat().map(x=>x|0).sort((a,b)=>b-a)[0];
        var min_T2 = B2.filter(x=>x.match(/e/)).map(x=>x.match(/\d/g)).flat().map(x=>x|0).sort((a,b)=>a-b)[0];
        // remapping ..
        T2 = T2.map(x=>x.map(y=>y.match(/e/)?y.replace(/(\d)/g,(x)=>(x|0)+max_T1):y.replace("1","e"+(1+max_T2+max_T1))));
        B2 = B2.map((y,i)=>i==0?y.replace("1","e"+(1+max_T2+max_T1)):y.replace(/(\d)/g,(x)=>(x|0)+max_T1));
        // Build the new basis and multable..
        var basis = [...B1,...B2];
        var Cayley = T1.map((x,i)=>[...x,...T2[0].map(x=>"0")]).concat(T2.map((x,i)=>[...T1[0].map(x=>"0"),...x]))
        // Build the new algebra.
        var grades = [...B1.map(x=>x=="1"?0:x.length-1),...B2.map((x,i)=>i?x.length-1:0)];
        var a = Algebra({basis,Cayley,grades,tot:Math.log2(B1.length)+Math.log2(B2.length)})
        // And patch up ..
        a.Scalar = function(x) {
          var res = new a();
          for (var i=0; i<res.length; i++) res[i] = basis[i] == Cayley[i][i] ? x:0;
          return res;
        }
        return a;
      }

    // The graphing function supports several modes. It can render 1D functions and 2D functions on canvas, and PGA2D, PGA3D and CGA2D functions using SVG.
    // It handles animation and interactivity.
    //   graph(function(x))     => function of 1 parameter will be called with that parameter from -1 to 1 and graphed on a canvas. Returned values should also be in the [-1 1] range
    //   graph(function(x,y))   => functions of 2 parameters will be called from -1 to 1 on both arguments. Returned values can be 0-1 for greyscale or an array of three RGB values.
    //   graph(array)           => array of algebraic elements (points, lines, circles, segments, texts, colors, ..) is graphed.
    //   graph(function=>array) => same as above, for animation scenario's this function is called each frame.
    // An optional second parameter is an options object { width, height, animate, camera, scale, grid, canvas }
      static graph(f,options) {
      // Store the original input
        if (!f) return; var origf=f;
      // generate default options.
        options=options||{}; options.scale=options.scale||1; options.camera=options.camera||(tot!=4?Element.Scalar(1): ( Element.Bivector(0,0,0,0,0,options.p||0).Exp() ).Mul( Element.Bivector(0,0,0,0,options.h||0,0).Exp()) );
        if (options.conformal && tot==4) var ni = options.ni||this.Coeff(4,1,3,1), no = options.no||this.Coeff(4,0.5,3,-0.5), minus_no = no.Scale(-1);
        var ww=options.width, hh=options.height, cvs=options.canvas, tpcam=new Element([0,0,0,0,0,0,0,0,0,0,0,-5,0,0,1,0]),tpy=this.Coeff(4,1),tp=new Element(),
      // project 3D to 2D. This allows to render 3D and 2D PGA with the same code.
        project=(o)=>{ if (!o) return o; while (o.call) o=o();
//          if (o instanceof Element && o.length == 32) o = new Element([o[0],o[1],o[2],o[3],o[4],o[6],o[7],o[8],o[10],o[11],o[13],o[16],o[17],o[19],o[22],o[26]]);
          // Clip 3D lines so they don't go past infinity.
          if (o instanceof Element && o.length == 16 && o[8]**2+o[9]**2+o[10]**2>0.0001) {
            o = [[options.clip||2,1,0,0],[-(options.clip||2),1,0,0],[options.clip||2,0,1,0],[-(options.clip||2),0,1,0],[options.clip||2,0,0,1],[-(options.clip||2),0,0,1]].map(v=>{
              var r = Element.Vector(...v).Wedge(o); return r[14]?r.Scale(1/r[14], r):undefined;
            }).filter(x=>x && Math.abs(x[13])<= (options.clip||2)+0.001 && Math.abs(x[12]) <= (options.clip||2)+0.001 && Math.abs(x[11]) <= (options.clip||2) + 0.001).slice(0,2);
            return o.map(o=>(tpcam).Vee(options.camera.Mul(o).Mul(options.camera.Conjugate)).Wedge(tpy));
          }
          // Convert 3D planes to polies.
          if (o instanceof Element && o.length == 16 && o.Grade(1).Length>0.01) {
            var m = Element.Add(1, Element.Mul(o.Normalized, Element.Coeff(3,1))).Normalized, e0 = 0;
            o=Element.sw(m,[[-1,-1],[-1,1],[1,1],[-1,-1],[1,1],[1,-1]].map(([x,z])=>Element.Trivector(x*o.Length,e0,z*o.Length,1)));
            return o.map(o=>(tpcam).Vee(options.camera.Mul(o).Mul(options.camera.Conjugate)).Wedge(tpy));
          }
          return (tot==4 && o instanceof Element && o.length==16)?(tpcam).Vee(options.camera.Mul(o).Mul(options.camera.Conjugate)).Wedge(tpy):(o.length==2**tot)?Element.sw(options.camera,o):o;
        };
      // if we get an array or function without parameters, we render c2d or p2d SVG points/lines/circles/etc
        if (!(f instanceof Function) || f.length===0) {
        // Our current cursor, color, animation state and 2D mapping.
          var lx,ly,lr,color,res,anim=false,to2d=(tot==5)?[0, 8, 11, 13, 19, 17, 22, 26]:(tot==3)?[0,1,2,3,4,5,6,7]:[0,7,9,10,13,12,14,15];
        // Make sure we have an array of elements. (if its an object, convert to array with elements and names.)
          if (f instanceof Function) f=f(); if (!(f instanceof Array)) f=[].concat.apply([],Object.keys(f).map((k)=>typeof f[k]=='number'?[f[k]]:[f[k],k]));
        // The build function generates the actual SVG. It will be called everytime the user interacts or the anim flag is set.
          function build(f,or) {
          // Make sure we have an aray.
            if (or && f && f instanceof Function) f=f();
          // Reset position and color for cursor.
            lx=-2;ly=options.conformal?-1.85:1.85;lr=0;color='#444';
          // Create the svg element. (master template string till end of function)
            var svg=new DOMParser().parseFromString(`<SVG viewBox="-2 -${2*(hh/ww||1)} 4 ${4*(hh/ww||1)}" style="width:${ww||512}px; height:${hh||512}px; background-color:#eee; -webkit-user-select:none; -moz-user-select:none; -ms-user-select:none; user-select:none">
            ${// Add a grid (option)
              options.grid?(()=>{
                if (tot==4 && !options.conformal) {
                  const lines3d = (n,from,to,j,l=0, ox=0, oy=0, alpha=1)=>[`<G stroke-opacity="${alpha}" fill-opacity="${alpha}">`,...[...Array(n+1)].map((x,i)=>{
                    var f=from.map((x,i)=>x*(i==3?1:(options.gridSize||1))), t=to.map((x,i)=>x*(i==3?1:(options.gridSize||1))); f[j] = t[j] = (i-(n/2))/(n/2) * (options.gridSize||1);
                    var D3a = Element.Trivector(...f), D2a = project(D3a), D3b = Element.Trivector(...t), D2b = project(D3b);
                    var lx=options.scale*D2a[drm[2]]/D2a[drm[1]]; if (drm[1]==6||drm[1]==14) lx*=-1; var ly=-options.scale*D2a[drm[3]]/D2a[drm[1]];
                    var lx2=options.scale*D2b[drm[2]]/D2b[drm[1]]; if (drm[1]==6||drm[1]==14) lx2*=-1; var ly2=-options.scale*D2b[drm[3]]/D2b[drm[1]];
                    var r = `<line x1="${lx}" y1="${ly}" x2="${lx2}" y2="${ly2}" stroke="black" stroke-width="${i%10==0?0.005:i%5==0?0.002:0.0005}" />`;
                    if (l && i && i!= n) r += `<text text-anchor="middle" font-size="0.04" fill="black" x="${l==1?lx+ox:lx2+ox}" y="${oy+(l==1?ly:ly2)}" >${((from[j]<0?-1:1)*(i-(n/2))/(n/2)*(options.gridSize||1)).toFixed(1)}</text>`
                    return r;
                  }),'</G>'];
                  var front = Element.sw(options.camera,Element.Trivector(1,0,0,0)).Dual.Dot(Element.Vector(0,0,0,1)).s, ff = front>0?1:-1;
                  var left  = Element.sw(options.camera,Element.Trivector(0,0,1,0)).Dual.Dot(Element.Vector(0,0,0,1)).s, ll = left>0?1:-1;
                  var fa = Math.max(0,Math.min(1,5*Math.abs(left))), la = Math.max(0,Math.min(1,5*Math.abs(front)));
                  return [
                    ...lines3d(20,[-1,-1,-1,1],[1,-1,1,1],2,options.labels?ff:0, 0, 0.05),
                    ...lines3d(20,[-1,-1,-1,1],[1,-1,1,1],0,options.labels?ll:0, 0, 0.05),
                    ...lines3d(20,[-1,-1,ll,1],[1,1,ll,1],0,0,0,0,fa),
                    ...lines3d(20,[-1,1,ll,1],[1,-1,ll,1],1,!options.labels?0:(ff!=-1)?1:2, ll*ff*-0.05, 0, fa),
                    ...lines3d(20,[ff,1,-1,1],[ff,-1,1,1],1,!options.labels?0:(ll!=-1)?1:2, ll*ff*0.05, 0, la),
                    ...lines3d(20,[ff,-1,-1,1],[ff,1,1,1],2,0,0,0,la),
                  ].join('');
                }
                const s = options.scale, n = (10/s)|0, cx = options.camera.e02, cy = options.camera.e01, alpha = Math.min(1,(s-0.2)*10); if (options.scale<0.1) return;
                const lines = (n,dir,space,width,color)=>[...Array(2*n+1)].map((x,xi)=>`<line x1="${dir?-10:((xi-n)*space-(tot<4?2*cy:0))*s}" y1="${dir?((xi-n)*space-(tot<4?2*cx:0))*s:-10}" x2="${dir?10:((xi-n)*space-(tot<4?2*cy:0))*s}" y2="${dir?((xi-n)*space-(tot<4?2*cx:0))*s:10}" stroke-width="${width}" stroke="${color}"/>`)
                return [`<G stroke-opacity='${alpha}' fill-opacity='${alpha}'>`,...lines(n*2,0,0.2,0.005,'#DDD'),...lines(n*2,1,0.2,0.005,'#DDD'),...lines(n,0,1,0.005,'#AAA'),...lines(n,1,1,0.005,'#AAA'),...lines(n,0,5,0.005,'#444'),...lines(n,1,5,0.005,'#444')]
                       .concat(options.labels?[...Array(4*n+1)].map((x,xi)=>(xi-n*2==0)?``:`<text text-anchor="middle" font-size="0.05" x="${((xi-n*2)*0.2-(tot<4?2*cy:0))*s}" y="0.06" >${((xi-n*2)*0.2).toFixed(1)}</text>`):[])
                       .concat(options.labels?[...Array(4*n+1)].map((x,xi)=>`<text text-anchor="end" font-size="0.05" y="${((xi-n*2)*0.2-(tot<4?2*cx:0))*s-0.01}" x="-0.01" >${((xi-n*2)*-0.2).toFixed(1)}</text>`):[]).join('')+'</G>';
            })():''}
            ${f.map&&f.map((o,oidx)=>{  if((o==Element.graph && or!==false)||(oidx==0&&options.animate&&or!==false)) { anim=true; requestAnimationFrame(()=>{var r=build(origf,(!res)||(document.body.contains(res))).innerHTML; if (res) res.innerHTML=r; }); if (!options.animate) return; } while (o instanceof Function) o=o(); o=(o instanceof Array)?o.map(project):project(o); if (o===undefined) return;
            // dual option dualizes before render
              if (options.dual && o instanceof Element) o = o.Dual;
            // line segments and polygons
              if (o instanceof Array && o.length>1)  { lx=ly=lr=0; o.forEach((o)=>{while (o.call) o=o(); lx+=options.scale*((drm[1]==6||drm[1]==14)?-1:1)*o[drm[2]]/o[drm[1]];ly+=options.scale*o[drm[3]]/o[drm[1]]});lx/=o.length;ly/=o.length; return o.length>2?`<POLYGON STYLE="pointer-events:none; fill:${color};opacity:0.7" points="${o.map(o=>((drm[1]==6||drm[1]==14)?-1:1)*options.scale*o[drm[2]]/o[drm[1]]+','+(-options.scale)*o[drm[3]]/o[drm[1]]+' ')}"/>`:`<LINE style="pointer-events:none" x1=${options.scale*((drm[1]==6||drm[1]==14)?-1:1)*o[0][drm[2]]/o[0][drm[1]]} y1=${-options.scale*o[0][drm[3]]/o[0][drm[1]]} x2=${options.scale*((drm[1]==6||drm[1]==14)?-1:1)*o[1][drm[2]]/o[1][drm[1]]} y2=${-options.scale*o[1][drm[3]]/o[1][drm[1]]} stroke="${color||'#888'}"/>`; }
            // svg
              if (typeof o =='string' && o[0]=='<') { return o; }
            // Labels
              if (typeof o =='string') { var res2=(o[0]=='_')?'':`<text x="${lx}" y="${-ly}" font-family="Verdana" font-size="${options.fontSize*0.1||0.1}" style="pointer-events:none" fill="${color||'#333'}" transform="rotate(${-lr},0,0)">&nbsp;${o}&nbsp;</text>`; ly-=0.14; return res2; }
            // Colors
              if (typeof o =='number') { color='#'+(o+(1<<25)).toString(16).slice(-6); return ''; };
            // Points
              if (o[to2d[6]]**2        >0.0001) { lx=options.scale*o[drm[2]]/o[drm[1]]; if (drm[1]==6||drm[1]==14) lx*=-1; ly=options.scale*o[drm[3]]/o[drm[1]]; lr=0;  var res2=`<CIRCLE onmousedown="this.parentElement.sel=${oidx}" cx="${lx}" cy="${-ly}" r="${options.pointRadius*0.03||0.03}" fill="${color||'green'}"/>`; ly+=0.05; lx-=0.1; return res2; }
            // Lines
              if (o[to2d[2]]**2+o[to2d[3]]**2>0.0001) { var l=Math.sqrt(o[to2d[2]]**2+o[to2d[3]]**2); o[to2d[2]]/=l; o[to2d[3]]/=l; o[to2d[1]]/=l; lx=0.5; ly=options.scale*((drm[1]==6)?-1:-1)*o[to2d[1]]; lr=-Math.atan2(o[to2d[2]],o[to2d[3]])/Math.PI*180; var res2=`<LINE style="pointer-events:none" x1=-10 y1=${-ly} x2=10 y2=${-ly} stroke="${color||'#888'}" transform="rotate(${-lr},0,0)"/>`; ly+=0.05; return res2; }
            // Vectors
              if (o[to2d[4]]**2+o[to2d[5]]**2>0.0001) { lr=0; ly+=0.05; lx+=0.1; var res2=`<LINE style="pointer-events:none" x1=${lx} y1=${-ly} x2=${lx-o.e02} y2=${-(ly+o.e01)} stroke="${color||'#888'}"/>`; ly=ly+o.e01/4*3-0.05; lx=lx-o.e02/4*3; return res2; }
            }).join()}`,'text/html').body;
          // return the inside of the created svg element.
            return svg.removeChild(svg.firstChild);
          };
        // Create the initial svg and install the mousehandlers.
          res=build(f); res.value=f; res.options=options; res.setAttribute("stroke-width",options.lineWidth*0.005||0.005);
          res.remake = (animate)=>{ options.animate = animate; if (animate) { var r=build(origf,(!res)||(document.body.contains(res))).innerHTML; if (res) res.innerHTML=r; }; return res;};
          //onmousedown="if(evt.target==this)this.sel=undefined"
          var mousex,mousey,cammove=false;
          res.onwheel=(e)=>{ e.preventDefault(); options.scale = Math.min(5,Math.max(0.1,(options.scale||1)-e.deltaY*0.0001)); if (!anim) {var r=build(origf,(!res)||(document.body.contains(res))).innerHTML; if (res) res.innerHTML=r; } }
          res.onmousedown=(e)=>{ if (e.target == res) res.sel=undefined; mousex = e.clientX; mousey = e.clientY; cammove = true;  }
          res.onmousemove=(e)=>{
            if (cammove && tot==4 && !options.conformal) {
              if (!e.buttons) { cammove=false; return; };
              var [dx,dy] = [(options.scale || 1)*(e.clientX - mousex)*3, 3*(options.scale || 1)*(e.clientY - mousey)];
              [mousex,mousey] = [e.clientX,e.clientY];
              if (res.sel !== undefined && f[res.sel].set) {
                 var [cw,ch] = [res.clientWidth, res.clientHeight];
                 var ox = (1/(options.scale || 1)) * ((e.offsetX / cw) - 0.5) * (cw>ch?(cw/ch):1);
                 var oy = (1/(options.scale || 1)) * ((e.offsetY / ch) - 0.5) * (ch>cw?(ch/cw):1);
                 var tb  = Element.sw(options.camera,f[res.sel]);
                 var z = -(tb.e012/tb.e123+5)/5*4; tb.e023 = ox*z*tb.e123; tb.e013 = oy*z*tb.e123;
                 f[res.sel].set(Element.sw(options.camera.Reverse, tb));
                //f[res.sel].set(   Element.sw(Element.sw(options.camera.Reverse,Element.Bivector(-dx/res.clientWidth,dy/res.clientHeight,0,0,0,0).Exp()),f[res.sel]) );
              } else {
                options.h = (options.h||0) + dx/300;
                options.p = (options.p||0) - dy/600;
                if (options.camera) options.camera.set( ( Element.Bivector(0,0,0,0,0,options.p).Exp() ).Mul( Element.Bivector(0,0,0,0,options.h,0).Exp() )/*.Mul(options.camera)*/ )
              }
              if (!anim) {var r=build(origf,(!res)||(document.body.contains(res))).innerHTML; if (res) res.innerHTML=r; }
              return;
            }
            if (res.sel===undefined || f[res.sel] == undefined || f[res.sel].set == undefined || !e.buttons) return;
            var resx=res.getBoundingClientRect().width,resy=res.getBoundingClientRect().height,
                x=((e.clientX-res.getBoundingClientRect().left)/(resx/4||128)-2)*(resx>resy?resx/resy:1),y=((e.clientY-res.getBoundingClientRect().top)/(resy/4||128)-2)*(resy>resx?resy/resx:1);
            x/=options.scale;y/=options.scale;
            if (options.conformal) { f[res.sel].set(this.Coeff(1,x,2,-y).Add(no).Add(ni.Scale(0.5*(x*x+y*y))) ) }
                              else { f[res.sel][drm[2]]=((drm[1]==6)?-x:x)-((tot<4)?2*options.camera.e01:0); f[res.sel][drm[3]]=-y+((tot<4)?2*options.camera.e02:0); f[res.sel][drm[1]]=1; f[res.sel].set(f[res.sel].Normalized)}
            if (!anim) {var r=build(origf,(!res)||(document.body.contains(res))).innerHTML; if (res) res.innerHTML=r; }
            res.dispatchEvent(new CustomEvent('input')) };
          return res;
        }
      }

    // The inline function is a js to js translator that adds operator overloading and algebraic literals.
    // It can be called with a function, a string, or used as a template function.
      static inline(intxt) {
      // If we are called as a template function.
        if (arguments.length>1 || intxt instanceof Array) {
          var args=[].slice.call(arguments,1);
          return res.inline(new Function(args.map((x,i)=>'_template_'+i).join(),'return ('+intxt.map((x,i)=>(x||'')+(args[i]&&('_template_'+i)||'')).join('')+')')).apply(res,args);
        }
      // Get the source input text.
        var txt = (intxt instanceof Function)?intxt.toString():`function(){return (${intxt})}`;
      // Our tokenizer reads the text token by token and stores it in the tok array (as type/token tuples).
        var tok = [], resi=[], t, possibleRegex=false, c, tokens = [/^[\s\uFFFF]|^[\u000A\u000D\u2028\u2029]|^\/\/[^\n]*\n|^\/\*[\s\S]*?\*\//g,                 // 0: whitespace/comments
          /^\"\"|^\'\'|^\".*?[^\\]\"|^\'.*?[^\\]\'|^\`[\s\S]*?[^\\]\`/g,                                                                // 1: literal strings
          /^\d+[.]{0,1}\d*[ei][\+\-_]{0,1}\d*|^\.\d+[ei][\+\-_]{0,1}\d*|^e_\d*/g,                                                       // 2: literal numbers in scientific notation (with small hack for i and e_ asciimath)
          /^\d+[.]{0,1}\d*[E][+-]{0,1}\d*|^\.\d+[E][+-]{0,1}\d*|^0x\d+|^\d+[.]{0,1}\d*|^\.\d+/g,                                        // 3: literal hex, nonsci numbers
          /^\/.*?[^\\]\/[gmisuy]?/g,                                                                                                    // 4: regex
          /^(\.Normalized|\.Length|\.\.\.|>>>=|===|!==|>>>|<<=|>>=|=>|\|\||[<>\+\-\*%&|^\/!\=]=|\*\*|\+\+|\-\-|<<|>>|\&\&|\^\^|^[{}()\[\];.,<>\+\-\*%|&^!~?:=\/]{1})/g,   // 5: punctuator
          /^[$_\p{L}][$_\p{L}\p{Mn}\p{Mc}\p{Nd}\p{Pc}\u200C\u200D]*/gu]                                                                 // 6: identifier
        while (txt.length) for (t in tokens) {
          if (t == 4 && !possibleRegex) continue;
          if (resi = txt.match(tokens[t])) {
            c = resi[0]; if (t!=0) {possibleRegex = c == '(' || c == '=' || c == '[' || c == ',' || c == ';';} tok.push([t | 0, c]); txt = txt.slice(c.length); break;
          }} // tokenise
      // Translate algebraic literals. (scientific e-notation to "this.Coeff"
        tok=tok.map(t=>(t[0]==2)?[2,'Element.Coeff('+basis.indexOf((!options.Cayley?simplify:(x)=>x)('e'+t[1].split(/e_|e|i/)[1]||1).replace('-',''))+','+(simplify(t[1].split(/e_|e|i/)[1]||1).match('-')?"-1*":"")+parseFloat(t[1][0]=='e'?1:t[1].split(/e_|e|i/)[0])+')']:t);
      // String templates (limited support - needs fundamental changes.).
        tok=tok.map(t=>(t[0]==1 && t[1][0]=='`')?[1,t[1].replace(/\$\{(.*?)\}/g,a=>"${"+Element.inline(a.slice(2,-1)).toString().match(/return \((.*)\)/)[1]+"}")]:t);
      // We support two syntaxes, standard js or if you pass in a text, asciimath.
        var syntax = (intxt instanceof Function)?[[['.Normalized','Normalize',2],['.Length','Length',2]],[['~','Conjugate',1],['!','Dual',1]],[['**','Pow',0,1]],[['^','Wedge'],['&','Vee'],['<<','LDot']],[['*','Mul'],['/','Div']],[['|','Dot']],[['>>>','sw',0,1]],[['-','Sub'],['+','Add']],[['%','%']],[['==','eq'],['!=','neq'],['<','lt'],['>','gt'],['<=','lte'],['>=','gte']]]
                                                :[[['pi','Math.PI'],['sin','Math.sin']],[['ddot','this.Reverse'],['tilde','this.Involute'],['hat','this.Conjugate'],['bar','this.Dual']],[['^','Pow',0,1]],[['^^','Wedge'],['*','LDot']],[['**','Mul'],['/','Div']],[['-','Sub'],['+','Add']],[['<','lt'],['>','gt'],['<=','lte'],['>=','gte']]];
      // For asciimath, some fixed translations apply (like pi->Math.PI) etc ..
        tok=tok.map(t=>(t[0]!=6)?t:[].concat.apply([],syntax).filter(x=>x[0]==t[1]).length?[6,[].concat.apply([],syntax).filter(x=>x[0]==t[1])[0][1]]:t);
      // Now the token-stream is translated recursively.
        function translate(tokens) {
          // helpers : first token to the left of x that is not of a type in the skip list.
          var left = (x=ti-1,skip=[0])=>{ while(x>=0&&~skip.indexOf(tokens[x][0])) x--; return x; },
          // first token to the right of x that is not of a type in the skip list.
              right= (x=ti+1,skip=[0])=>{ while(x<tokens.length&&~skip.indexOf(tokens[x][0])) x++; return x; },
          // glue from x to y as new type, optionally replace the substring with sub.
              glue = (x,y,tp=6,sub)=>{tokens.splice(x,y-x+1,[tp,...(sub||tokens.slice(x,y+1))])},
          // match O-C pairs. returns the 'matching bracket' position
              match = (O="(",C=")")=>{var o=1,x=ti+1; while(o){if(tokens[x][1]==O)o++;if(tokens[x][1]==C)o--; x++;}; return x-1;};
          // grouping (resolving brackets).
          for (var ti=0,t,si;t=tokens[ti];ti++) if (t[1]=="(") glue(ti,si=match(),7,[[5,"("],...translate(tokens.slice(ti+1,si)),[5,")"]]);
          // [] dot call and new
          for (var ti=0,t,si; t=tokens[ti];ti++) {
            if (t[1]=="[") { glue(ti,si=match("[","]"),7,[[5,"["],...translate(tokens.slice(ti+1,si)),[5,"]"]]); if (ti)ti--;}    // matching []
            else if (t[1]==".") { glue(left(),right()); ti--; }                                                                   // dot operator
            else if (t[0]==7 && ti && left()>=0 && tokens[left()][0]>=6 && tokens[left()][1]!="return") { glue(left(),ti--) }     // collate ( and [
            else if (t[1]=='new') { glue(ti,right()) };                                                                           // collate new keyword
          }
          // ++ and --
          for (var ti=0,t; t=tokens[ti];ti++) if (t[1]=="++" || t[1]=="--") glue(left(),ti);
          // unary - and + are handled separately from syntax ..
          for (var ti=0,t,si; t=tokens[ti];ti++)
            if (t[1]=="-" && (left()<0 || (tokens[left()]||[])[1]=='return'||(tokens[left()]||[5])[0]==5)) glue(ti,right(),6,["Element.Sub(",tokens[right()],")"]);   // unary minus works on all types.
            else if (t[1]=="+" && (left()<0 || (tokens[left()]||[])[1]=='return'|| (tokens[left()]||[0])[0]==5 && (tokens[left()]||[0])[1][0]!=".")) glue(ti,ti+1);                   // unary plus is glued, only on scalars.
          // now process all operators in the syntax list ..
          for (var si=0,s; s=syntax[si]; si++) for (var ti=s[0][3]?tokens.length-1:0,t; t=tokens[ti];s[0][3]?ti--:ti++) for (var opi=0,op; op=s[opi]; opi++) if (t[1]==op[0]) {
            // exception case .. ".Normalized" and ".Length" properties are re-routed (so they work on scalars etc ..)
                  if (op[2]==2) { var arg=tokens[left()]; glue(ti-1,ti,6,["Element."+op[1],"(",arg,")"]); }
            // unary operators (all are to the left)
              else if (op[2])    { var arg=tokens[right()]; glue(ti, right(), 6, ["Element."+op[1],"(",arg,")"]); }
            // binary operators
                            else { var l=left(),r=right(),a1=tokens[l],a2=tokens[r]; if (op[0]==op[1]) glue(l,r,6,[a1,op[1],a2]); else glue(l,r,6,["Element."+op[1],"(",a1,",",a2,")"]); ti-=2; }
          }
          return tokens;
      }
      // Glue all back together and return as bound function.
        return eval( ('('+(function f(t){return t.map(t=>t instanceof Array?f(t):typeof t == "string"?t:"").join('');})(translate(tok))+')') );
      }
    }

    res.arrow = res.inline(( from_point, to_point, w=0.03, aspect=0.8, camera=1 )=>{
        from_point = from_point/(-from_point|!1e0); to_point = to_point/(-to_point|!1e0);
        var line = ( from_point & to_point ), l = line.Length;
        var shape = [[0,w],[l-5*w,w],[l-5*w,aspect*5*w],[l,0],[l-5*w,-aspect*5*w],[l-5*w,-w],[0,-w]].map(([x,y])=>!(1e0+x*1e1+y*1e2));
        var sqrt = R => R==-1?1e12:(1+R).Normalized;
        var R = ((to_point - from_point).UnDual).Normalized * 1e1;
        var R2 = sqrt(from_point/!1e0) * sqrt(R);
        var p2 = R2 >>> 1e3;
        if (p2 != 0) { var p1 = (((~(camera+0e1) >>> 1e3)|line)/line).Normalized; return sqrt(p1/p2) * R2 >>> shape; }
        return  R2  >>> shape;
    })

    Object.defineProperty(res.prototype, 'Inverse', {configurable: true, get(){
      return this.Conjugate.Mul(this.Mul(this.Conjugate).Map(3,4)).Mul( this.constructor.Scalar(1/this.Mul(this.Conjugate).Mul(this.Mul(this.Conjugate).Map(3,4))[0]));
    }});

    res.inline(fu)();
  }
}));
