/*
Cycle
version 1.0.3
----------------------------------
  Method     |   Class(es)
-------------|--------------------
+ kaprekar   | + Array / + Integer   ---> 1637.kaprekar(8)
  sieve      | + Array
+ pea        | + Array / + Integer   ---> 1.pea
  symGroup   | + Array
+ symPerm    | + Array               ---> [1,3,2,4].symPerm([2,4,3,1])
+ cirPerm    | + Array / + Integer   ---> 1637.circPerm(10,2)
  kreuzspiel | + Array
+ lorenz     | + Number              ---> 0.234.lorenz(2)
+ collatz    | + Integer / + Env     ---> 1637.collatz / Env.collatz(1637)
+ interlace  | + Array               ---> [(1..4),(1..8),(1..3)].interlace
+ euclidean  | + Integer             ---> 5.euclidean(13,true)
----------------------------------
<by.cmsc@gmail.com>
*/

+ Array {

	sieve {
		"Not yet implemented.".error; ^nil
	}

	symGroup {
		"Not yet implemented.".error; ^nil
	}

	kreuzspiel {
		"Not yet implemented.".error; ^nil
	}

	symPerm { | arrayCode |
		var tmp;
		var res = Array.new;
		var ac = Array.newFrom(arrayCode);
		var rec = { | val, ser, ar |
			var perm=[ser,val].flop.sort{|x,y| x[0]<y[0]}.flop[1];
			ar=ar.add(val);
			if(ar.any{|it| it.isEqual(perm)})
			{
				ar=ar.add(perm)
			}
			{
				rec.value(perm, ser, ar)
			}
		};
		if(arrayCode.isArray && (this.size==arrayCode.size) && (ac.sort[0]==1) && ac.sort.isSeries(1),
			{ tmp = rec.(this, arrayCode, res);
				^tmp },
			{ "symPerm argument requires a scrambled series from 1 to the size of the symPerm array.".error; ^nil })
	}

	isEqual { | to |
		^this.every { |it, i| to[i]==it };
	}

	interlace {
		if(this.alwaysArray)
		{
			var len = this.collect{|it|it.size};
			var mx = len.lcm(len.maxItem).maxItem;
			var al=len.collect{|it|mx/it}.asInteger;
			var tmp=[this,len,al].flop.collect{|it|it[0].wrapExtend(it[1]*it[2])}.flop;
			^tmp
		}
		{
			"interlace array requires only arrays".error; ^nil
		}
	}

	pea {
		var tmp;
		var res = Array.new;
		var rec = { | val, ar |
			var ref=val.asSet.asArray.sort;
			var hist=ref.collect{|it| val.count{|x| it==x}};
			ar=ar.add(val);
			val=[hist,ref].flop.flat;
			if(ar.indexOfEqual(val).isInteger)
			{
				ar=ar.add(val)
			}
			{
				rec.value(val, ar)
			}
		};
		if(this.alwaysInteger(0),
			{ tmp = rec.(this, res);
				^tmp.asCycle },
			{ "pea array requires only positive integer".error })
	}

	circPerm { | iBase=10, cBase=2 |
		var tmp;
		var n=this.size;
		var res = Array.new;
		var rec = { | val, base, ar |
			var circ;
			ar=ar.add(val);
			val=val.reverse;
			circ=val.pop;
			val=val.addFirst(circ).reverse;
			if(ar.indexOfEqual(val).isInteger)
			{
				ar=ar.add(val)
			}
			{
				rec.value(val, base, ar)
			}
		};
		if(this.alwaysInteger(0),
			{ tmp = rec.(this.toBase(iBase, cBase), cBase, res);
				^tmp.collect{|it| it.toBase(cBase, iBase, n)} },
			{ "circPerm array requires only positive integer".error })
	}

	toBase { | ibase, cbase, n |
		^this.convertDigits(ibase).asDigits(cbase, n)
	}

	kaprekar { | base=10 |
		var tmp;
		var res = Array.new;
		var	kaDiff = { | ar, base=10 |
			var diff;
			var ref = Array.newFrom(ar);
			var arr = ref.sort;
			var len = ref.size;
			var k1 = arr.reverse.convertDigits(base);
			var k2 = arr.convertDigits(base);
			diff = k1-k2;
			diff.asDigits(base, len)
		};
		var rec = { | val, base, ar, i |
			if(ar.isEmpty, {ar=ar.add(val)});
			if(ar.indexOfEqual(kaDiff.(val,base)).isInteger)
			{
				ar=ar.add(kaDiff.(val,base))
			}
			{
				i=i+1;
				// this test avoid SC to crash for inf loop
				if(i>100000,
					{  "something went wrong! Please report this issue.".error; ar[0] },
					{ ar=ar.add(kaDiff.(val,base));
						rec.value(kaDiff.(val,base), base, ar, i) })
			}
		};
		if(this.alwaysInteger(0) && base.isInteger && (base>1),
			{ tmp = rec.(this, base, res, 1);
				^tmp.asCycle },
			{ "kaprekar array requires only positive integer".error })
	}

	alwaysInteger { | n |
		if (n.isInteger,
			{ ^this.every { |x| x.isInteger && (x >= n) }; },
			{ ^this.every { |x| x.isInteger }; })
	}

	alwaysArray {
		^this.every { |x| x.isArray };
	}

	butlast {
		var res = this[0..this.size-1];
		^res
	}

	isSingleton {
		if(this.size == 1) {^true} {^false}
	}

	asCycle {
		var a, b, c, i, res;
		a=this.asArray;b=[];i=0;while({(a[i]!=a.last) && (i<a.size)},{b=b.add(a[i]);i=i+1});res=[b,a.copyRange(i, a.size-2)];
		^res.reject{|i| i.isEmpty}
	}

	seq {
		^this.flatten(1).butlast;
	}

	cycle {
		^this.last;
	}

	path {
		if(this.isSingleton.not)
		{ ^this.first }
		{ ^nil }
	}

	asIndex { | al |
		var depth=this.maxDepth;
		if (this.flat.alwaysInteger(0) && (this.flat.maxItem<al.size))
		{
			^this.deepCollect(depth, {|it| al[it].asInteger})
		}
		{
			"The content of the array cannot be the indices of al".error; ^nil;
		}
	}

}

+ Integer {

	pea {
		if(this.isPositive)
		{
			^this.asArray.pea
		}{
			"only for positive integer".error; ^nil
		}
	}

	circPerm { | iBase=10, cBase=2 |
		if(this.isPositive)
		{
			^this.asDigits(iBase).circPerm(iBase,cBase).collect{|it| it.collect{|itt| itt.convertDigits(iBase)}}
		}{
			"only for positive integer".error; ^nil
		}
	}

	kaprekar { | base=10 |
		if(this.isPositive && base.isInteger && (base>1))
		{
			^this.asDigits(base).kaprekar(base).collect{|it| it.collect{|itt| itt.convertDigits(base)}}
		}{
			"only for positive integer".error; ^nil
		}
	}

	collatz {
		var tmp;
		var res = Array.new;
		var rec = { | n, r, i |
			n=n.asInteger;
			(r.isNil.not && r.asArray.includes(n)).if (
				{
					r=r.add(if(r.last.even, {r.last/2}, {3*r.last+1}).asInteger)
				},
				{
					i=i+1;
					// this test avoid SC to crash for inf loop
					if(i>100000,
						{  "something went wrong! Please report this issue".error; r[0] },
						{
							r=r.add(n);
							(n.even).if (
								{rec.value(n/2, r, i)},
								{rec.value(3*n+1, r, i)})})
				}
			)};
		tmp = rec.(this, res, 1);
		^tmp.asCycle
	}

	euclidean { | n, ratio |
		var tmp;
		var rec = { | len, m, head, tail, ratio |
			var res;
			((head.isNil.not && (tail.size<2))).if (
				{
					if(ratio.asBoolean)
					{res=(head ++ tail).flat;(res.collect{|it,i| if(it==1){i}}.select{|it| it.isInteger && it.asBoolean}).add(res.size).differentiate
					}
					{(head ++ tail).flat}
				},
				{
					rec.value(nil, nil, if(len.asBoolean,{Array.fill(len, 1)},{[head.size,tail.size].minItem.collect{|i| head[i].asArray++tail[i].asArray}}), if(len.asBoolean,{Array.fill(m-len, 0)},
						{
							if(head.size == tail.size)
							{nil}
							{if(head.size > tail.size)
								{Array.fill(head.size-tail.size, head[0])}
								{Array.fill(tail.size-head.size, tail[0])}
							}
						}
					), ratio)
				}
		)};
		if(n.isInteger && (this>0) && (n>=this))
		{
			tmp = rec.(this, n, nil, nil, ratio);
			^tmp
		}
		{
			"Condition: this > 0 AND n >= this AND n must be an integer.".error; ^nil;
		}
	}

}

+ Number {

	lorenz { | n=0.000001 |
		if((this<=1) && (this>=0))
		{
			var tmp;
			var res = Array.new;
			var rec = { | in, r, i |
				(r.isNil.not && r.asArray.includes(in.round(n))).if (
					{
						r=r.add(in)
					},
					{
						i=i+1;
						// this test avoid SC to crash for inf loop
						if(i>100000,
							{  "something went wrong! Please report this issue".error; r[0] },
							{
								r=r.add(in.round(n));
								(2*in.round(n)<=1).if (
									{rec.value(2*in.round(n), r, i)},
									{rec.value(2*in.round(n)-1, r, i)})})
					}
			)};
			tmp = rec.(this.round(n), res, 1);
			^tmp.asCycle
		}{
			"lorenz requires a number between 0 and 1".error; ^this;
		}
	}

}

+ Env {

	*collatz { | n, dur=1, normX=0, normY=\max |
		var col, env, levels, times;
		col = n.collatz ++ 0;
		if (normY == \freq)
		{
			col=col/n
		};
		if (normY == \max)
		{
			col=col/col.maxItem
		};
		levels = col ++ 0;
		if (normX > (col.size))
		{
			times = (dur/normX)!(col.size-1) ++ (dur - ((dur/normX)*(col.size-1)));
		}
		{
			times = (dur/col.size)!(col.size-1);
		};
		env = this.new(levels, times);
		^env;
	}

}