/*
Cycle
version 1.0.5
-----------------------------------
  Method      |   Class(es)
--------------|--------------------
+ kaprekar    | + Array / + Integer   ---> 1637.kaprekar(8)
+ sieve       | + Array               ---> [2,11,7,12,8,14].sieve
+ pea         | + Array / + Integer   ---> 1.pea
+ symGroup    | + Array               ---> [3,10,2,4,7,9,8,5,6,1].symGroup
+ symPerm     | + Array               ---> [1,3,2,4].symPerm([2,4,3,1])
+ cirPerm     | + Array / + Integer   ---> 1637.circPerm(10,2)
+ kreuzspiel  | + Array               ---> [1,2,3,4].kreuzspiel
+ lorenz      | + Number              ---> 0.234.lorenz(2)
+ collatz     | + Integer / + Env     ---> 1637.collatz / Env.collatz(1637)
+ interlace   | + Array               ---> [(1..4),(1..8),(1..3)].interlace
+ euclidean   | + Integer             ---> 5.euclidean(13,true)
+ campanology | + Array               ---> [1,2,3,4].campanology(1)
----------------------------------
<by.cmsc@gmail.com>
*/

+ Array {

	//-------------------------------------
	placecriblemat {
		|i,j|
		^this.collect{|cr| i.matpairslst(j).detect{|it| it[0] == cr}}
	}

	decallcriblemat {
		|i,j|
		^this.placecriblemat(i,j).collect{|e| i.matpairslst(j).detect{|it| (e[1]+i).mod(i*j) == it[1]}}.collect(_.first)
	}

	cyx {
		|ij|
		var cy = {
			|crible,ij|
			var i = ij[0];
			var j = ij[1];
			var pcm = [crible.placecriblemat(i,j).collect(_[0])];
			if ((1 == i.gcd(j)) && (i != 1) && (j != 1))
			{
				while( {pcm.indexOfEqual(pcm.last.decallcriblemat(i,j)).isNil},
					{pcm=pcm.add(pcm.last.decallcriblemat(i,j))} );
				pcm
			}
		};
		if (ij.notNil)
		{if(ij.product > this.maxItem){ ^[cy.(this,ij),cy.(this,ij.reverse)] }}
	}
	//-------------------------------------
	sieve {
		|field,i,j,optimize=\no|
		var a = this.maxItem+1;
		var k = if (i.asBoolean.xor(j.asBoolean)) {if(i.notNil){i}{j}};
		var f = if (field.isNumber) {field} {a};
		case

		{i.isInteger && j.isInteger} {if (((i*j) >= f) && (1 == i.gcd(j))) { ^this.cyx([i,j]) }}

		{field.isNil && k.isNil}
		{
			case
			{(optimize == \yes) || (optimize == \y)} { ^this.cyx(a.iandj(\plusyes)) }
			{(optimize == \no) || (optimize == \n)} { ^this.cyx(a.iandj(\plusno)) }
		}

		{(f >= a) && k.isNil}
		{
			case
			{(optimize == \no) || (optimize == \n)} { ^this.cyx(f.iandj(\moinsno)) }
			{(optimize == \yes) || (optimize == \y)} { ^this.cyx(f.iandj(\moinsyes)) }
			{(optimize == \field) || (optimize == \f)} { ^this.cyx(a.infx(f, k)) }
		}

		{field.isNil && k.notNil} { ^this.cyx(k.iorjplus(a)) }

		{(f >= a) && k.notNil}
		{
			if ((optimize == \field) || (optimize == \f))
			{ ^this.cyx(a.infx(field, k)) }
			{if (k.iorjmoins(f).asBoolean) { ^this.cyx(k.iorjmoins(f)) }}
		}
	}

	symGroup {
		|ref|
		var in, al;
		var tolist = { |ar| [Array.series(ar.size, 1),ar].flop };
		var boucle = {
			|tl, res|
			var tmp;
			if (res.isNil)
			{res=[tl[0]]; boucle.(tl,res)}
			{tmp=tl.detect{|it| res.last.last == it.first}};
			if ((tmp.isNil.not) && (res.last[0] != res.last[1]))
			{
				if ((res.includesEqual(tmp)).not)
				{res=res.add(tmp)}
			};
			if ((res.last[0] == res.last[1]) || (res.collect(_.first).includesEqual(if (tmp.isNil.not) {tmp.last})))
			{ res }
			{ boucle.(tl,res)}
		};
		var remassoc = {
			|boucle, ar|
			ar.reject{|it| boucle.includesEqual(it)}
		};
		var cfp = {
			|ar, res|
			res=res.add(boucle.(ar).collect(_.first));
			if (remassoc.(boucle.(ar), ar).isEmpty)
			{ res }
			{ cfp.(remassoc.(boucle.(ar), ar), res) }
		};
		//-----------
		if ((ref.notNil) && (ref.asArray.asBag == this.asBag))
		{
			al = [Array.series(ref.asArray.size, 1), ref.asArray].flop;
			in = this.collect{|it| al.detect{|itt| itt[1] == it}}.collect(_[0]);
			^cfp.(tolist.(in)).collect{|a| a.collect{|it| al.detect{|itt| itt[0] == it}}.collect(_[1])}
		}
		//-----------
		{
			if ((ref.isNil) && (difference(this, (1..this.size)).isEmpty))
			{ ^cfp.(tolist.(this)) }
			{ "Wrong array input!".error; ^nil }
		}
	}

	campanology { |mode=0, rev=false|
		//----------------
		// code ref: https://scsynth.org/t/do-not-returning-array/6416/14
		var size = this.size;
		var swapConsequtiveIndexes = {|from, to|
			(from..to).clump(2).collect{|p| p.reverse }.flat};
		var indexesEven = swapConsequtiveIndexes.(0, size - 1);
		var indexesOdd = [0] ++ swapConsequtiveIndexes.(1, size - 1);
		var swappers = size.collect{ |n|
			{|toSwap|
				if
				(
					case
					{mode==0} {n.odd}
					{mode==1} {n.even}
				)
				{ indexesEven.collect{|i| toSwap[i]} }
				{ indexesOdd.collect{|i| toSwap[i]} }
			}};
		var campanology = swappers.inject( [this], {
			|col, f|
			col ++ [f.(col.last)]
		});
		//----------------
		if (rev)
		{ ^campanology }
		{ ^campanology ++ campanology.last
			.campanology(
				case
				{mode==0} {if (size.even) {0} {1}}
				{mode==1} {if (size.even) {1} {0}},
				rev:true)[1..size-1] }
	}

	kreuzspiel { |ind|
		var res = Array.new;
		var kpop = { |ar, ind|
			var p1, p2;
			if ((ind > 0) && (ind < ar.size))
			{
				p1 = ar[..ind-1];
				p2 = ar[ind..];
				p1[1..] ++ p2.last ++ p1.first ++ p2[..p2.size-2]
			}
			{ ar }};
		var rec = {
			|ar, ind, res, i|
			if(res.indexOfEqual(ar).isInteger)
			{ res }
			{
				i=i+1;
				// this test avoid SC to crash for inf loop
				if(i>100000,
					{  "something went wrong! Please report this issue.".error; res[0] },
					{ res=res.add(ar); rec.(kpop.(ar, ind), ind, res, i) })
			}
		};
		if (ind.isNumber)
		{ ^rec.(this, ind.abs.asInteger%this.size, res, 1) }
		{
			if (ind.isNil)
			{ ^this.kreuzspiel((this.size/2).floor) }
			{ "kreuzspiel ind requires only integer.".error; ^nil }
		}
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
				^tmp.butlast },
			{ "symPerm argument requires a combined series such as (symPerm.asBag == (1..symPerm.size).asBag) and (symPerm.size == this.size).".error; ^nil })
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
				^tmp.collect{|it| it.toBase(cBase, iBase, n)}.butlast },
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
		var res = this[0..this.size-2];
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
		^this.flatten(1);
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
			^this.asDigits(iBase).circPerm(iBase, cBase).collect{|it| it.convertDigits(iBase)}
		}{
			"only for positive integer".error; ^nil
		}
	}

	campanology { |mode=0, rev=false|
		^this.asDigits.campanology(mode,rev).collect{|it| it.convertDigits}
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

	//-------------------------------------
	voirX {
		var asg = {
			|ar|
			(0..(ar.size-2)).collect{
				|i|
				(0..(ar.size-i-1)).collect{|j| ar.copyRange(j, j+i)}
			}.flatten(1).removeAllSuchThat{|it| it.notEmpty}
		};
		var fact = this.factors;
		var res=[], tmp;
		asg.(fact).do{
			|it|
			if ((1 == it.product.gcd(difference(fact,it).product))
				&&
				(0 != (it.product - difference(fact,it).product)))
			{
				res=res.add([(it.product - difference(fact,it).product).abs, it, difference(fact,it)])
			}
		};
		tmp=res.sort{|a,b| a[0] < b[0]}.collect(_[1..]).first;
		if (tmp.notNil)
		{
			if (tmp.every{|it| it.notEmpty})
			{ ^tmp }
			{ ^nil }
		}
		{ ^nil }
	}


	iandj1 {
		var vx = this.voirX;
		if (vx.notNil)
		{ ^vx.collect(_.product).sort }
		{ ^[1,1] }
	}

	optplus {
		var ij = this.iandj1;
		if (0 != ij.differentiate.last)
		{
			if ((this+1).iandj1.differentiate.last.abs < ij.differentiate.last.abs)
			{
				if (0 == (this+1).iandj1.differentiate.last)
				{ ^ij }
				{(this+1).optplus}
			}
			{ ^ij }
		}
		{(this+1).optplus}
	}

	optmoins {
		var ij = this.iandj1;
		if (0 != ij.differentiate.last)
		{
			if ((this-1).iandj1.differentiate.last.abs < ij.differentiate.last.abs)
			{
				if (0 != (this+1).iandj1.differentiate.last)
				{ ^ij }
				{(this-1).optmoins}
			}
			{ ^ij }
		}
		{(this-1).optmoins}
	}

	iandj {
		|key|
		case
		{key == \plusno} {if (this.voirX.isNil) { ^(this+1).iandj1 } { ^this.iandj1 }}
		{key == \plusyes} { ^this.optplus }
		{key == \moinsno} {if (this.voirX.isNil) { ^(this-1).iandj1 } { ^this.iandj1 }}
		{key == \moinsyes} { ^this.optmoins }
	}

	iorj1 {
		|x|
		if (x > (this*2))
		{
			if (0 == x.mod(this))
			{
				if (1 == this.gcd((x/this).asInteger))
				{[this, (x/this).asInteger]}
			}
		}
	}

	iorjplus {
		|x|
		if (x > (2*this))
		{
			if (0 == x.mod(this))
			{
				if (1 == this.gcd((x/this).asInteger))
				{ ^[this, (x/this).asInteger].sort }
				{this.iorjplus(x+1)}
			}
			{this.iorjplus(x+1)}
		}
	}

	iorjmoins {
		|k,x|
		if (x > (2*this))
		{
			if (0 == x.mod(this))
			{
				if (1 == this.gcd((x/this).asInteger))
				{ ^[this, (x/this).asInteger].sort }
				{this.iorjmoins(x-1)}
			}
			{this.iorjmoins(x-1)}
		}
	}

	infx {
		|b,k|
		var res=[];
		if (k.isNil)
		{
			(b-this).do{
				|it| if ((it+this).voirX.notNil) {res=res.add([(it+this).iandj1.differentiate.last, (it+this).iandj1])}
			}
		}
		{
			if (k < (b/2))
			{
				(b-this).do{
					|it| if (k.iorj1(it+this).notNil) {res=res.add([k.iorj1(it+this).differentiate.last.abs, k.iorj1(it+this)])}}
			}
		};
		if (res.notEmpty)
		{ ^res.reverse.minItem(_.first)[1] }
	}

	xmatricemod {
		|j|
		var modby1 = {
			|i,j|
			(0..i-1).collect{|a| (a*(i+1)).mod(i*j)}
		};
		var modby2 = {
			|i,j, modby1|
			(Array.fill(i,i+1)*(0..i-1)).collect{|a| (a+modby1.last+1).mod(i*j)}
		};
		var res=[modby1.(this,j)];
		(j-1).do{res=res.add(modby2.(this,j,res.last))};
		^res
	}

	matpairslst {
		|j|
		^[this.xmatricemod(j).flat, (0..(this*j)-1)].flop
	}
	//-------------------------------------

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
		col = n.collatz.seq ++ 0;
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