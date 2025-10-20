/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/

import LectureNotes.Formatting

set_option autoImplicit false
set_option pp.rawOnError true

open Verso.Genre Manual

#doc (Manual) "Rationals"  =>

So far we have defined the integers, $`0`, $`1`, addition, negation and multiplication,
and in the previous chapter and Sheet 2 we proved the following facts:

:::theorem "int" (title := "Summary of main results about integers")
For all integers $`x`, $`y` and $`z`, we have:
* $`0+x=x+0=x`; ($`0` is an additive identity)
* $`x+(y+z)=(x+y)+z`; (addition is associative)
* $`(-x)+x=x+(-x)=0`; (negation is an additive inverse)
* $`x+y=y+x`; (addition is commutative)
* $`1\times x=x\times 1=x`; ($`1` is a multiplicative identity)
* $`x(yz)=(xy)z`; (multiplication is associative)
* $`xy=yx`; (multiplication is commutative)
* $`x(y+z)=xy+xz` and $`(x+y)z=xz+yz`. (multiplication distributes over addition)
:::

As you will learn later on in this degree,
those are the axioms for what is called a _commutative ring_.
Because subtraction $`a-b` can be defined as $`a+(-b)`, we now have three of the four basic mathematical operations.
The one missing one is division; we cannot solve equations like $`2x=1` in the integers.
A commutative ring with a well-behaved division is called a _field_, and in the next chapter we shall be studying the rationals, reals and complexes, three examples of fields.

But let's get back to the problem at hand.
To solve $`2x=1` we need to move away from the integers and make a new bigger system of numbers:
the _rationals_, a system containing new numbers such as $`1/2`.

# Construction of the rationals

We will mimic our approach to defining the integers from the naturals.
We don't want to allow division by $`0`, but conversely we know that what we want is a number system where every number can be written as $`a/b` with $`b\not=0`.
So our first approach -- the set of "pre-rationals" if you like, is just the set $`\Z\times(\Z-\{0\})`,
and the idea is that the element $`(a,b)` represents the rational $`a/b`.

However, just as with the integers, we now have "too many" numbers to be rationals.
The elements $`(1,2)` and $`(2,4)` are distinct in $`\Z\times(\Z-\{0\})`
but we want $`1/2` and $`2/4` to be the same rational number.
So we need to "identify" these distinct elements $`(1,2)` and $`(2,4)` (as well as $`(3,6)` and $`(-1,-2)` and $`\ldots`)
by making them _equivalent_.
The mathematical calculation is this:
pretending that $`\mathbb{Q}` exists for a second, and that $`b,d\not=0`, we have $`a/b=c/d` if and only $`ad=bc`.
Hence let us put the following binary relation on $`\Z\times(\Z-\{0\})`:

:::definition
Define the following binary relation on $`\mathbb{Z}\times(\mathbb{Z}-\{0\})`: we say
$$`(a,b)\sim (c,d) \text{ if and only if }ad=bc.`
:::

:::theorem
This binary relation is an equivalence relation.
:::

:::proof
* Reflexivity: we have to check $`(a,b)\sim(a,b)`, or in other words $`ab=ba`, and this follows from ({theoremref "int"}[]).
* Symmetry: we have to check that if $`(a,b)\sim(c,d)` then $`(c,d)\sim(a,b)`. In other words we have to check that $`ad=bc\implies cb=da`,
  but this follows because multiplication is commutative and equality is symmetric.
* Transitivity: we have to check that if $`(a,b)\sim(c,d)` and $`(c,d)\sim(e,f)` then $`(a,b)\sim(e,f)`.
  In other words, we need to check that if $`ad=bc` and $`cf=de` then $`af=be`.
  First we observe that $`afd=adf=bcf=bde=bed`, so we will be done if we can cancel $`d`, but $`d\not=0` and so we can; this follows from a question on Problem Sheet~2.
:::

:::definition "rat_def" (title := "The rationals")
The _rational numbers_ $`\mathbb{Q}` are defined to be the quotient of $`\Z\times(\Z-\{0\})` by this equivalence relation.
In other words, the rationals are defined to be the set of equivalence classes for this equivalence relation.
:::

# The gory details of +, -, ×, /

Unfortunately this is incredibly tedious to do on paper.
I would not spend too much time worrying about this subsection; it's many many simple calculations.

We have the notation $`cl(a,b)` for the equivalence class of $`(a,b)\in\Z\times(\Z-\{0\})`;
we would like to call it $`a/b` but we need to hold off on this until we have defined division!

Of course, as well as division, we also want to have an addition and a multiplication on $`\mathbb{Q}`, satisfying
$$`\frac{a}{b}+\frac{c}{d}=\frac{ad+bc}{bd},\quad \frac{a}{b}\times\frac{c}{d}=\frac{ac}{bd}`
and we also need to define negation $`-x` of a rational and reciprocal $`x^{-1}` of a nonzero rational;
then we can define subtraction $`x-y` to be $`x+(-y)`, and division $`x/y` to be $`x\times y^{-1}` and we will finally have our four basic arithmetical operations.

This construction is quite formal and very tedious.
Let me plough through it in these notes.
Looking back at our approach for defining operations on the integers, we see that we need to do the following.

:::definition "pre-ops" (title := "pre-operations")
* We define pre-addition on $`\Z\times(\Z-\{0\})` by $`(a,b)+(c,d)=(ad+bc,bd)`.
* We define pre-negation on $`\Z\times(\Z-\{0\})` by $`-(a,b)=(-a,b)`.
* We define pre-multiplication on $`\Z\times(\Z-\{0\})` by $`(a,b)\times(c,d)=(ac,bd)`.
* We define pre-reciprocal on $`(\Z-\{0\})\times(\Z-\{0\})` by $`(a,b)^{-1}=(b,a)`.
:::

It is worth remarking that everything here makes sense, i.e., that all the second terms in each bracket are nonzero. For addition and multiplication this is because the product of two non-zero integers is non-zero (see the second problem sheet).

Now let's go back to defining these operations on the rationals.
Let me explain the problem again.
The rationals are "pairs of integers, glued together".
When you give a function the same input twice, it _has_ to give the same output -- that's what being a function is about.
So if we're trying to define a function on a set which is a bunch of things glued together, we need to make sure that the function doesn't take two things glued together and rip them apart and send them to different things.

More formally, to show that these "pre" operations really do descend to operations on the rational numbers, we must hence have to prove the following.
:::theorem "pre_ops_lift" (title := "pre-operations descend to the quotient")
1. If $`(a,b)\sim(a',b')` then $`(a,b)+(c,d)\sim(a',b')+(c,d)`, and if $`(c,d)\sim(c',d')` then $`(a,b)+(c,d)\sim(a,b)+(c',d')`.
2. If $`(a,b)\sim(a',b')` then $`-(a,b)\sim-(a',b')`.
3. If $`(a,b)\sim(a',b')` then $`(a,b)\times(c,d)\sim(a',b')\times(c,d)` and if $`(c,d)\sim(c',d')` then $`(a,b)\times(c,d)\sim(a,b)\times(c',d')`.
4. If $`(a,b)\sim(a',b')` and $`a,a'\not=-0` then $`(a,b)^{-1}\sim(a',b')^{-1}`.
:::

:::proof
None of these are hard, and the first one is probably the most complicated (because the definition of pre-addition is the messiest).
I'll do that one and will leave the rest to you.
1. For the first part, we know $`ab'=ba'` and we want to check that $`(ad+bc,bd)\sim(a'd+b'c,b'd)`, or equivalently that $`(ad+bc)b'd=bd(a'd+b'c)`.
  Multiplying everything out (i.e., using distributivity) we reduce the goal to $`(ad)(b'd)+(bc)(b'd)=(bd)(a'd)+(bd)(b'c)`.
  Using commutativity and associativity loads of times gives $`ab'dd+bcb'd=ba'dd+bcb'd`, and now $`ab'=ba'` gives the result easily.

  For the second part, we know that $`cd'=dc'` and need to show $`(ad+bc,bd)\sim(ad'+bc',bd')` or equivalently that $`(ad+bc)bd'=bd(ad'+bc')`.
  Again multiplying out the brackets and applying commutativity and associativity of multiplication the result follows from $`cd'=dc'`.

The rest are on the problem sheet.
:::

:::corollary "add_def" (title :="addition, subtraction, multiplication")
We can define addition, negation and multiplication on $`\mathbb{Q}` by $`cl(a,b)+cl(c,d)=cl((a,b)+(c,d))`, $`-cl(a,b)=cl(-a,b)`, $`cl(a,b)\times cl(c,d)=cl(ac,bd)`
:::

:::proof
The subtle thing which needs to be done here is simply to check that our functions are well-defined, that is, in each case, changing the input $`cl(a,b)` to the _equal_ element $`cl(a',b')` if $`(a,b)\sim(a',b')` doesn't change the value of the answer.
But this is exactly what we proved in the previous theorem.
:::

Just as we considered the naturals as being a subset of the integers via an explicit map, let's define $`j:\Z\to\mathbb{Q}` by $`j(z)=cl(z,1)` (i.e., the rational which we think of as $`z/1`).
We leave as an exercise to show that the map $`j` is injective and preserves addition and multiplication.

We define the rational $`0` to be $`j(0)=cl(0,1)`.
Now, reciprocal is a bit different from the other operations because it doesn't work with $`0` (infinity is not a number).
So let's just check that we've got this straight.
First let's observe that if $`(a,b)\sim(0,1)` then by definition $`a\times1=b\times 0`, so $`a=0`.
Thus reciprocals definitely make sense on the rationals:

:::definition (title := "reciprocal on the rational numbers")
If $`x\not=0` is a rational number then every $`(a,b)` in the equivalence class representing $`x` has $`a\not=0`, so $`(a,b)^{-1}` makes sense (the pre-reciprocal).
We define $`x^{-1}` to be the class of $`(a,b)^{-1}` and note that it's well-defined by the previous theorem.
:::

It's tiresome talking about $`(a,b)` and $`cl(a,b)`. Let's introduce the more sensible notation $`a/b`, and check that this really is $`a` divided by $`b` in the sense we've just introduced.

:::lemma "rat_sensible" (title := "Sensible notation for rationals")
  If $`a` and $`b` are integers and $`b\not=0`, and if we abuse notation also call $`a` the rational number $`j(a)=cl(a,1)` and similarly for $`b`, then the equivalence class of $`(a,b)` is the rational number $`a/b`.
:::
:::proof
The definition of $`a/b` is $`j(a)\times j(b)^{-1}`, so it's the class of $`(a,1)\times(b,1)^{-1}`, so it's the class of $`(a,1)\times(1,b)`, so it's the class of $`(a\times 1, 1\times b)`, so it's the class of $`(a,b)`.
:::

It turns out that the rationals are a _field_.
Let me explicitly record the definition of a field here.

:::definition "field_def" (title := "Fields")
  A _field_ is a set $`X`, equipped with two special elements $`0\in X` and $`1\in X` with $`0\not=1`, two functions $`+:X\times X\to X` and $`\times:X\times X\to X`, and two other functions $`-:X\to X` and $`(\cdot)^{-1}:(X-\{0\})\to X`, satisfying the following axioms:

For all $`x,y,z\in X`, we have:
* $`0+x=x+0=x`; ($`0` is an additive identity)
* $`x+(y+z)=(x+y)+z`; (addition is associative)
* $`(-x)+x=x+(-x)=0`; (negation is an additive inverse)
* $`x+y=y+x`; (addition is commutative)
* $`1\not=0`; (fields have at least two elements)
* $`1\times x=x\times 1=x`; ($`1` is a multiplicative identity)
* $`x(yz)=(xy)z`; (multiplication is associative)
* If $`x\not=0` then $`x\times x^{-1}=x^{-1}\times x=1`; (reciprocal is a multiplicative inverse)
* $`xy=yx`; (multiplication is commutative)
* $`x(y+z)=xy+xz` and $`(x+y)z=xz+yz`. (multiplication distributes over addition)
:::

Exercise: which two axioms of a field aren't axioms of a commutative ring?

Fields are important because the abstract theory of _vector spaces_ works over any field.
The non-JMC students among you will already have heard about these in the IUM Applied lectures.
And they are also covered in the Linear Algebra and Groups module later this term.

The rational numbers are a field, but we skip the proof -- not because it is hard, but because it is long and very boring, and every check is very easy if you know what you're doing.
I'll force you to do one of the checks on the last problem sheet.

# The operation ≤ on the rationals

We say that an integer is _non-negative_ if it is in the image of the map $`i:\N\to\Z`.
We say that a rational number is _non-negative_ if it can be written as $`a/b` with $`a` and $`b` integers both of which are non-negative (and of course with $`b\not=0`).
If $`x` and $`y` are rational numbers then we say $`x\leq y` if $`y-x` is non-negative.

It is now a very long but straightforward exercise to prove that $`\leq` is a total order on $`\mathbb{Q}`.
And it is another fairly long and straightforward exercise to show that if $`a` and $`b` are integers, then $`a\leq b\iff q(a)\leq q(b)` (remember that $`q` is the function from the integers to the rationals), that if $`x\leq y` then $`x+n\leq y+n`, and if $`0\leq x` and $`0\leq y` then $`0\leq xy`.

I think I will spare you these exercises, and instead just say that from now on you can just assume all the standard facts about $`+,-,\times,/` and $`\leq` which you know about rational numbers.
It's quite satisfying to do these exercises in Lean, for just the same reason that it's annoying to do them on paper: there are lots of them, and all the proofs are short.
