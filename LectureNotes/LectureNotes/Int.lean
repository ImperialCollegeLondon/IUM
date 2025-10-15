/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/

import LectureNotes.Formatting
import LectureNotes.Int.Arithmetic

set_option autoImplicit false
set_option pp.rawOnError true

open Verso.Genre Manual

#doc (Manual) "Integers"  =>

We now define the integers.
The integers are _constructed_ from the natural numbers, and in this chapter we explain the construction.

# Construction of the integers

We have developed a theory of addition, but there are equations involving addition such as $`x+3=2` which we cannot solve in natural numbers.
The approach we will take to fix this is to define a _new_ number system, the _integers_:

$`\Z=\{\ldots,-3,-2,-1,0,1,2,3,\ldots\}.`

Of course we cannot use this as a definition because it has $`\ldots` in it.
So how do we construct the integers formally from the naturals?
We will explain a beautiful method using the theory of equivalence relations and equivalence classes.

We want to think of negative integers as things like "the result of subtracting 7 from 4" --
whatever this is.
Now, every integer $`k` can be expressed as a difference $`a - b` of natural numbers, and in particular can be built from two natural numbers.
So how about we just _define_ the integers to be $`\N \times \N`, the set of ordered pairs of natural numbers?
The ordered pair $`(4,7)` would then correspond to the integer $`4 - 7`.

But there is a problem here: we have _too many_ integers with this definition.
The ordered pairs $`(4,7)` and $`(5,8)` are different pairs
(they are different vectors in the plane, if you like),
but the integers $`4-7` and $`5-8` are _equal_.
There isn't just _one_ way to write an integer $`k` as a difference $`a-b`, there are _lots_ of ways.

What we want to do then, is to start with $`\N \times \N` (which is too big) and then "squish some elements together" and somehow make $`(4,7)` and $`(5,8)` "equal" even though they are not actually equal.
Once we have squished $`(4,7)` and $`(5,8)` and $`(6,9)` and $`(n,n+3)` together, and then squished together all the other different pairs of natural numbers which give rise to the same integer,
then we really will have defined the integers.{margin}[Note that there is another possibility here:
instead of squishing different pairs together, we could decide to _throw out_ all pairs $`(a,b)` except those of the form $`(a,0)` or $`(0,b)`, i.e. we only consider "differences" $`a-0` and $`0-b`.
This might superficially look simpler, but it causes real problems later on.
For example the standard formula $`(a-b)+(c-d)=(a+c)-(b+d)` is no longer helpful in telling us how to add differences,
because even if one each of the numbers in $`(a,b)` and $`(c,d)` is zero,
this may not be the case for $`(a+c, b+d)`.
You could still define the sum to be "start with $`(a+c, b+d)` and decrement until one of these numbers reaches zero," but then proving things like associativity of addition becomes a _nightmare_.]

-- Instead of having to manipulate $`(a+c, b+d)` to put it into lowest terms,
-- our approach is to allow non-lowest-terms differences but set things up so that they are _equivalent_ to the corresponding lowest term difference, and then use equivalence classes.

This squishing together of different elements of a set is formally done by putting an _equivalence relation_ on the set, and then considering the _equivalence classes_.
The axioms of an equivalence relation are an attempt to mimic and generalise the concept of equality.
When you quotient out a set by an equivalence relation by taking the set of equivalence classes, the concept of equivalence in the bigger set _becomes_ the concept of equality in the quotient set:
if $`x\sim y` are equivalent, then the equivalence classes $`cl(x)` and $`cl(y)` are _equal_.

-- Every integer can be written as the _difference_ of two natural numbers.
-- For example, $`3=5-2` and $`-3=5-8`.
-- And, just like in the case of fractions, there is more than one way to do this (for example $`-3=5-8=6-9=7-10=\cdots`).

-- So let's start with pairs $`\N\times\N` of naturals, with the idea that the pair $`(a,b)` of naturals is supposed to represent the integer $`a-b`.
What should our equivalence relation be?
It is supposed to relate pairs $`(a,b)` and $`(c,d)` of naturals if they represent the same integer, that is, if $`a-b=c-d`.
But there is a big problem here: this argument is _circular_, because we haven't defined the integers or subtraction yet, so "$`a-b=c-d`" _doesn't make sense_ at this point.
Can we rewrite this equation in such a way that it doesn't mention subtraction?
Yes we can: adding $`b+d` to both sides turns the equation into $`a+d=b+c`, which makes perfect sense.
But is it an equivalence relation?

:::proposition "equiv_relation_integers"
The following  binary relation on $`\mathbb{N}\times\mathbb{N}`
$$`(a,b)\sim (c,d)\textrm{ if and only if } a+d=b+c`
is an equivalence relation.
:::

:::proof
Reflexivity: We have to show that $`(a,b)\sim (a,b)`.
By commutativity of addition we have immediately  $`a+b=b+a`, hence $`\sim` is reflexive.

Symmetry: Here we must show that if $`(a,b)\sim (c,d)`, then $`(c,d)\sim (a,b)`.
By definition, $`(a,b)\sim (c,d)` means the same as $`a+d=b+c`, and similarly $`(c,d)\sim (a,b)` if and only if $`c+b=d+a`.
So we need to show that $`a+d=b+c\implies c+b=d+a`.
This follows, because equality is symmetric and addition is commutative.


Transitivity: Assume that $`(a,b)\sim (c,d)` and $`(c,d)\sim (e,f)` or in other words $`a+d=b+c` and $`c+f=d+e`.
We want to show that $`a+f=b+e`.
Adding $`f` to both sides of the first identity, we deduce $`a+d+f=b+c+f`,
and using the second identity on the right hand side (and did you spot the use of associativity?) gives us $`a+d+f=b+d+e`.
Rearrange to get $`a+f+d=b+e+d`, and now using the cancellation law for addition ({theoremref "le_prereq"}[](1)) we deduce $`a+f=b+e`, which was what we had to prove.
:::

:::definition "def_integers"
The set of integers $`\mathbb{Z}` is the set of all equivalence classes for $`\N\times\N` under this equivalence relation.
:::

Note that we did not add any new axioms here, we just made definitions.

# Relationship with the naturals

We've defined the naturals $`\N` and the integers $`\Z`.
But can you see that the standard inclusion $`\N\subseteq \Z` is _not actually true_?
The natural number $`2` is just $`S(S(0))`, whereas the integer $`2` is a totally different object:
it is an infinite equivalence class $`\{(2,0),(3,1),(4,2),\ldots\}.`
However we really _want_ $`\N\subseteq \Z` to be true.
What to do about this?

Let's define a _function_ $`i` from $`\N` to $`\Z`, sending a natural number $`n` to the equivalence class of $`(n,0)`.

:::lemma "nat_coe"
The function $`i` is injective.
In other words, if $`x,y` are two natural numbers and $`i(x)=i(y)`, then $`x=y`.
:::

:::proof
Say $`x,y` are natural numbers, and $`i(x)=i(y)`.
Then by definition $`cl((x,0))=cl((y,0))`, which means that $`(x,0)\sim (y,0)`.
By definition this means that $`x+0=0+y`. Hence $`x=y`.
:::

Mathematicians often _identify_ $`\N` with its image $`i(\N)` in $`\Z` to avoid this problem.
This causes some formal subtleties, which are usually ignored.
We'll talk about some of these on the second problem sheet.

:::definition "int_numerals" (title := "The integers 0, 1, 2")
We define $`0\in\Z` to be $`i(0)` where that last $`0` is the natural $`0`,
we define $`1\in\Z` to be $`i(1)`, we define $`2\in\Z` to be $`i(2)`.
:::

{include 1 LectureNotes.Int.Arithmetic}

# Back to GCDs

In the section on naturals we defined the greatest common divisor of two naturals.
Here is another important fact about the greatest common divisor which can easily be proved by induction,
but only when you have subtraction available.

:::theorem "euclid2" (title := "Euclid revisited")
Let $`a` and $`b` be natural numbers.
There are integers $`\lambda` and $`\mu` such that $`gcd(a,b)=\lambda a+\mu b`.
:::

:::proof
We prove this by strong induction.
Let $`a` be a natural number, and suppose this is known for $`gcd(t,s)`, for all $`t<a`.
Now let $`b` be a natural number and consider $`gcd(a,b)`.

If $`a=0` then $`gcd(a,b)=b=0\cdot a+1\cdot b`.

Otherwise, by the inductive hypothesis,
there exist integers $`\lambda` and $`\mu` such that $`gcd(r_a(b),a)=\lambda r_a(b)+\mu a`.
Also, by {theoremref "quotrec_thm"}[](2),
the remainder $`r_a(b)` satisfies $`b=aq+r_a(b)` for some natural number $`q` (the "quotient").

We then have
$$`\begin{align*}gcd(a,b)&=gcd(r_a(b),a)\\
&=\lambda r_a(b)+\mu a\\
&=\lambda (b-aq)+\mu a\\
&=(\mu-q\lambda)a+\lambda b.
\end{align*}`
:::

We say that two natural numbers $`a` and $`b` are _coprime_ if $`gcd(a,b)=1`.
The following corollary is immediate from the theorem.

:::corollary "coprime"
If $`a` and $`b` are coprime, then there exist integers $`\lambda` and $`\mu` such that $`\lambda a+\mu b=1`.
:::

We use this result to prove a crucial fact about prime numbers.

# Primes and unique factorisation

We have already proved that every positive integer factors into primes.
But we have not yet proved that the factorisation is _unique_.
It can sometimes be hard to explain to people what the issue is here.
Let me attempt to do so. Say $`p<q<r<s` are prime numbers.
Say that you are _only_ allowed to use the definition of a prime number (that its only factors are 1 and itself).
How do you deduce from this that $`ps\neq qr`?
The problem is that $`ps` and $`qr` are both probably _bigger_ than $`p,q,r,s`,
so the definition of a prime number (which only tells you things about numbers _less_ than the prime) isn't much help.

The following crucial lemma gets us out of this mess.

:::theorem "prime2" (title := "Euclid's lemma")
If $`p` is prime and if $`a,b` are natural numbers, and if $`p\mid ab`, then $`p\mid a` or $`p\mid b`.
:::

See problem sheet 2 for a demonstration of how this and other ideas do not generalise away from primes.

:::proof
Assume $`p` is prime and $`p\mid ab`.
Let's assume the $`p\nmid a`, and we'll show that $`p\mid b`.

What can we say about $`gcd(p,a)`?
Certainly it divides $`p`, which means that it must be 1 or $`p`, because $`p` is prime.
But it can't be $`p` because $`p\nmid a`.
Hence it's 1.
Thus by {theoremref "coprime"}[] there exist integers $`\lambda` and $`\mu` such that $`\lambda a+\mu p=1`.
Multiplying both sides by $`b` we deduce $`\lambda ab + \mu p b=b`.
But $`p` divides $`ab` and hence $`p` divides the left hand side of this equality,
so $`p` divides the right hand side, which is $`b`.
:::

:::corollary "prime3"
If $`p` is prime and if $`a_1,a_2,\ldots,a_n` are natural numbers, and if $`p\mid a_1a_2\ldots a_n` then $`p` divides one of the $`a_i`.
:::

:::proof
Induction on $`n\geq1`.
The base case $`n=1` has $`p\mid a_1` as an assuption, so we're done.
For the inductive step assume that if $`p\mid a_1a_2\ldots a_n` then $`p` divides one of the $`a_i`,
and we have to deduce that if $`p\mid a_1a_2\ldots a_na_{n+1}=(a_1a_2\ldots a_n)a_{n+1}` then it divides one of the $`a_i`.
By Euclid's lemma ({theoremref "prime2"}[]) we know $`p` divides either $`a_1a_2\ldots a_n` or $`a_{n+1}`.
If $`p` divides $`a_{n+1}` we're done immediately, and if $`p` divides $`a_1a_2\ldots a_n` then we're done by the inductive hypothesis.
:::

:::theorem "nat_ufd" (title := "Uniqueness of prime factorisation")
Every positive integer is _uniquely_ the product of prime numbers, up to re-ordering.
:::

:::proof
We have already shown that every positive integer can be written as the product of primes in {theoremref "prime_factorisation"}[].
What is left to show that if
$`n=p_1p_2\ldots p_r=q_1q_2\ldots q_s`
with the $`p_i` and the $`q_j` all prime numbers,
then $`r=s` and after possibly re-ordering the $`q_i`, we have $`p_i=q_i` for all $`i`.

Let's prove this by strong induction on $`n`.
Suppose we have established this uniqueness result for all nonzero natural numbers smaller than $`n`.
Now let $`n=p_1p_2\ldots p_r=q_1q_2\ldots q_s` be two prime factorisations of $`n`.

By switching the $`p`'s and $`q`'s if necessary, we can assume $`r\leq s`.

If $`r=0` then $`p_1p_2\ldots p_r=1` (the product of no things is 1),
so $`n=1`, so $`q_1q_2\ldots q_s=1` meaning that $`s` must also be $`0` (because if $`s\geq1` then $`q_1q_2\ldots q_s>1`).
Therefore the $`r`-factorisation and the $`s`-factorisation are both empty, and so are equal.

If however $`r\geq1` then consider the last prime $`p_r` on the left hand side.
It divides $`p_1p_2\ldots p_r`, so it divides $`q_1q_2\ldots q_s`.
By {theoremref "prime3"}[], $`p_r` must divide one of the $`q_i`.
By rearranging the $`q_i` we can assume that it's $`q_s`.
But the only divisors of $`q_s` are 1 and $`q_s`, because $`q_s` is prime.
Hence $`p_r=q_s`, meaning that we can cancel and get $`p_1p_2\ldots p_{r-1}=q_1q_2\ldots q_{s-1}`.
This number is less than $`n`, so by the inductive hypothesis, its prime factorisation is unique;
it follows that its factorisations $`p_1p_2\ldots p_{r-1}` and $`q_1q_2\ldots q_{s-1}` agree up to re-ordering.

Therefore the factorisations $`p_1p_2\ldots p_{r}` and $`q_1q_2\ldots q_{s}` of $`n` also agree up to re-ordering.
:::


Something else we can do with subtraction is to prove that the quotient and remainder whose existence we proved in {theoremref "quotrec"}[] and {theoremref "quotrec_thm"}[] are unique!
In fact we can extend the quotient-remainder result to integers, as long as the integer we're dividing by is positive.

:::proposition "quotremint" (title := "quotient-remainder for integers")
If $`a` is an integer and $`b` is a positive integer, there exists integers $`q` and $`r` with $`0\leq r<b` and $`a=qb+r`.
:::
:::proof
See problem sheet 2.
:::
Note that $`b` is positive and the remainder $`r` is non-negative even if $`a` is negative.
For example if we divide $`-37` by $`10` using this method, we get $`q=-4` and $`r=3`.

:::theorem "quotrec2" (title := "uniqueness of quotient and remainder")
If $`a` is an integer, $`b` is a positive integer, and $`a=qb+r=q'b+r'` with $`0\leq r,r'<b` then $`q=q'` and $`r=r'`.
:::

:::proof
By swapping $`q,r` with $`q',r'` if necessary, we can assume $`r\leq r'`. Now subtracting the equations gives $`(q-q')b=r'-r`, so $`r'-r` is a multiple of $`b`.
But it's $`\geq 0` and $`<b`, so it can't be $`b\times S(x)` because this is $`bx+b\geq b` and hence too big.
So it must be $`b\times 0`, meaning $`r=r'`.
Hence $`qb=q'b` and because $`b\neq0` we deduce $`q=q'` from the fact that you can cancel multiplication by non-zero naturals
(this needs a proof: see problem sheets 1 and 2!)
:::

# Modular arithmetic

We will now give a short introduction to congruences of integers.
Here again the notion of equivalence relation is of vital importance.
Note that the notion of division extends easily to integers:
if $`x,y` are integers then we say $`x\mid y` if there exists an integer $`z` with $`y=xz`.

:::definition
Let $`a,b\in\mathbb{Z}` and $`n\in\mathbb{N},n>0`.
We say that $`a` is congruent to $`b` modulo $`n` if $`n\mid(a-b)`.\\
Notation: $`a\equiv b \mod n`.
:::

:::example
$`22\equiv 4 \mod 9`, since $`22-4=18`, and $`9\mid18`.
:::

:::proposition
Let $`a,b,c\in\mathbb{Z}` and $`n\in\mathbb{N},n>0`.
1. $`a\equiv a \mod n`, for all $`a\in \mathbb{Z}`.
2. If $`a\equiv b\mod n`, then $`b\equiv a\mod n`.
3. If $`a\equiv b\mod n` and $`b\equiv c\mod n`, then $`a\equiv c\mod n`.
:::

:::proof
1. $`a-a=0`, and $`n\mid0` for all $`n`, which yields the result.
2. $`b-a=-(a-b)`.
Hence since $`n\mid(a-b)`, then $`n\mid-(a-b)=b-a`.
3. If $`n\mid(a-b)` and $`n\mid(b-c)`, then $`n\mid(a-b)+(b-c)=a-c`, which by definition means that $`a\equiv c\mod n`.
:::
The last proposition exactly means that congruence modulo $`n` is an equivalence relation on $`\Z`.
We denote the equivalence class of $`a` by
$$`[a]_n:=\{b\in\mathbb{Z}\,:\,b\equiv a\mod n\}`
and we call it a _congruence class_.

For example, the congruence class $`[7]_{10}` is all the integers congruent to 7 mod 10, so it's $`\{\ldots,-23,-13,-3,7,17,27,37,\ldots\}`.

Here's a useful result.
:::proposition "prop_modulo_and_remainder"
Let $`a,b\in\mathbb{Z}` and $`n` a positive integer.
Then $`a\equiv b\mod n` if and only if $`a` and $`b` have the same remainder after division by $`n`.
:::
:::proof
Let $`a=qn+r` and $`b=q'n+r'` be the Euclidean division of $`a` and $`b` by $`n` with $`0\leq r,r'< n`.
Then we get immediately $`a-b=(q-q')n+(r-r')`.

Assume that $`a\equiv b\mod n`.
By definition $`n\mid(q-q')n+(r-r')`, therefore $`n\mid(r-r')`.
But $`0\leq r,r'< n`, therefore $`-n<r-r'<n` and the only multiple of $`n` in this range is $`0`.
Hence $`r=r'` and $`a` and $`b` have the same remainder after division by $`n`.

Conversely if $`r=r'`, then $`a-b=(q-q')n` and $`n\mid a-b` which by definition means exactly $`a\equiv b\mod n`.
:::
We want now to find out how many congruence classes exist modulo $`n`.
Let us look at it when $`n=1,2,3` to try to understand what is going on.

Note that $`1` divides every integer.
Hence if $`a` and $`b` are any integers then $`a\equiv b\mod 1`.
Hence there is only one congruence class modulo~1.
In other words
$`[0]_1=[1]_1=[2]_1=\dots=\mathbb{Z}.`

If $`n=2`, for any two integers $`a,b` such that $`a\equiv b\mod 2`, we have that $`a=2k+b`, which means that $`[a]_n=\{\dots,a-4,a-2,a,a+2,a+4\dots\}`, hence $`a` and $`b` have necessarily the same parity (they are either both odd or both even).
There are therefore two classes of integers modulo 2: the even numbers $`[0]_2=\{\ldots,-4,-2,0,2,4,\ldots\}` and the odd numbers $`[1]_2=\{\ldots,-5,-3,-1,1,3,5,\ldots\}`.
We have
$$`\cdots=[-2]_2=[0]_2=[2]_2=[4]_2\dots\textrm{ and } \cdots=[-1]_2=[1]_2=[3]_2=[5]_2=\dots`
so $`[a]=[a']` if and only if the integers $`a` and $`a'` are congruent mod $`n`.

If $`n=3`, we have $`a=3k+b` for some integers $`k` and this reduces to the three cases $`3k,3k+1,3k+2`.
Therefore we get three congruence classes modulo $`3`, i.e. $`[0]_3`, $`[1]_3` and $`[2]_3`.

We can recognize a pattern here.
In fact we can show the following result.
:::proposition
There are exactly $`n` congruence classes modulo $`n`.
:::
:::proof
We are first going to show that the equivalence classes $`[0]_n, [1]_n, ..., [n-1]_n` are all different.
Let $`a,b\in\mathbb{Z}`, $`0\leq a,b\leq n-1`.
Assume that $`[a]_n=[b]_n`.
Then $`n\mid a-b` by definition.
But this is impossible since $`-n<a-b<n` and the only multiple of $`n` in this range is $`0`, meaning $`a=b`.

Now we prove that these  are the only possible classes.
Again given any integer $`a`, consider the Euclidean division of $`a` by $`n` given by $`a=qn+r`, $`0\leq r <n`.
Obviously $`n\mid a-r` and consequently $`[a]_n=[r]_n`.
Therefore since $`0\leq r <n` any integer $`a` is congruent modulo $`n` to exactly one of the integers $`0,1,\dots n-1`,
which by our previous considerations are not congruent to each other.
:::
The last proposition means that every integer is congruent to exactly one of the numbers $`0,1,\ldots,n-1`,
so there are exactly $`n` equivalence classes.
We write
$`\mathbb{Z}/n\mathbb{Z} =: \{ [0]_n, [1]_n, ..., [n-1]_n\}`
for the set of equivalence classes modulo $`n`.
These are infinitely many new worlds of numbers, where, like the integers, we can do addition, subtraction and multiplication
(but still not division: you'll have to wait for the next chapter to see that).

From now on $`n` will be fixed, and we'll just write $`[a]` for $`[a]_n`.
We now want to define operations on this new set.
In order to do this we need the following
:::lemma (title := "pre-addition and pre-multiplication for integers mod n")
Suppose that $`a, a', b, b'\in \mathbb{Z}` are integers such that $`a\equiv a'\mod n` and $`b\equiv b'\mod n`. Then
1. $`a+b\equiv a'+b'\mod n`;
2. $`ab\equiv a'b'\mod n`.
:::
:::proof
Exercise! See problem sheet 2.
:::
This lemma means that if we choose integers $`a` and $`b` and calculate $`a+b` or $`ab`,
and then you choose two other representatives $`a'\in [a]` and $`b'\in [b]` and calculate $`a'+b'` or $`a'b'` we get the same element of $`\mathbb{Z}/n\mathbb{Z}`.
This is the same idea we used to define the addition and multiplication on the integers:
we needed our operation to be independent of the elements of the class.
We can therefore define the following well-defined addition and multiplication on $`\mathbb{Z}/n\mathbb{Z}`:
$$`\begin{align*}
&+:\mathbb{Z}/n\mathbb{Z}\times\mathbb{Z}/n\mathbb{Z}\rightarrow\mathbb{Z}/n\mathbb{Z}, &&([a]_n,[b]_n)\mapsto [a+b]_n\\
&\times:\mathbb{Z}/n\mathbb{Z}\times\mathbb{Z}/n\mathbb{Z}\rightarrow\mathbb{Z}/n\mathbb{Z}, &&([a]_n,[b]_n)\mapsto [ab]_n.
\end{align*}`
We can now ask all the usual questions:
whether $`(x+y)+z=x+(y+z)` and $`x(y+z)=xy+xz` and so on for this new world of numbers;
the answer is that again all these things are true, and not hard to prove,
but let us leave this for now because I want to talk about division.
