/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/

import LectureNotes.Formatting

set_option autoImplicit false
set_option pp.rawOnError true

open Verso.Genre Manual

#doc (Manual) "Fields and ordered fields"  =>

The rationals are a _field_.
They are equipped with $`0`, $`1`, $`+`, $`-` and $`\times`, and satisfy all of the field axioms in the previous section ({theoremref "field_def"}[]).
In clearer but vaguer terms, a field is any number system with $`+,-,\times,/` which satisfies all the usual rules for these symbols.
Using the rationals, we can make some more fields; in this section we say something about how.

# The reals and complexes

In this last section of Part II, we want to talk about the real and complex numbers.
Let's start with the reals.
The ancient Greeks thought that the concepts of "length" (a positive real number) and "fraction" (a positive rational number) were the same thing.
This idea was destroyed by Pythagoras' theorem, which shows that the diagonal of a unit square is definitely a length, but its square is 2 so it cannot be a rational.
In case you haven't seen a careful proof that there's no rational number whose square is 2, we include it here:

:::lemma
There is no rational number whose square is $`2`.
:::

:::proof
Assume that there exists $`p` and $`q` in $`\mathbb{Z}` with $`q\not=0` and such that $`(p/q)^2=2`.
Cancelling out common factors of 2, we can assume without loss of generality that at least one of $`p` and $`q` is odd.
Now clearing denominators gives $`p^2=2q^2` which means that $`2 \mid p^2` and consequently $`2 \mid p` as we proved on problem sheet 0.
But then $`4 \mid p^2` and consequently $`2 \mid q^2`.
Again this yields $`2 \mid q`.
This is a contradiction to the fact that at least one of $`p,q` have to be odd.
:::


-- We worked hard in the integer section to prove that every positive integer is uniquely the product of prime numbers.
-- It is not difficult to check that $`2` is prime (because the only naturals smaller than it are $`1` and $`0`), and using this we can give a different and shorter proof of the nonexistence of a rational number $`p/q` whose square is 2.
-- Define the _2-adic valuation_ $`v(n)` of a positive integer $`n` to be the largest power of 2 which divides $`n`, so, for example, $`v(40)=3` because $`24=2^3\times5`.
-- Using the fact that numbers factor uniquely into primes it's easy to check that $`v(ab)=v(a)+v(b)`.
-- So a second proof that there is no rational whose square is 2, is that if $`p^2=2q^2` then taking valuations shows us that $`2v(p)=1+2v(q)`.
-- However a number cannot be both even and odd (as you will know if you have played even/odd world in the natural number game $`\ldots`).

-- Whatever way you look at it,
Pythagoras' theorem tells us that there is definitely a _length_ whose square is 2 (the diagonal of a unit square),
but the above argument shows that there is no rational whose square is 2.
Hence the rationals are not a good model for the concept of length: there must be many tiny holes in the rationals and we need to invent new numbers to fill these holes.

:::definition "real_def" (title := "Real numbers")
The real numbers are defined to be the _completion_ of the rationals.
:::

I am not going to tell you what this means; you will learn this concept later (perhaps in Analysis 1, a module which starts when IUM has finished).
The details typically involve equivalence relations again, and I think we've seen quite enough of those for now.

:::theorem "real_field" (title := "The reals are a field")
The real numbers are a field.
:::

In other words, they satisfy that huge list of axioms in {theoremref "field_def"}[].
We did not give the details of the definition of the real numbers though, so we cannot prove this theorem.
We will just _assume_ it, like you have been assuming it in school.
Here are some more theorems which we cannot prove for the same reason.

:::theorem (title := "Structure on the real numbers")
There is an injective map from $`\mathbb{Q}` to $`\R`, preserving addition, subtraction, multiplication, division, and $`\leq`.
:::

:::theorem (title := "Interplay between algebra and ordering")
* If $`x,y,z` are real numbers and $`x\leq y`, then $`x+z\leq y+z`.
* If $`x,y` are real numbers and $`0\leq x` and $`0\leq y` then $`0\leq xy`.
:::

If you believe in the real numbers, then defining the complex numbers is easy.

:::definition "complex_def" (title := "Complex numbers")
  The complex numbers are defined to be $`\R\times\R`.
:::

In other words, a complex number is just _defined_ to be a pair of real numbers.

*Exercise:* Assume in this exercise that the real numbers are a commutative ring.
If we define addition of complex numbers to be addition of vectors, so $`(p,q)+(r,s)=(p+r,q+s)`,
and if we define multiplication by $`(p,q)\times(r,s)=(pr-qs,ps+qr)`, and if we define $`0` to be $`(0,0)` and $`1` to be $`(1,0)`,
then show that the complex numbers form a commutative ring.
Note: this exercise is long and boring.
Don't do it.
Instead just check one of the axioms.
I think the hardest one is associativity of multiplication, so try that one.

A trickier exercise is to prove that the complex numbers are a field.
The main issue is figuring out how to define reciprocals.

# More examples of fields

We've seen three examples of fields.
But actually we have seen a few more in this course.
The integers modulo $`m` (recall that this is the set whose elements are equivalence classes of integers for the equivalence relation $`a\sim b\iff a\equiv b \mod m`)
are also all commutative rings, and (perhaps surprisingly) if $`m` is prime then they are all fields.
Let's do the example of $`m=2`.

:::example
Let $`\mathbb{F}_2=\{0,1\}` be a set with two elements, together with addition and multiplication defined by
$$`0+0=0,\, 0+1=1+0=1,\,1+1=0,\quad 0\cdot 0=0,\, 0\cdot 1=1\cdot 0=0,\, 1\cdot 1=1.`
We define negation by $`-0=0` and $`-1=1`, and we define reciprocal by $`1^{-1}=1`.
Choose one random axiom for a field (for example commutativity of multiplication) and check it for this example (by checking all cases).
:::

# Arithmetic in fields

We are going to prove some theorems which are valid in _all fields_. So this is like the natural number game again -- we have a list of axioms (the axioms for a field, all of which look ``standard'') and we want to now prove a whole bunch of other ``standard'' things. The advantage of doing it this way is that then we'll know that these facts apply to _all_ fields, not just to fields you already know, such as the real numbers.

:::theorem (title := "Cancellation law for addition")
Let $`\mathbb{F}` be a field and say $`x,y,t\in\mathbb{F}`. If $`x+t=y+t`, then $`x=y`.
:::

:::proof
Suppose that $`x+t=y+t`.
Adding $`-t` to both sides, we deduce $`(x+t)+(-t)=(y+t)+(-t)`.

Now use associativity of addition twice to deduce that $`x+(t+(-t))=y+(t+(-t))`.
Now use the axiom of additive inverses twice to deduce that $`x+0=y+0`.

Finally use the axiom of additive identity twice to deduce that $`x=y`, and we're done.
:::

Here's something else which looks standard, is not one of the axioms of a field, but which can be deduced from the axioms.

:::lemma (title := "Negation is involutive")
If $`\mathbb{F}` is a field and $`x\in F`, then $`-(-x)=x`.
:::

:::proof
Applying the axiom of additive inverses to $`x` tells us that $`x+(-x)=0`.
Applying it to $`-x` tells us that $`-(-x)+(-x)=0`.
Hence $`x+(-x)=-(-x)+(-x)`, and now by the cancellation law for addition, we deduce $`x=-(-x)`.
:::


Here's another example.
:::lemma
Let $`\mathbb{F}` be a field, $`x\in\mathbb{F}`. Then $`x\times 0=0.`
:::

:::proof
By the axiom of additive identity, $`0+0=0`.
Multiplying both sides by $`x` we deduce that $`x\times(0+0)=x\times 0`.
Using the axiom of distributivity, the left hand side is $`x\times 0 + x \times 0`.
Using the axiom of additive identity on the right hand, we deduce $`x\times 0 + x\times 0 = 0 + x\times 0`.
And now by the cancellation law for addition we deduce that $`x \times 0 = 0`.
:::

There are more of these on the problem sheet.

# Ordered fields

:::definition "ordered-field" (title := "Ordered field")
An _ordered field_ is a field  $`\mathbb{F}` together with a total order $`\leq` such that additionally if $`x,y,t\in\mathbb{F}` with $`x\leq y` then
1. $`x+t\leq y+t`; (relationship between $`\leq` and $`+`)
2. and if moreover $`t\geq 0` then $`x\times t\leq y\times t`. (relationship between $`\leq` and $`\times`).
:::

Recall that a _total_ order is an ordering satisfying reflexivity, antisymmetry and transitivity, and also totality:
if $`x,y\in\mathbb{F}` then either $`x\leq y` or $`y\leq x`.

Both the rationals and the reals are ordered fields.
However it is known that it is impossible to put an ordering on the complexes making it into an ordered field;
this was one of the questions on a Logic and Sets problem sheet.

Again from these axioms we can prove all the usual rules that we know about inequalities. Again I will do some examples and then put some on the problem sheet.
:::proposition
Let $`\mathbb{F}` be an ordered field, and say $`x\in\mathbb{F}`. Then $`0\leq x` if and only if $`-x\leq 0`, and $`x\leq 0` if and only if $`0\leq -x`.
:::

:::proof
Say $`0\leq x`.
We can add $`-x` to both sides by the axiom relating $`\leq` to $`+`.
We deduce that $`0+(-x)\leq x+(-x)`.
Now applying the axiom of additive identity and the axiom of additive inverse we deduce $`-x\leq 0`.

Now say $`-x\leq 0`.
Adding $`x` to both sides preserves the inequality by the axiom relating $`\leq` to $`+`, and again using additive identity and additive inverse we deduce $`0\leq x`.

The second claim comes for free by applying the first claim to $`-x` and using the fact that $`-(-x)=x`, which we already proved above.
:::

As I've mentioned, $`\mathbb{Q}` is an example of an ordered field, which means that despite having seen a lot of axioms,
they are still not enough to _characterise_ the reals.
We will need to add something which is called the axiom of completeness in order to define them uniquely.


# Axiom of completeness

The natural numbers are uniquely determined by Peano's axioms.
However the real numbers are clearly _not_ uniquely determined by the axioms of an ordered field,
because the rational numbers also satisfy these axioms.

We finish Part 2 with an explanation of one last axiom, the _completeness axiom_.
It turns out that, up to a subtle concept of equality called _isomorphism_, the real numbers are the _only_ complete ordered field.

We're going to develop the a little of the theory of totally ordered sets to explain this axiom.
A totally ordered set is a set $`X` equipped with a total order $`\leq`.
Recall that this means that the order is reflexive $`(x\leq x`), antisymmetric ($`x\leq y` and $`y\leq x` implies $`x=y`), transitive ($`x\leq y` and $`y\leq z` implies $`x\leq z`), and _total_ (for all $`x` and $`y`, either $`x\leq y` or $`y\leq x`). Given $`a` and $`b` in a totally ordered set, we define $`a<b` to mean $`a\leq b` and $`a\ne b`, we define $`a\geq b` to mean $`b\leq a` and we define $`a>b` to mean $`b<a`. Now let's learn about _bounds_ in such sets.

:::definition
Let $`X` be a totally ordered set.
* A subset $`S\subseteq X`  is called _bounded above_ if there is an element $`B\in X` such that $`\forall x\in S, x \leq B`.
* If $`S` is bounded above, then any $`B\in X` such that $`\forall x\in S, x\leq B` is called an _upper bound_ for $`S`.
:::

Exercise: guess the definitions of what it means for a subset $`S\subseteq X` to be _bounded below_,
and what it means for an element of $`X` to be a _lower bound_ for $`S`.

Now let $`X` be the real numbers.
Here are some examples of subsets of $`X` and now they relate to the above ideas.

The subset $`S=\{1,2,3\}` is bounded above,
and an upper bound for $`S` is the number $`37`.
This is because $`1\leq 37`, $`2\leq 37` and $`3\leq 37`.
Another upper bound for this set is $`3`; note that $`3` is actually _in the set_, but upper bounds don't have to be in the set.
$`S` is also bounded below, by $`-3.1415926535\ldots` for example.
Note in particular that sets can have many upper and lower bounds.

The subset $`S=\{0,1,2,3,4,\ldots\}` is not bounded above.
However the subset $`S=\{0,-1,-2,-3,\ldots\}` is bounded above, and again $`37` is an upper bound.
This example shows you that sets can be bounded above but not bounded below.

The subset of negative reals $`S=\{x\in\R\,:\,x<0\}` is bounded above (by $`37` for example, or by $`0`).
But in contrast to the previous examples, even though $`S` is bounded above, there is no _element of $`S`_ which is an upper bound.
This is in contrast to $`S=\{1,2,3\}`, which had an upper bound 3 which was in $`S`.

Exercise: prove that if $`S` is the negative reals, then no element of $`S` is an upper bound for $`S`.

:::definition "completeness" (title := "Least upper bound")
Let $`X` be a totally ordered set and let $`S\subset X` be a subset.
We say that an element $`L\in X` is a _least upper bound_ for $`S` if
1. $`L` is an upper bound for $`S`;
2.  if $`x<L` then $`x` is _not_ an upper bound for $`S`.
:::

This new notion will allow us to explain the concept which captures the real numbers completely.
:::definition (title := "Completeness")
A totally ordered set $`X` is said to be _complete_ if every nonempty bounded-above subset of $`X` has a least upper bound.
:::

This is the very important property which distinguishes $`\mathbb{R}` from the set $`\mathbb{Q}` of rational numbers.
We cannot prove that the real numbers are complete, because although we said that the real numbers were "the completion" of the rational numbers we gave no indication on how to complete a field.
However, linguistically it should not be surprising that a completion is complete.
We record this as a theorem, even though we cannot prove it here.

:::theorem (title := "The reals are complete")
  The reals are a complete ordered field.
:::

The rational numbers themselves are not complete however: they have "holes in".
For example the subset $`\{x\in\mathbb{Q}\,|\,x^2<2\}\subset \mathbb{Q}` is bounded above (by, for example, the rational numbers $`1.5`, $`1.42`, $`1.415`, $`\ldots`) but it does not have a _least_ upper bound in the rationals,
because (after quite some effort) one can check that a least upper bound for this set would have square equal to 2, and there is no rational number whose square is 2.

Another important theorem, which again we will not prove, is this:

:::theorem (title := "Uniqueness of the reals")
If $`\mathbb{F}` is any ordered field which satisfies the completeness axiom, then $`\mathbb{F}` bijects with the real numbers in a way which preserves $`0`, $`1`, $`+`, $`-`, $`\times`, $`(\cdot)^{-1}` and $`\leq`.
:::

We cannot prove any of these theorems because we have not given a rigorous definition of the real numbers.

To understand the importance of the axiom of completeness we are going to look several applications.
The first (and maybe most important) consequence of this last axiom is called the Archimedean
property or sometimes the axiom of Eudoxus. It basically states that the natural numbers are not bounded above in $`\mathbb{R}`. This property, which you will use extensively in analysis may seem obvious, but in fact there are other ordered fields than the reals in which it does not hold.
:::proposition (title := "Archimedean Property")
For all $`x\in\mathbb{R}`, there exists an $`n\in\mathbb{N}`, such that $`x<n`.
:::

:::proof
We prove it by contradiction.
Assume that we've managed to find a real number $`x` such that $`x\geq n` for every natural number $`n`.
This means that $`\N\subseteq\R` is bounded above.
By the completeness axiom, $`\N` must then have a least upper bound $`B`.
Now consider $`B-1`.
This is less than $`B`, and $`B` is the least upper bound for $`\N`, so $`B-1` cannot be an upper bound for $`\N`.
This means that there must exist some natural $`n` with $`n>B-1`.
Adding 1 to both sides we deduce $`n+1>B`.
But this contradicts the fact that $`B` is an upper bound for the naturals.
:::

There are several equivalent forms of the Archimedean property that are useful
in different contexts and which we state in the following immediate corollary.
Especially, you will encounter the second formulation very often when you study convergence properties of sequences for example.
:::corollary
1. For all $`x,y\in\mathbb{R}`, if $`x>0` there exists an $`n\in\mathbb{N}` such that $`nx>y`.
2. For all $`x\in\mathbb{R}`, $`x>0` there exists an $`n\in\mathbb{N}` such that $`0<\frac{1}{n}<x`.
:::
The following result is another nice consequence.
:::lemma "lemma_for_density"
Let $`x\in\mathbb{R}`, $`x\geq 0`. Then there exists some $`n\in\mathbb{N}` such that $`n\leq x<n+1`.
:::

:::proof
Consider the set $`S=\{m\in\mathbb{N}|x<m\}`, and note that $`0\not\in S` by our assumption on $`x`.
By the Archimedean property we know that $`S` is non empty.
Hence by the well-ordering principle, {theoremref "nat_wf"}[], we know that $`S` has a smallest element.
This element cannot be $`0` and hence it's $`n+1` for some natural number $`n`.
Because $`n+1` is in $`S` we have $`x<n+1`.
Moreover, becaue $`n<n+1` and $`n+1` is the smallest element of $`S`, we must have $`n\not\in S` and hence $`n\leq x`.
:::
The natural number $`n` is called the _floor_ of $`x`.
If you allow negative real numbers then they still have floors, but these are integers rather than naturals.

Another important consequence of the completeness axiom is the following fact.
:::proposition "density" (title := "Rationals are dense in the reals")
For all $`x,y\in\mathbb{R}` such that $`x<y`, then there exists a number $`r\in\mathbb{Q}` such that $`x<r<y`.
:::
:::proof
We will go through the proof of this on the problem sheet.
:::
