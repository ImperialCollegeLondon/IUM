/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/

import LectureNotes.Nat.AdditionDef
import LectureNotes.Nat.AdditionProperties
import LectureNotes.Nat.ConsequencesNoConfusion
import LectureNotes.Nat.LE
import LectureNotes.Formatting

set_option autoImplicit false
set_option pp.rawOnError true

open Verso.Genre Manual

#doc (Manual) "Natural numbers"  =>

The natural numbers are as old as mankind.
But it's really with the work of Dedekind and finally Peano in 1889,
that they were described axiomatically.
Let’s take a look at a modern version of Peano’s axioms.

# Peano axioms

In this section, we will uniquely characterise the natural numbers by axioms.
Informally, what we are trying to _model_ with these axioms is the infinite set
$$`\mathbb{N}=\{0,1,2,3,4,\ldots\}`
of _natural numbers_.
Some other lecturers will use the convention that $`\mathbb{N}=\{1,2,3,4,\ldots\}` starts at 1,
and historically Peano actually started with 1,
but for the material we present here it is much more convenient to start with 0, so we shall start with 0.

Infinity gives rise to lots of paradoxes;
the problem with the above definition is that it is unclear what that ". . ." in the equation above really _means_.
Let us give a slightly more formal definition of $`\mathbb{N}`, in terms of three axioms.

:::axiom "peanov1" (title := "Peano axioms, first version")
The natural numbers $`\mathbb{N}` are defined via the following three axioms.
* $`0` is a natural number.
* If $`n` is a natural number, then its successor $`S(n)` is a natural number.
* That’s it.
:::

The _successor_ of a natural number is the number which comes after it.
For example the successor of 37 is 38.
"That’s it" means "$`0` and successors are the only ways to make natural numbers".
We will be more precise about this later; we do not need the third axiom for the moment.

You might be thinking "why do we talk about $`S(n)`? Why don’t we just say that $`S(n)` is $`n + 1`?"
Unfortunately this would be a _circular argument_, and those are not allowed in mathematics.
We _have not yet defined addition_ on the natural numbers,
and the definition of addition will _use_ the successor function,
so the definition of the successor function cannot use addition.
If you think that it is surprising to introduce this funny function $`S : \mathbb{N} \to \mathbb{N}` before addition,
then think back to the way very small children are taught about numbers:
before they learn to add, they learn to count.
The successor function is telling you how to count.

# Our first numbers

Forget the third axiom: let's think about the first two.
Which numbers can we make from them?
The first axiom only gives us $`0`.
But applying the second axiom gives us new numbers $`S(0)` (the number after $`0`), $`S(S(0))` (the number after the number after $`0`) and so on.
New numbers have just been born: let's give them names.

:::definition "1234" (title := "One, two, three, four")
We define $`1` to be $`S(0)`,
we define $`2` to be $`S(1)`,
we define $`3` to be $`S(2)` and we define $`4` to be $`S(3)`.
:::

Summary: So far we have numbers $`0,1,2,3,4`, a function $`S`, and _nothing else_.
No addition, no multiplication, and no $`\leq`.
We still have a lot of work to do before numbers become the mathematical object which we are all familiar with.

# More on "That's it"

Now we have defined $`2` and $`4`, can we prove that $`2+2=4`?
Unfortunately we cannot, because we have not yet defined addition!
Let's work towards this now.
Let's fix a natural number like $`37`,
and discuss how to define the function which adds $`37` to a number, i.e., the function $`f(x)=37+x`.
I stress again: addition does _not yet exist_ in our theory --
we have to _make_ it, and this is what we will do now.
More generally, for a fixed number $`a` we will have to define the function sending $`x` to $`a+x`.

To define addition, we have say more precisely what the final axiom "that's it" means.
Let us give a slightly more precise explanation of this axiom.

:::axiom "thatsitv2" (title := "That's it, version 2")
If you want to do something (for example define something, or prove something) for _all_ natural numbers,
then you only need to do the following two things:
* Do it for $`0`.
* Do it for $`S(n)`, assuming you've already done it for $`n.`
:::

The point of "That's it" is that it is saying that $`0` and $`S` are the _only ways to make natural numbers_,
so if you want to do something for all natural numbers,
then it suffices to do it in the $`0` case and do it in the $`S(n)` case.
Let's now define addition.

{include 1 LectureNotes.Nat.AdditionDef}

{include 1 LectureNotes.Nat.AdditionProperties}

# Recursion

I have told you one aspect of "that's it" -- it encodes the principle of mathematical induction.
But in fact the full formal definition of "that's it" is both the principle of induction and the principle of recursion, which we now state in its most general form.
This definition is non-examinable.

:::axiom "rec" (title := "Principle of mathematical recursion")
Say we have a set $`X`.
You can make a function $`F` which sends a natural number $`n` to an element of the set $`X` by doing the following two things:
* Define the element $`F(0)\in X`;
* Define a function $`p_n` from $`X` to $`X`, and define $`F(S(n))` to be $`p_n(F(n))`.
:::

In many applications, all the $`p_n` are equal.
For example, when we defined $`F(x)=a+x` above, we let the set $`X` be $`\N`, we let all the $`p_n` be $`S:\N\to\N`, and we defined $`F(0)=a`.
Informally, adding $`x` to a number $`a` is defined by "start at $`a`, and then repeatedly take the successor $`x` times".
But don't write this in an exam, because $`x` is a _formal term in a formal system_, and "doing something $`x` times" makes no sense in this formal system.
In particular, trying to define $`a+x` as $`\underbrace{S(S(S(\ldots S}_{x\ \text{times}}(a)))\ldots)` is _not allowed_,
because it is not at all clear what $`\ldots` _means_;
it is attempting to attach an intuitive semantic meaning to a formal term in a formal language. But intuition is exactly what is not allowed here:
if you want to do something $`x` times, you must use induction or recursion.

# Multiplication

Subtraction is a problem on the natural numbers -- if the only numbers available to us are $`\{0,1,2,3,\ldots\}` then we cannot define $`2-5` correctly.
So let's leave subtraction until later on when we have negative integers,
and now define multiplication, which will work fine.
We use both notations $`a\times x` and $`ax` for multiplication.

:::definition "mul" (title := "Multiplication")
Fix a natural number $`a`.
The function $`F(x)=a\times x` is defined by the following two rules:
* $`a\times 0=0;`
* $`a\times S(n)=a\times n + a.`
:::

Like addition, we're defining the $`F(x)` by saying what it does to $`0`, and also what it does to $`S(n)` assuming we know what it does to $`n`.
By "that's it" (or more formally "by recursion"), this is a valid way to define multiplication.

\[Note: A fully formal justification that this is a valid definition of the function $`F(x)=ax` would use the principle of recursion above,
with the sets $`X` defined to be $`\N`, with $`x_0=0` and $`p_n(m)=m+a`.
In short, to multiply a general number $`x` by $`a`, you "start at $`0`, and then repeatedly add $`a`, $`x` times".\]

Just like addition, we now have a lot of work to do, in order to prove all the basic properties of multiplication which we know and love.

-- Basic facts about multiplication
:::proposition (title := "Basic facts about multiplication")
Let $`x,y,z\in\mathbb{N}`. Then
* $`x\times 1=x;`
* $`0\times x=0`;
* $`S(x)y=xy+y`;
* $`xy=yx`;
* $`1\times x=x`;
* $`x(y+z)=xy+xz`;
* $`(x+y)z=xz+yz`;
* $`(xy)z=x(yz)`.
:::

The order above is the recommended order for proving the above results.
Proving this proposition is the first question on the first IUM Numbers problem sheet.

# Peano's remaining axioms

Earlier on we proved $`1+1=2`, but can we also prove that $`1+1=3`?
This would be easy to prove if $`3=2`, but $`3=2` looks a bit suspicious.
However, can we rule out $`3=2` _using only the axioms_?
It is amusing to note that we were able to prove lots of theorems about addition and multiplication without ever worrying about this issue.

In Peano's original paper, he add two extra axioms to the system in order to make this easy.

* If $`x` is a natural number, then $`S(x)\not=0.`
* If $`x` and $`y` are natural numbers and $`S(x)=S(y)`, then $`x=y`.

The first of these axioms says that if you keep applying $`S` then you will never end up back at $`0`, and the second axiom says that $`S` is an _injective_ function.
Put together, these two axioms guarantee that if we keep applying the $`S` function then it will never output a number which we've seen before ("counting doesn't loop").
Let's use Peano's extra axioms to show that $`3\not=2`.

:::theorem
$`3\not=2.`
:::

:::proof
We prove this by contradiction.
Let's assume $`3=2`.
Writing $`2=S(1)` and $`3=S(2)` (remember that those are the _definitions_ of $`3` and $`2`),
we deduce $`S(2)=S(1)` and hence by the second extra axiom we deduce $`2=1`, or in other words $`S(1)=S(0)`.
Applying this axiom again we deduce that $`1=0` or in other words $`S(0)=0`.
But this contradicts the first extra axiom (set $`x=0`).
:::

However, using the more modern approach explained in these notes,
it is possible to _prove_ these two extra axioms of Peano -- we don't need them after all.
So for us they are _theorems_, not _axioms_.

:::theorem (title := "Peano's extra axioms")
* If $`x` is a natural number, then $`S(x)\not=0.`
* If $`x` and $`y` are natural numbers and $`S(x)=S(y)`, then $`x=y`.
:::

This proof is non-examinable.

:::proof
Let's use the axiom of recursion ("that's it") to define two new temporary functions.
First let's define a function $`Z` from the natural numbers to the set $`\{{\tt true},{\tt false}\}` by recursion.
It's called $`Z` because it detects whether a number is zero.

Set $`Z(0)={\tt true}`, and if we have already defined $`Z(n)` then let's define $`Z(S(n))` by ignoring what the value of $`Z(n)` was and just setting $`Z(S(n))` to be always `false`.
The upshot of this definition is that we have a function which sends $`0` to `true` and everything else to `false`.

Now it is easy to prove the first of Peano's extra axioms $`S(x)\neq0` by contradiction:
if $`S(x)=0` for some $`x`, then applying $`Z` to both sides we deduce that $`{\tt false}={\tt true}`,
which is the contradiction we seek.

To prove the second axiom,
let's define a "predecessor" function $`P(x)` which subtracts 1 from a number.
There is a problem with $`0` though, because $`0-1` is not a natural number, so we'll have to define $`P(0)` to be something else.
Fortunately our proof will never involve looking at $`P(0)`,
so we can just define it to be anything we like.
Formally then, let's define a function $`P` from the naturals to the naturals by recursion:
we will define $`P(0)` to be $`37`,
and if we have already defined $`P(n)` then let's define $`P(S(n))` by forgetting all about $`P(n)` and just setting $`P(S(n))=n`.

Now $`P(0)` is a bit weird, but $`P(S(n))=n`,
and this is exactly what we need to prove Peano's second extra axiom (injectivity of $`S`).
Indeed, if $`x` and $`y` are natural numbers and $`S(x)=S(y)`,
then applying $`P` we deduce $`P(S(x))=P(S(y))` and hence $`x=y`, which is what we require.
We conclude that Peano's extra axioms can be proved from the three axioms we assumed at the beginning.

:::

We saw some slightly odd uses of recursion in the proof above;
here's a slightly odd use of induction.

:::theorem "zero_or_succ"
Every natural number $`x` is either $`0` or the successor of some other natural number.
:::

This proof is non-examinable too.

:::proof
Induction on $`x`.
The base case has $`x=0` which is zero.
For the inductive step we set $`x=S(n)` and we know that the result is true for $`n`.
We can ignore the inductive hypothesis though, and conclude because $`x=S(n)` is a successor.
:::

{include 1 LectureNotes.Nat.ConsequencesNoConfusion}

{include 1 LectureNotes.Nat.LE}

# Variants of the induction principle

Now we know about $`\leq` we can state and prove some variants of the principle of mathematical induction.
The first is an easy one: you don't have to start at zero.
What I mean by this is: if you have some fixed "base" natural number $`k`, and true-false statements $`Q_k`, $`Q_{k+1}`, $`Q_{k+2}`, $`\ldots`,
then to prove them all it suffices to prove the base case $`Q_k` and the inductive step that for all $`n\geq k`, $`Q_n` implies $`Q_{n+1}`.
How do we prove that this is valid?
Simple: just define $`P_n` to be $`Q_{k+n}` and apply the usual induction principle to the $`P_n`.

A more subtle variant is _strong induction_.
Again we have statements $`P_0`, $`P_1`, $`P_2`, $`\ldots`,
and we want to prove all of them.
Strong induction relies crucially on the concept of $`<`,
which we haven't talked about yet and which we develop the theory of in the first Numbers example sheet.
So let's define $`x<y` to mean $`S(x)\leq y`, and then we can state the principle of strong induction.

:::theorem "strong_induction" (title := "The principle of strong induction")

Say $`P_0`, $`P_1`, $`P_2`, $`\ldots` are infinitely many true-false statements.
To prove that all of them are true, it suffices to prove the following statement:

(\*) For every $`n`, you can deduce $`P_n` if you assume $`P_t` for all $`t<n`.
:::

:::proof
Let's define infinitely many new true-false statements $`Q_n` by $`Q_n=P_0\land P_1\land\ldots\land P_n`.
This definition is no good because we used $`\ldots`,
but we can define $`Q_n` properly by recursion:
we define $`Q_0` to be $`P_0`, and if we've defined $`Q_n` already then we define $`Q_{S(n)}` to be $`Q_n\land P_{S(n)}`.

Exercise: check that $`Q_2` is $`(P_0\land P_1)\land P_2`.

We now prove $`Q_n` by induction on $`n`.
To do the base case we use (\*) with $`n=0`;
this says that you can deduce $`P_0` from no hypotheses at all, so in particular $`P_0` must be true, and hence $`Q_0` is true.

To do the inductive step, we assume $`Q_n` and we need to deduce $`Q_{S(n)}`.
Now if $`Q_n=P_0\land P_1\land \ldots P_n` is true then $`P_t` is true for all $`t<S(n)`,
so by (\*) applied at $`S(n)` we deduce that $`P_{S(n)}` is true.
Hence $`Q_{S(n)}=Q_n\land P_{S(n)}` is true.

Hence $`Q_n` is true for all $`n`.
But it is easy to check that $`Q_n\implies P_n` for all $`n` (check the $`0` and successor cases separately), and hence $`P_n` is true for all $`n`.
:::

Variants of induction have associated variants of recursion.
For example, here is a _strong recursion_ principle,
analogous to strong induction
in the same way that the recursion principle ({theoremref "rec"}[]) is analogous to induction.
This statement is non-examinable, and we will also skip the proof.

:::definition "strong_rec" (title := "Strong recursion")
Say we have a set $`X`.
You can make a function $`F` which sends a natural number $`n` to an element of the set $`X` by providing the following thing:

(\*) For every $`n`, a function $`p_n` from $`X^{\{t\in\N\mid t<n\}}` to $`X`.

The resulting function $`F` will have the property that $`F(S(n))` is equal to $`p_n(\left.F\right\rvert_{\{t\in\N\mid t<n\}})`.
:::

This says that it is safe to define a function from $`\N` to a set $`X` by a recursive formula in which $`F(n)` depends on any or all previous values of $`F`.

Using strong induction we can deduce that the naturals are _well-ordered_,
meaning that if a set of naturals has one or more elements, then it has a smallest element.
Before we embark on this, you might want to think about the following exercise, which shows you "the point" of being well-ordered.

_Exercise:_ This section is about the non-negative integers.
But assume temporarily that we have already created the non-negative real numbers and all the usual properties we know about them are true.
Show that the non-negative real numbers are _not_ well-ordered, by proving that the set of positive real numbers is a nonempty set with no smallest element.

:::theorem "nat_wf" (title := "Well-ordering principle")
Every non-empty set $`A\subseteq\mathbb{N}` of natural numbers has a least element, i.e., there exists a number $`a\in A`, such that for every $`x\in A` we have $`a\leq x`.
:::

:::proof
We will prove this by contradiction.
Let $`A\subseteq\mathbb{N}` be a set, and assume that it has no least element;
we'll show that $`A` is empty.
If $`n` is a natural number, define $`P_n` to be the true-false statement "$`n\not\in A`".
Let's prove that $`P_n` is true for all $`n`;
this is enough, as it shows that $`A` has no elements.

We prove $`P_n` for all $`n`, by strong induction.
This means that for a fixed $`n`, we have to check that if $`P_t` is true for all $`t<n` then $`P_n` is also true.
But if $`P_t` is true for all $`t<n` then this means (by definition of $`P_t`) that every number less than $`n` is not in $`A`.
So if $`n\in A` then $`n` would be the least element of $`A`, a contradiction.
We deduce that $`n` can't be in $`A` either, so $`P_n` is true, and we are done.
:::


# Division, divisibility and primes

We can't do exact division in the natural numbers ($`1` and $`2` are natural numbers, but $`1/2` isn't).
However we can do division with remainder.

Here's the idea we are about to formulate more rigorously:
The _remainder_ of $`a` on division by $`b` is what you get when you subtract $`b` from $`a` as many times as possible.
The _quotient_ of $`a` on division by $`b` is the maximum number of subtractions of $`b` you can perform.

:::definition "quotrec"
Let $`b\in\N` with $`b` nonzero.
We define the _quotient_ function $`q_b : \N \to \N` as follows:
for a natural number $`a`,
* if $`a\geq b`: then there exists $`k` such that $`a=b+k`, and we set $`q_b(a)` to be $`q_b(k)+1`.
* otherwise: we set $`q_b(a)` to be $`0`.

Similarly we define the _remainder_ function $`r_b : \N \to \N` as follows:
for a natural number $`a`,
* if $`a\geq b`: then there exists $`k` such that $`a=b+k`, and we set $`r_b(a)` to be $`r_b(k)`.
* otherwise: we set $`r_b(a)` to be $`a`.
:::

Example: $$`q_3(7)=q_3(4)+1=q_3(1)+1+1=0+1+1=2,` and $`r_3(7)=r_3(4)=r_3(1)=1`.
That is, when 7 is divided by 3, the quotient is 2 and the remainder is 1.

This is the first time we are using strong _recursion_ ({theoremref "strong_rec"}[]):
we define $`q_b(a)` and $`r_b(a)` in terms of prior, _not necessarily immediately-prior_, values of $`q_b` and $`r_b`.

:::proposition "quotrec_thm" (title := "Quotient-Remainder Theorem")
Let $`a, b\in\N` with $`b` nonzero.
Letting $`q` and $`r` be respectively the quotient and remainder when $`a` is divided by $`b`,
we have:
* $`0\leq r<b`
* $`a=bq+r`.
:::

:::proof
Fix $`b` and do strong induction on $`a`.

Let $`a` be a natural number and suppose that for all natural numbers $`t<a`,
$`0\leq r_b(t)<b` and $`t=bq_b(t)+r_b(t)`.
There are now two cases to consider:
* if $`a\geq b`: then there exists $`k<a` such that $`a=b+k`.
  We can deduce the desired results from the inductive hypothesis applied to $`k`:
  $`0\leq r_b(k)<b` and $`k=bq_b(k)+r_b(k)`.
* otherwise: then $`r_b(a)=a`, where $`0\leq a<b` by assumption,
  and $`q_b(a)=0`, so $$`a=b\times 0+a=bq_b(a)+r_b(a).`
:::

Even though we can't do exact division in naturals, we can at least record when it would work.

:::definition "def_divisibility"
Let $`n,m\in\mathbb{N}`.
We say that $`m` _divides_ $`n` if there exists a number $`k\in\mathbb{N}`, such that $`n=m\times k`.
Notation: $`m\mid n`.
We also say that $`n` is _divisible_ by $`m`.
:::

Note that this is the analogue of the definition of $`\leq`, with addition replaced by multiplication.

:::lemma "dvd_sub"
Let $`a`, $`k` and $`d` be natural numbers, and suppose that $`d` divides both $`a` and $`a+k`.
Then $`d` divides $`k`.
:::

:::proof
Since $`d` is a factor of both $`a` and $`a+k`, and $`a+k\geq a`,
let us write $`a=da'`, $`a+k=db'` for some natural numbers $`a'` and $`b'`.
By the totality of the order $`a'\ge b'` or $`a'\le b'`.

If the former, by {theoremref "le_add_mul"}[](2)
$$`a=da'\ge db'=a+k;`
by the antisymmetry of the order $`a=a+k`,
so by the cancellative principle of addition ({theoremref "le_prereq"}[]), $`k=0`,
so $`d` divides $`k`.

If the latter, then there exists a natural number $`k'` such that $`b'=a'+k'`.
We then have
$$`a+k=db'=d(a'+k')=a+dk';`
by the cancellative principle of addition ({theoremref "le_prereq"}[]), $`k=dk'`,
so $`d` is a factor of $`k`.
:::

:::definition "def_prime"
A natural number $`n\geq 2` which is divisible only by $`1` and itself is called a prime number.
An integer greater than $`1` which is not prime is called composite.
:::

Note that $`0` and $`1` are neither prime nor composite;
$`0` is zero, and $`1` is called a _unit_.

By "a finite product of prime numbers" below, we mean "a product of finitely many prime numbers", so for example $`84=2^2\times 3\times 7.`

:::proposition "prime_factorisation" (title := "Prime factorisation")
Every natural number greater than one can be factored as a finite product of prime numbers.
:::

:::proof
We prove this by strong induction.
Let $`n` be a natural number greater than one
and suppose that all previous natural numbers greater than one can be factored as a finite product of prime numbers.

This number $`n` is either prime or composite.
If it's prime then it's the product of one prime number!
And if it's composite then we can write $`n=ab` with $`1<a,b<n`.
By the inductive hypothesis, each of $`a` and $`b` can be factored as a finite product of prime numbers,
so $`n=ab` is also a product of finitely many primes.
:::

If you think about it, $`1` is also a product of prime numbers:
it's the product of no prime numbers at all (for the same reason that $`2^0=1`).

Here is another consequence of these ideas.
:::theorem
There are infinitely many primes.
:::

:::proof
We will prove this result by contradiction.
Assume that there are only finitely many primes $`p_1,p_2,\dots,p_n`, $`n\in\mathbb{N}` and define
$$`X=p_1p_2\dots p_n+1.`
By the previous proposition, $`X` must have a prime factor $`q`.
Then
$$`q\mid p_1p_2\dots p_n+1.`
But also $`q` must be one of the $`p_i` because those are all of the primes.
Hence
$$`q\mid p_1p_2\dots p_n.`
Hence by {theoremref "dvd_sub"}[] $`q` divides 1, which is a contradiction.
There are therefore infinitely many primes.
:::

# Euclid's algorithm

Say we have two natural numbers $`a` and $`b`.
Here is a complicated function of $`a` and $`b`.
It's called _Euclid's algorithm_.

:::definition "euclid" (title := "Euclid's Algorithm")
Define a sequence of functions $`gcd_a:\N \to \N` as follows:
* $`gcd_0` is the identity function: for all $`b`, $`gcd_0(b)=b`;
* for nonzero $`a`, $`gcd_a` is defined on the input $`b` in terms of the remainder on division by $`a`
  (see {theoremref "quotrec"}[]):
  $`gcd_a(b)=gcd_{r_a(b)}(a)`.

Notation: sometimes we write $`gcd(a,b)` rather than $`gcd_a(b)`;
with this notation $`gcd` is being thought of as a function from $`\N\times\N` to $`\N`.
:::

This definition is another example of strong recursion ({theoremref "strong_rec"}[]).
The set $`X` is $`\N \to \N`, the set of functions from the natural numbers to themselves:
For each natural number $`a` we define a function $`gcd_a :\N \to \N`.
The function $`gcd_a` is defined in terms in terms of prior, _not necessarily immediately-prior_, functions $`gcd_t`,
namely functions $`gcd_{r_a(b)}`, where $`r_a(b)` are the remainders on dividing various natural numbers by $`a`,
which are all smaller than $`a` itself by {theoremref "quotrec_thm"}[](1).

Let's see an example.
Let's start with $`a=20` and $`b=28`.
We take the remainder of 28 when dividing by 20; this gives 8.
Next we take the remainder of 20 when dividing by 8; this gives 4.
We continue:
$$`\begin{align*}
gcd(20,28)&=gcd(8,20)\\
&=gcd(4,8)\\
&=gcd(0,4)\\
&=4.\end{align*}`
Eventually the remainder is zero, and at that point we return the most recent previous remainder, which was 4.

Let's prove some facts about this function $`gcd`.

:::proposition "euclidstuff" (title := "Results about Euclid's algorithm")
1. $`gcd(a,b)` is always positive, unless both inputs $`a`, $`b` are zero (in which case it's zero).
2. $`gcd(a,b)` divides both $`a` and $`b`.
3. If $`x` is any number which divides $`a` and $`b`, then it also divides $`gcd(a,b)`.
:::

:::proof
We prove all these facts by strong induction.
Let $`a` be a natural number, and suppose these facts are known for $`gcd(t,s)`, for all $`t<a`.
Now let $`b` be a natural number and consider $`gcd(a,b)`.

1.  If $`a=0` then $`gcd(a,b)=b`, which is positive unless $`b` is also zero.

    Otherwise $`gcd(a,b)=gcd(r_a(b),a)`, which is positive by the inductive hypothesis (since $`a` is nonzero).

2.  If $`a=0` then $`gcd(a,b)=b`, which is a factor of both $`0` and $`b`.

    Otherwise $`gcd(a,b)=gcd(r_a(b),a)`, which by the inductive hypothesis is a factor of both $`a` and $`r_a(b)`.
    By {theoremref "quotrec_thm"}[](2),
    the remainder $`r_a(b)` satisfies $`b=aq+r_a(b)` for some natural number $`q` (the "quotient").
    Since $`gcd(a,b)` is a factor of both $`a` and $`r_a(b)`, it must also be a factor of $`b`.

3.  If $`a=0` then $`gcd(a,b)=b`, so $`x`, being a factor of $`b`, is a factor of $`gcd(a,b)`.

    Otherwise, by {theoremref "quotrec_thm"}[](2),
    $`b=aq+r_a(b)` for some natural number $`q`.
    Since $`x` is a factor of both $`a` and $`b`,
    by {theoremref "le_add_mul"}[] it is also a factor of $`r_a(b)`.
    By the inductive hypothesis it follows that $`x` is a factor of $`gcd(r_a(b),a)`,
    which is equal to $`gcd(a,b)` by definition.
:::

We have just shown this:

:::theorem "facts" (title := "Greatest common divisor facts")
If at least one of $`a` and $`b` is positive, then $`gcd(a,b)` is the greatest of the common divisors of $`a` and $`b`,
and it is even a _multiple_ of all common divisors of $`a` and $`b`.
:::

This is why we chose the notation $`gcd` -- it stands for _greatest common divisor_ (we will also use that terminology).

In the case $`a=b=0`, the number $`0=gcd(a,b)` still does have the property that any divisor of $`a` and $`b` divides $`0`,
because _everything_ divides $`0`.
In this case $`0=gcd(a,b)` is not the _greatest_ common divisor because $`37>0` and $`37` divides $`0`.
However it is still the divisor that all the other divisors divide.

Note that computing the greatest common divisor of two numbers via Euclid's algorithm is _much_ more efficient than factoring both sides,
the moment the numbers involved are bigger than 200 or so.

Developing the theory of prime numbers and divisors any further is pretty annoying without a theory of subtraction,
and developing a theory of subtraction is pretty annoying without having access to negative numbers.
So we stop our development of naturals here, and move on to an explanation of the integers.
