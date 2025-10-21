/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "../IUM"
set_option verso.exampleModule "IUM.Int.Arithmetic"
set_option verso.externalExamples.suppressedNamespaces "MyInt"

#doc (Manual) "Addition, subtraction, multiplication"  =>

To test that our definitions are behaving the way we expect, we could check that $`2-1=1`.
But wait: we haven't defined subtraction yet!
Or addition or multiplication for that matter.
Now we have a new number system $`\Z` we _strictly speaking_ have to start again and define $`+` and $`\times` on $`\Z`,
and we also have to define subtraction, and prove all the standard facts about how they are related such as $`(x-y)\times z=x\times z-y\times z`.
Fortunately this job is easier than the corresponding job for the natural numbers.
I'll get you to do some of it on the second Numbers problem sheet.

Let's talk about subtraction, because we've not seen it before.
A cool definition of subtraction could be to _define_ $`x-y` to be $`x+(-y)`, where that $`-y` is "minus $`y`", the _negation_ of $`y`.
Note that even though we use the same symbol $`-` for both ideas, subtraction and negation are strictly speaking two different things:
subtraction eats two integers and spits out an integer; negation only eats one.
Let's define negation. This involves introducing a new idea.

The integers $`\Z` were defined to be the _quotient_ of the auxiliary object $`\N\times\N` by a certain equivalence relation.
So the integer $`2` is actually the infinite set $`\{(2,0),(3,1),(4,2),(5,3)\ldots\}`
(remember that an ordered pair $`(a,b)` of naturals should be thought of as representing the integer $`a-b`, even though this doesn't make sense yet).
Let's think of the integers as obtained from $`\N\times\N` by "squishing together" equivalent pairs into one object.

Now a function _has_ to have the property that if give it the same input twice, you get the same output.
So for example if $`a=b` and $`f` is a function then $`f(a)` has to equal $`f(b)`
(note that this is not injectivity; injectivity is the implication the other way. This is an axiom of mathematics).
The problem with all this "squishing together" idea is that if two things got squished together then in the quotient they are _equal_,
so any function had better do the same thing to them -- it can "unsquish them".

The upshot of all this:
if we want to define negation $`f(x)=-x` on the integers, then we should
1. First define a version of negation on $`\N\times\N`; then
2. Second check that it sends equivalent inputs to equivalent outputs.
The second condition ensures that no "unsquishing" is taking place.

Let's pretend the integers exist for 10 seconds, and ask what the negation of $`a-b` is; it's $`b-a`.
This motivates the following definition.

:::definition "preneg" (title := "pre-negation")
Define a "pre-negation" function from $`\N\times\N` to $`\N\times\N`, by defining $`-(a,b)` to be $`(b,a)`.
:::

Now let's prove that pre-negation _preserves the equivalence relation_.
Informally I mean that we need to check that "pre-negation doesn't unsquish squished things".
Formally I mean this:

:::theorem "neg_welldefined" (title := "pre-negation plays well with equivalence")
If $`(a,b)\sim(c,d)` then $`-(a,b)\sim -(c,d)`.
:::

:::proof
Our hypothesis is that $`a+d=b+c`, and the conclusion we want is that $`(b,a)\sim(d,c)` or in other words that $`b+c=a+d`.
But this obviously follows (you can say "$`\ldots` because equality is symmetric" if you want to sound clever).
:::

```anchor prenegation
Lemma prenegation_wd
  "Pre-negation is well-defined"
  Given: {a b c d : ℕ}
  Assume: (h : (a, b) ≈ (c, d))
  Conclusion: prenegation (a, b) ≈ prenegation (c, d)
Proof:
  We reformulate h as a + d = b + c
  Let's prove that b + c = a + d
  We conclude by h
QED
```

:::definition "" (title := "negation on the integers")
Define negation on $`\Z` (i.e. the function sending $`x` to $`-x`) to be the function sending the equivalence class of $`(a,b)` to the equivalence class of $`(b,a)`.
:::

We have just proved that this is a valid mathematical definition.
The potential issue is that you can have different elements $`(a,b)` and $`(c,d)` of $`\N\times\N` which are equivalent but not equal, and then their equivalence classes are equal,
so we have to make sure this function maps them to equal things, but it does by the preceding theorem.

Now let's do addition, subtraction and multiplication.

For addition we first do the following calculation, pretending that the integers already have a subtraction: $`(a-b)+(c-d)=(a+c)-(b+d)`, so this motivates the following:

:::definition "preadd1" (title := "pre-addition")
Define pre-addition to be the function which takes two elements $`(a,b)` and $`(c,d)` of $`\N\times\N` and returns the element $`(a+c,b+d)`.
:::

:::theorem "preaddequiv" (title := "pre-addition plays well with equivalence")
If $`(a,b)\sim(a',b')` and $`(c,d)\sim(c',d')` then $`(a+c,b+d)\sim(a'+c',b'+d')`.
:::

:::proof
Our hypotheses are $`a+b'=b+a'` and $`c+d'=d+c'`.
Our goal is $`(a+c)+(b'+d')=(b+d)+(a'+c')`.
But the left hand side rearranges to $`(a+b')+(c+d')` and the right hand side to $`(b+a')+(d+c')` and these are equal by our assumptions.
:::

```anchor preaddition
Lemma preaddition_wd
  "Pre-addition is well-defined"
  Given: {a a' b b' c c' d d' : ℕ}
  Assume: (h1 : (a, b) ≈ (a', b')) (h2 : (c, d) ≈ (c', d'))
  Conclusion: preaddition (a, b) (c, d) ≈ preaddition (a', b') (c', d')
Proof:
  We reformulate h1 as a + b' = b + a'
  We reformulate h2 as c + d' = d + c'
  Let's prove that (a + c) + (b' + d') = (b + d) + (a' + c')
  Calc
    (a + c) + (b' + d') = (a + b') + (c + d') by computation
    _                   = (b + a') + (c + d') from h1
    _                   = (b + a') + (d + c') from h2
    _                   = (b + d) + (a' + c') by computation
QED
```

This means that pre-addition cannot unsquish things which are already squished -- if two things are equivalent and you pre-add them, they stay equivalent.
This means that the definition of pre-addition descends to $`\Z`.

:::definition "intadd" (title := "addition on the integers")
Define addition on $`\Z` by saying that $`cl(a,b)+cl(c,d)=cl(a+c,b+d)`.
:::

We don't need presubtraction; we can just define subtraction given what we already have.
:::definition "intsub" (title := "subtraction on the integers")
If $`x,y\in\Z` then define $`x-y` to be $`x+(-y)`.
:::

Finally, multiplication.
First the thought experiment: $`(a-b)\times(c-d)=(ac+bd)-(ad+bc)`.
Now the pre-definition.

:::definition "premul" (title := "pre-multiplication")
If $`(a,b)` and $`(c,d)` are in $`\N\times\N`, define their pre-product $`(a,b)\times(c,d)` to be $`(ac+bd,ad+bc)`.
:::

Now the proof that it's well-defined.
Instead of doing it all in one go like we did with addition, let's make our lives a bit easier by checking that we can change one input at a time and not mess up the output.

:::theorem "preadd_equiv"
1. If $`(a,b)\sim(a',b')` then $`(a,b)\times(c,d)\sim (a',b')\times (c,d)`;
2. If $`(c,d)\sim(c',d')` then $`(a,b)\times(c,d)\sim (a,b)\times(c',d')`.
:::

:::proof
For the first part, we are assuming $`a+b'=b+a'` and we want to prove that $`(ac+bd,ad+bc)\sim(a'c+b'd,a'd+b'c)`,
or equivalently that $`(ac+bd)+(a'd+b'c)=(ad+bc)+(a'c+b'd)`.
By rearranging (i.e., using commutativity and associativity several times, as well as distributivity)
we deduce that we want to prove $`(a+b')c+(b+a')d=(a+b')d+(b+a')c`,
and this is immediate because of our assumption $`a+b'=b+a'`.

The second part follows similarly.
:::

```anchor premultiplication
Lemma premultiplication_wd_1
  "Pre-multiplication is well-defined in the first variable"
  Given: {a a' b b' c d : ℕ}
  Assume: (h : (a, b) ≈ (a', b'))
  Conclusion:
    premultiplication (a, b) (c, d) ≈ premultiplication (a', b') (c, d)
Proof:
  We reformulate h as a + b' = b + a'
  Let's prove that (a * c + b * d) + (a' * d + b' * c)
    = (a * d + b * c) + (a' * c + b' * d)
  Calc
    (a * c + b * d) + (a' * d + b' * c)
      = (a + b') * c + (b + a') * d         by computation
    _ = (b + a') * c + (a + b') * d         from h
    _ = (a * d + b * c) + (a' * c + b' * d) by computation
QED

Lemma premultiplication_wd_2
  "Pre-multiplication is well-defined in the second variable"
  Given: {a b c c' d d' : ℕ}
  Assume: (h : (c, d) ≈ (c', d'))
  Conclusion:
    premultiplication (a, b) (c, d) ≈ premultiplication (a, b) (c', d')
Proof:
  We reformulate h as c + d' = d + c'
  Let's prove that (a * c + b * d) + (a * d' + b * c')
    = (a * d + b * c) + (a * c' + b * d')
  Calc
    (a * c + b * d) + (a * d' + b * c')
      = a * (c + d') + b * (d + c')         by computation
    _ = a * (d + c') + b * (c + d')         from h
    _ = (a * d + b * c) + (a * c' + b * d') by computation
QED
```

:::definition "intmul" (title := "multiplication")
We define $`cl(a,b)\times cl(c,d)` to be $`cl(ac+bd,ad+bc)`.
:::

The theorem above shows that this is well-defined, i.e. if $`cl(a,b)=cl(a',b')` and $`cl(c,d)=cl(c',d')` then the equivalence class of the products are also equal.

By definition, $`0\in\Z` is the equivalence class of $`(0,0)`, and $`1\in\Z` is the equivalence class of $`(1,0)`.
So now you can check the analogues of all of the facts about addition and multiplication which we showed for the naturals.
Here is an example.

:::theorem "mul_add" (title := "distributivity")
If $`x,y,z` are integers, then $`x(y+z)=xy+xz`.
:::

:::proof
Let's say $`x` is the class of $`(a,b)`, $`y` is the class of $`(c,d)` and $`z` is the class of $`(e,f)`.
Then the left hand side is the class of $`(a,b)\times(c+e,d+f)` which is
$$`(a(c+e)+b(d+f),a(d+f)+b(c+e)),`
and the right hand side is the class of $`(ac+bd,ad+bc)+(ae+bf,af+be)` which is
$$`((ac+bd)+(ae+bf),(ad+bc)+(af+be))`
and these are equal because of standard facts from the theory of addition
(distributivity, commutativity and associativity).
:::

```anchor th_distrib
Lemma mul_add
  "Multiplication on the integers is distributive"
  Given: (x y z : ℤ)
  Assume:
  Conclusion: x * (y + z) = x * y + x * z
Proof:
  We represent x as (a, b)
  We represent y as (c, d)
  We represent z as (e, f)
  We lift to the relation on pairs
  Let's prove that
    (a * (c + e) + b * (d + f), a * (d + f) + b * (c + e)) ≈
    ((a * c + b * d) + (a * e + b * f), (a * d + b * c) + (a * f + b * e))
  We compute
QED
```

From this point on, let us use addition, subtraction and multiplication normally, because we have shown how to justify all the usual rules.
