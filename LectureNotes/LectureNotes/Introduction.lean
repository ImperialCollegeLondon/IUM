/-
Copyright (c) 2025 Heather Macbeth, based on prior versions by Marie-Amélie Lawn and Kevin Buzzard.
All rights reserved.
-/
import LectureNotes.Formatting

open Verso.Genre Manual

#doc (Manual) "Introduction"  =>

Historically, numbers were used to solve real world problems,
and formal _definitions_ of numbers did not exist in the literature.
For example the ancient Greeks might have thought of positive real numbers as "lengths" in the physical universe.
This informal approach is fine in practice if you're using numbers to do things like make measurements of real world objects
(for example if you are building a tower, or keeping track of how much gold or how many sheep you have),
but it has deficiencies.
For example it doesn't answer the questions of whether $`0.999999\ldots=1`
and whether infinitely small positive numbers can exist.
By the 1600s Newton and Leibniz had discovered the elusive quantities $`dy` and $`dx`,
which were giving correct answers to questions in physics via the theory of differential equations.
Are these "numbers"?
Any attempt to resolve such subtle questions about the nature of numbers via physics will inevitably fail,
because by the time we have got down to about $`10^{-35}` metres (Planck length) then spacetime becomes a quantum foam,
matter and antimatter start rapidly appearing and disappearing, and things get pretty weird.

The mathematician knows that quantum foam has nothing to do with the real numbers.
What is happening is that the real numbers _do not exist in the physical universe_
and hence we cannot use the real universe to model them perfectly.
Indeed no infinite thing can _exist_ in our physical universe,
which is large but finite,
and contains only around $`10^{70}` atoms.
This is in sharp contrast to what is happening in mathematics,
where one of the first things we learn as children is how to count,
together with the implicit idea that you can continue to count forever.

The idea of a "mathematical universe"
where things like a perfect circle or a 17-dimensional cube can exist untroubled by physics,
goes back to Plato.
But it was only around 140 years ago that mathematicians started seriously thinking about _axioms_ which defined numbers.
There are all kinds of number systems in use in mathematics:
in this and the next chapter we shall consider the five most important ones:

* The natural numbers (the counting numbers);
* The integers (where we allow negative whole numbers);
* The rationals (where we allow ratios of integers);
* The reals (where we allow non-periodic decimals);
* The complexes (where we allow square roots of negative reals).

We'll also consider the integers modulo $`n`,
a world where some positive numbers can equal zero.
People interested in the quaternions, octonions, sedonions, $`p`-adic numbers, hyperreals, nimbers and other exotic number systems
will have to wait until later in the course;
we already have plenty to get through here.

We will begin our story with the _natural numbers_.
We will watch these numbers be born,
and then we will develop the theory until they become the numbers which we are used to using.
A big big warning:
while the theory is being developed,
we absolutely _cannot_ use standard facts about numbers which we all know:
for most of this section we will be seeing numbers in a strange half-constructed state,
and we will need to be _extremely_ careful not to assume anything which we didn't already prove,
because we need to avoid _circular arguments_.

We will summon the natural numbers into existence by using three _axioms_;
these will be rules which we decree are true in the mathematical universe,
rather like how the laws of physics are true in our physical universe.
Once we have the natural numbers up and running, we will then _build_ the integers, rationals, reals and complexes from them directly;
no more axioms will be required.

One important consequence of this is that we will then be able to _prove_ statements like $`x+y=y+x` or that $`0.9999\dots=1`,
without _ever_ having to appeal to real world intuition.
In particular, in this part of the course, we _reject_ arguments such as
"if I have $`x` apples in one hand and $`y` apples in the other,
and I then swap my hands around,
obviously the total number of apples I have didn't change,
and obviously this works for all things, not just apples, therefore $`x+y=y+x`".
The formalist view of mathematics is that it is a puzzle game, like a Sudoku or a chess puzzle.
You cannot make an illegal move to solve a chess puzzle because this contradicts the axioms of chess (i.e., the rules of chess).
We will take the same view when working with numbers:
if you can't deduce your argument from the axioms, then your argument is not allowed.
