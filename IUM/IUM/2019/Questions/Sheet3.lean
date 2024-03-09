/-  Math40001 : Introduction to university mathematics.

Problem Sheet 3, October 2019.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online at 
https://tinyurl.com/Lean-M40001-Example-Sheet-3

or you can install Lean and its maths library following the
instructions at
https://github.com/leanprover-community/mathlib#installation

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online. 

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/
import Data.Real.Basic

#align_import «2019».questions.sheet3

-- the real numbers
-- the real numbers
namespace Questions2019

/- Question 1. 

  Say $X$, $Y$ and $Z$ are sets, and $f:X\to Y$ and $g:Y\to Z$ are functions. In lectures we proved that if 
$f$ and $g$ are injective, then $g\circ f$ is also injective, and we will prove on Monday that if $f$ and $g
$ are surjective, then $g\circ f$ is surjective. But what about the other way?
  \begin{enumerate}
  \item If $g\circ f$ is injective, then is $f$ injective? Give a proof or a counterexample.
  \item If $g\circ f$ is injective, then is $g$ injective? Give a proof or a counterexample.
  \item If $g\circ f$ is surjective, then is $f$ surjective? Give a proof or a counterexample.
  \item If $g\circ f$ is surjective, then is $g$ surjective? Give a proof or a counterexample.
  \end{enumerate}
-/
open Function

-- in Q1 you would be best off defining the counterexample explicitly before you embark upon the
-- disproofs of the false statements
-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
theorem question_one_a_true :
    ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Injective (g ∘ f) → Injective f := by sorry

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
theorem question_one_b_true :
    ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Injective (g ∘ f) → Injective g := by sorry

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
theorem question_one_c_true :
    ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Surjective (g ∘ f) → Surjective f := by sorry

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
theorem question_one_d_true :
    ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), Surjective (g ∘ f) → Surjective g := by sorry

/-
% Q2
\item For each of the following functions, decide whether or not thprop_decidableey are injective, surjective, bijective. 
Proofs required!

  \begin{enumerate}
    \item $f:\R\to\R$, $f(x)=1/x$ if $x\not=0$ and $f(0)=0$.
\item  $f : \R\to\R$, $f(x)=2x+1$.
\item  $f:\Z\to\Z$, $f(x)=2x+1$.
\item  $f:\R\to\R$ defined by $f(x)=3-x$ if the Riemann hypothesis is true, and $f(x)=2+x$ if not. [NB the \
href{https://en.wikipedia.org/wiki/Riemann_hypothesis}{Riemann Hypothesis} is a hard unsolved problem in mat
hematics; nobody currently knows if it is true or false.]
\item $f:\Z\to\Z$, $f(n)=n^3-2n^2+2n-1$.
\end{enumerate}

-/
-- this line just says "we're mathematicians so every proposition is either true or false"
attribute [local instance 10] Classical.propDecidable

-- this line says "a function might not be defined by an algorithm"
noncomputable section

-- definition of the functions in Q2."λ x," is the way computer scientists say "x ↦"
def fa : ℝ → ℝ := fun x => 1 / x

-- Lean defines 1/0 to be 0
def fb : ℝ → ℝ := fun x => 2 * x + 1

def fc : ℤ → ℤ := fun x => 2 * x + 1

axiom RiemannHypothesis : Prop

-- doesn't matter what it says
def fd : ℝ → ℝ := fun x => if RiemannHypothesis then 3 - x else 2 + x

def fe : ℤ → ℤ := fun n => n ^ 3 - 2 * n ^ 2 + 2 * n - 1

-- now write your own questions, below are some examples (that may or may not be possible to prove)
theorem Q2a1 : Injective fa :=
  sorry

theorem Q2a2 : ¬Surjective fa :=
  sorry

theorem Q2c3 : Bijective fc :=
  sorry

/-
Question 3 is "why does this not make sense" so it can't be formalised.
-/
/-
  % Q4
\item  Prove the claim I will make in lecture on Monday, saying that if $f:X\to Y$ is a function, and $g:Y\t
o X$ is a two-sided inverse of~$f$, then~$f$ is a two-sided inverse for~$g$. Deduce that if~$X$ and~$Y$ are 
sets, and there exists a bijection from~$X$ to~$Y$, then there exists a bijection from~$Y$ to~$X$.
-/
theorem Q4a (X Y : Type) (f : X → Y) (g : Y → X)
    (h2sided : (∀ x : X, g (f x) = x) ∧ ∀ y : Y, f (g y) = y) :
    (∀ y : Y, f (g y) = y) ∧ ∀ x : X, g (f x) = x :=
  sorry

-- you will need this result to do the second part. Ignore the proof, I'm using term mode just to
-- make it quicker. Note that this crazy-looking proof is an indication that there are other
-- ways of using Lean apart from tactic mode.
theorem exists_bijection_iff_has_two_sided_inverse (X Y : Type) :
    (∃ f : X → Y, Bijective f) ↔
      ∃ f : X → Y, ∃ g : Y → X, (∀ x : X, g (f x) = x) ∧ ∀ y : Y, f (g y) = y :=
  ⟨fun ⟨f, hf⟩ => ⟨f, bijective_iff_has_inverse.1 hf⟩, fun ⟨f, g, hgf, hfg⟩ =>
    ⟨f, bijective_iff_has_inverse.2 ⟨g, hgf, hfg⟩⟩⟩

theorem Q4b (X Y : Type) : (∃ f : X → Y, Bijective f) ↔ ∃ g : Y → X, Bijective g :=
  sorry

/-
  % Q5
  \item Let~$Z$ be a set. If $f:X\to Z$ and $g:Y\to Z$ are injective functions, let's say that $f$ \emph{is 
friends with} $g$ if there is a bijection $h:X\to Y$ such that $f=g\circ h$. Prove that $f$ is friends with 
$g$ if and only if the image of~$f$ equals the image of~$g$. NB: by the \emph{image} of $f:X\to Z$ I mean th
e subset of~$Z$ consisting of things ``hit'' by $f$, in other words the set $\{z\in Z\,:\,\exists x\in X, f(
x)=z\}$. Some people call this the ``range'' of $f$, although other people use ``range'' to mean the same th
ing as ``codomain'' :-| 

-/
def Friends {X Y Z : Type} (f : X → Z) (g : Y → Z) (hf : Injective f) (hg : Injective g) :=
  ∃ h : X → Y, Bijective h ∧ f = g ∘ h

theorem Q5 (X Y Z : Type) (f : X → Z) (g : Y → Z) (hf : Injective f) (hg : Injective g) :
    Friends f g hf hg ↔ Set.range f = Set.range g :=
  sorry

end Questions2019

