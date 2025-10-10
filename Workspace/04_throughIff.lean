/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/


-- ANSWER

--Formal Proof
theorem andImpEquiv (P Q : Prop) : (P ∧ Q) → (P ↔ Q) := by
  intro hPQ
    -- hPQ : P ∧ Q
  -- Build an equivalence by giving both directions.
  refine Iff.intro ?pq ?qp
  · -- P → Q
    intro _p
    exact hPQ.right
  · -- Q → P
    intro _q
    exact hPQ.left

/- @@@
#2: Give the proof in #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER
Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in this
context,  and we will then show that, in that
context, the conclusion must be true as well. So
assume P ∧ Q is true. The conclusion to be proved
is an equivalence. To prove an equivalence we need
to prove both directions:
(i) P → Q and (ii) Q → P.
For (i) assume P From out original assumption P ∧ Q,
by ∧-elimination, we obtain Q Thus P → Q
For (ii) assume Q From P ∧ Q we also obtain P by
∧-elimination. Thus Q → P. Having proved both directions,
we conclude P ↔ Q. Since this was under the assumption
P ∧ Q, we have (P ∧ Q) → (P ↔ Q).
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Do not just copy the proof. The whole point is to
reinforce the idea that one you've proved a theorem
you can use it (by applying it) to prove any special
case (here involving X and Y) of the general claim.
@@@ -/

-- Answer
axiom X : Prop
axiom Y : Prop
axiom hXY : X ∧ Y

--Apply the general theorem from #1 to this specific world:
#check (andImpEquiv X Y hXY)
-- : X ↔ Y


/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER
--Formal proof using 'False.elim'
theorem exFalsoK (K : Prop) : False → K := by
  intro f
  exact False.elim f

--Equivalent proof using 'nomatch'
theorem exFalsoK_nomatch (K : Prop) : False → K := by
  intro f
  nomatch f

/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

ANSWER:
It's safe because 'False' had no proofs/constructors.
Any context that provides 'f : False' is an impossible case.
From an impossible hypothesis, anything follows (principle:
ex falso quodlibet) Lean accepts "bailing out" of an impossible
branch with 'False.elim f' or 'nomatch f' for any target K
precisely because such a branch can never actually occur

@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER
theorem falseAndP_implies_Q ( Q : Prop) : (False ∧ P) → Q := by
  intro h
--From h : False ∧ P we get a proof of False
  have f : False := h.left
  exact False.elim f

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.
@@@ -/

-- ANSWER
/-
Let P and Q be propositions. Assume False ∧ P.
By ∧-elimination we obtain a proof False. From a
contradiction, anything follows (ex falso), so Q holds
Therefore, (False ∧ P) → Q. ∎
-/

/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/


-- ANSWER

--Formal Proof
theorem falseImpFalse : False → False := by
  intro f
  exact f

--English Proof
-- Proof. Assume False. Then, False holds; return the same proof.
--Therefor False → False.
