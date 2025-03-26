## Summary of several tactics

### `apply`

**Summary:** If we have the goal `⊢ Q`, and a proof of `h : P → Q`, we only need to find a proof for `P`. This transition happens by `apply h`.

:::table (align := left) (header := true)
* + , h : P → Q {br}[] ⊢ P
  + apply h
  + ⊢Q
* + h₁ : P → Q {br}[] h₂ : Q → R  {br}[] ⊢ R
  + apply h₂ h₁
  + h₁ : P → Q {br}[] h₂ : Q → R  {br}[] ⊢ P
:::

The `apply`-tactics works iteratively. This means that if `apply h` makes no progress, it uses the placeholder `_` and tries to make `apply h _`.

```lean
example (hPQR : P → Q → R) : R := by
  apply hPQR
  · sorry
  · sorry
```


**Remarks:**
* `apply` works up to equality by definition. This can be seen in the example above, where `¬P ↔ (P → False)` is true by definition.
* `apply h` is frequently identical to `refine ?_`.
* If the use of `apply` closes the current goal, you might as well use `exact` instead of `apply`.


## `by_cases

**Summary: **
If you have a term `P : Prop` as a hypothesis, `by_cases hP : P` returns two goals. The first one has `hP : P`, and the second one `hP : ¬P`. This tactic is thus identical to `have hP : P ∨ ¬ P, exact em P, cases hP,`. (The second expression is `em : ∀ (p : Prop), p ∨ ¬p`.)

**Examples**

+-----------------------------+--------------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:============================+:=========================+:======================+
| `⊢ P` | `by_cases h : Q,` | `h : Q` |
+-----------------------------+--------------------------+-----------------------+
| | | `⊢ P` |
+-----------------------------+--------------------------+-----------------------+
| | | `h : ¬Q` |
+-----------------------------+--------------------------+-----------------------+
| | | `⊢ P` |
+-----------------------------+--------------------------+-----------------------+
| `x: bool`\ | | |
| `⊢ x = tt ∨ x = ff` | | |
| | | |
| & | | |
| | | |
| `by_cases x=tt,` | | |
| | | |
| & | | |
| | | |
| `x: bool`\ | | |
| `h: x = tt`\ | | |
| `⊢ x = tt ∨ x = ff`\ | | |
| `x: bool`\ | | |
| `h: ¬x = tt`\ | | |
| `⊢ x = tt ∨ x = ff` | | |
+-----------------------------+--------------------------+-----------------------+

In the second example, we use a variable of type `bool` This is defined as follows:

```
inductive bool : Type
| ff : bool
| tt : bool
```

A Boolean variable can only have the values `tt` (for `true`) and `ff` (for `false`).

**Notes**

* Apparently, the `by_cases` tactic (just like `by_contradiction`) assumes that a statement is either true or false. This is also known as the law of excluded middle. In mathematics, proofs that do not use this rule are called constructive.
* For terms of type `Prop`, the tactic `tauto` (or `tauto!`) can
draw

## `by_contra`

**Summary**

The `by_contra` tactic provides a proof by contradiction. It is therefore assumed (i.e. transformed into a hypothesis) that the statement (after `⊢`) is not true, and this must be made to contradict itself, i.e. a proof of `false` must be found.

**Examples**

+---------------------------+-----------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==========================+:======================+:======================+
| `⊢ P` | `by_contra h,` | `h : ¬P` |
+---------------------------+-----------------------+-----------------------+
| | | `⊢ false` |
+---------------------------+-----------------------+-----------------------+
| `h: ¬¬P`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `by_contra hnegP,` | | |
| | | |
| & | | |
| | | |
| `h: ¬¬P`\ | | |
| `hnegP: ¬P`\ | | |
| `⊢ false` | | |
+---------------------------+-----------------------+-----------------------+

**Notes**

This tactic is stronger than `exfalso`. After all, there the goal is only converted to `false` without adding a new hypothesis. With `by_contra`, the new goal is also `false`, but there is still a new hypothesis.

## `calc`

**Summary:** As the word suggests, `calc` is about concrete calculations. This is not a tactic, but a `lean` mode. This means that you can enter this mode (with the word `calc`) and enter calculation steps and proofs that each individual calculation step is correct.

**Examples**

Here is a proof of the first binomial formula that only comes about by rewriting of calculating properties from the `mathlib`.

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
have h : n + n = 2*n,
{
nth_rewrite 0 ← one_mul n,
nth_rewrite 1 ← one_mul n,
rw ← add_mul,
},
calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }...
 = (n+1)*n + (n+1) * 1: by {rw mul_add, }
... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}...
 = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}...
 = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← h, },
```

The same can be achieved without the `calc` mode, like this:

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2*n, by { nth_rewrite 0 ← one_mul n,
  nth_rewrite 1 ← one_mul n, rw ← add_mul, },
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul,
  ← pow_two, add_assoc, ← add_assoc n n 1,
  ← add_assoc, ← h],
```

However, this is much less readable.

**Notes**

## `cases`

**Summary:** If a hypothesis is composed, i.e. can be expanded into two or more cases, `cases'` delivers exactly that. This can be used not only used with hypotheses `h : P ∨ Q` or `h : P ∧ Q`, but also with structures that consist of several cases, such as `∃...` (here there is a variable and a statement) and `x : bool` or `n : ℕ`.

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `h : P ∧ Q` | `cases h | `hP : P` |
| | with hP hQ,` | |
+----------------------+----------------------+----------------------+
| `⊢ R` | | `hQ : Q` |
+----------------------+----------------------+----------------------+
| | | `⊢ R` |
+----------------------+----------------------+----------------------+
| `h : P ∨ Q` | `cases h | `hP : P` |
| | with hP hQ,` | |
+----------------------+----------------------+----------------------+
| `⊢ R` | | `⊢ R` |
+----------------------+----------------------+----------------------+
| | | `hQ : Q` |
+----------------------+----------------------+----------------------+
| | | `⊢ R` |
+----------------------+----------------------+----------------------+
| `h : false` | `cases h,` | **goals accomplished |
| | | ** |
+----------------------+----------------------+----------------------+
| `⊢ P` | | |
+----------------------+----------------------+----------------------+
| ` | | |
| P: ℕ → Prop`\ | | |
| `h: ∃ ( | | |
| m : ℕ), P m`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `cases x | | |
| with m h1, ` | | |
| | | |
| & | | |
| | | |
| `P | | |
| : ℕ → Prop`\ | | |
| `m : ℕ`\ | | |
| `h1 : P m`\ | | |
| `⊢ Q` | | |
+----------------------+----------------------+----------------------+

**Notes:**

* The application `cases' n` for `n : ℕ` is strictly weaker than complete induction (see `induction`). After all, `cases` only converts `n : ℕ` into the two cases `0` and `succ n`, but you cannot use the statement for `n-1` to prove the statement for `n`.
* A more flexible version of `cases'` is `rcases`.

## `change`

**Summary:**

Changes the goal (or a hypothesis) into a goal (or a hypothesis) that is defined the same.

**Examples:**

+---------------------------------+---------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:================================+:====================+:======================+
| `⊢ : P → false` | `change ¬P,` | `⊢ ¬P` |
+---------------------------------+---------------------+-----------------------+
| `h : ¬P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `change P → false at h,` | | |
| | | |
| & | | |
| | | |
| `h: P → false`\ | | |
| `⊢ Q` | | |
+---------------------------------+---------------------+-----------------------+

**Notes:**

* As can be seen from the penultimate example, `change` also works for hypotheses.
* Since many tactics test for definitional equality anyway, `change` is often not necessary. However, it can help to make the proof more readable.

## `clear`

**Summary:** With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

**Examples:**

**Proof state** **Command** **New proof state**
----------------- ------------------- -----------------------
`h : P` `clear h,` `⊢ Q`
`⊢ Q`

## `congr`

**Summary:** If you have to show an equality `f x = f y`, then `congr` uses the statement that the equality is particularly true if `x = y`.

**Examples:**

**Proof state** **command** **New proof state**
---------------------- ----------------- -----------------------
`⊢ P x = P y` `congr,` `⊢ x = y`

**Notes:**

The related tactic `congr'` uses another parameter that determines how many recursive layers are eliminated in the goal. This is helpful in the following examples:



+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ f (x + y) = f (y + x)` | | |
| | | |
| & | | |
| | | |
| `congr,` | | |
| | | |
| & | | |
| | | |
| `⊢ x = y`\ | | |
| `⊢ y = x` | | |
+----------------------------------+--------------+-----------------------+

## `exact`

**Summary:** If the goal can be achieved with a single command, then it can be achieved with the `exact` tactic. Like many other tactics, `exact` also works with terms that are defined the same.

**Examples:**

+----------------------------+-------------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:==================+:========================+
| `h : P` | `exact h,` | **goals accomplished ** |
+----------------------------+-------------------+-------------------------+
| `⊢ P` | | |
+----------------------------+-------------------+-------------------------+
| `hP: P`\ | | |
| `hQ: Q`\ | | |
| `⊢ P ∧ Q` | | |
| | | |
| & | | |
| | | |
| `exact ⟨ hP, hQ ⟩,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+----------------------------+-------------------+-------------------------+

**Notes:**

In the third example, note the order in which the two hapotheses `hP` and `hnP` are applied. The first hypothesis after `exact` is always the one whose right side matches the goal. If the goal requires further input, it is appended afterwards.

## `exfalso`

**Summary:** The statement `false → P` is true for all `P`. If the current goal is `⊢ P`, and you would apply this true statement using `apply`, the new goal would be `⊢ false`. This is exactly what the `exfalso` tactic does.

**Examples:**

+--------------------+-------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:==================+:======================+
| `h : P` | `exfalso,` | `h : P` |
+--------------------+-------------------+-----------------------+
| `⊢ Q` | | `⊢ false` |
+--------------------+-------------------+-----------------------+
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `exfalso, ` | | |
| | | |
| & | | |
| | | |
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ false` | | |
+--------------------+-------------------+-----------------------+

**Notes:**

If you use this tactic, you leave the realm of constructive mathematics. (This dispenses with the rule of the excluded middle.)

## `have`

**Summary:** By using `have` we introduce a new claim, which we have to prove first. Afterwards, it is available as a hypothesis in all further goals. This is identical to first proving a lemma `h` with the statement after `have h : ` and then reusing it at the appropriate place in the proof (for example with `apply` or `rw`).

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `⊢ R` | `have | `⊢ P ↔ Q` |
| | h : P ↔ Q, ` | |
+----------------------+----------------------+----------------------+
| | | `h : P ↔ Q` |
+----------------------+----------------------+----------------------+
| | | `⊢ R` |
+----------------------+----------------------+----------------------+
| `⊢ P` | | |
| | |
| & | | |
| | | |
| `have h1 : | | |
| ∃ (m : ℕ),`\ | | |
| ` | | |
| f 27 m, ...`\ | | |
| `cases | | |
| h1 with m hm` | | |
| | | |
| & | | |
| | | |
| `m : ℕ`\ | | |
| `hm: f 27 m`\ | | |
| `⊢ P` | | |
+----------------------+----------------------+----------------------+

**Notes:**

* Suppose we have two goals (let's call them `⊢1` and `⊢2`), and we need the statement of `⊢1` in the proof of `⊢2`. We can first introduce a third goal with `have h := ⊢ 1` (where `⊢1` is to be replaced by the statement). Then `⊢ 1` can be proved with `exact`, and has the statement `⊢ 1` available in the proof of `⊢ 2`.

## `induction`

**Summary:**

Inductive types allow the possibility of proving statements about them by means of induction. This includes, for example, the usual case of complete induction over natural numbers.

**Examples** {#beispiele-12.unnumbered}

**Proof state** **command** **new proof state**
---------------------- --------------------------------- ---------------------------------
`n : ℕ` `induction n with d hd,` `⊢ 0 = 0 + 0`
`⊢ n = 0 + n` `hd : d = 0 + d`
`⊢ d.succ = 0 + d.succ,`

## `intro`

**Summary**

If the goal is of the form `⊢ P → Q` or `∀ (n : ℕ), P n`, you can proceed with `intro P` or `intro n`. You can use several `intro` commands at the same time to summarize a single one. A little more precisely, `intro h1 h2 h3,` is identical to `intro h1; intro h2; intro h3`.


**Examples**

**Proof state** **Command** **New proof state**
--------------------------- ------------------- -----------------------
`⊢ P → Q` `intro hP` `hP : P`
`⊢ Q`
`f : α → Prop` `intro x,` `f: α → Prop`
`⊢ ∀ (x : α), f x` `x : α`
`⊢ f x`

+-------------------------------+------------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=======================+:======================+
| `⊢ P → Q → R` | `intros hP hQ,` | `hP : P` |
+-------------------------------+------------------------+-----------------------+
| | | `hQ : Q` |
+-------------------------------+------------------------+-----------------------+
| | | `⊢ R` |
+-------------------------------+------------------------+-----------------------+
| `P: ℕ → Prop`\ | | |
| `⊢ ∀ (n : ℕ), P n → Q` | | |
| | | |
| & | | |
| | | |
| `intros n hP` | | |
| | | |
| & | | |
| | | |
| `P: ℕ → Prop`\ | | |
| `n: ℕ`\ | | |
| `hP: P n` `⊢ Q` | | |
+-------------------------------+------------------------+-----------------------+


**Notes**

* Several `intro` commands in a row are best combined. Furthermore,  `rintro` is a more flexible variant.
* A reversal of `intro` is `revert`.






## `left`

**Summary:**

The application of `left,` is identical to `apply h,` for `h : P → P ∨ Q`. So if you have a goal of the form `⊢ P ∨ Q`, `left,` causes you to have only the goal `⊢ P`. After all, it is sufficient to show `P` to close the goal.

**Examples:**

+-------------------------+----------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:======================+
| `⊢ P ∨ Q` | `left,` | `⊢ P` |
+-------------------------+----------------+-----------------------+
| `⊢ ℕ` | | |
| | | |
| & | | |
| | | |
| `left,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+-------------------------+----------------+-----------------------+


The second example requires a little explanation. First of all, you have to understand that the goal `⊢ ℕ` is to show that there is a term of type `ℕ`, i.e. that there is a natural number. Now you have to know how `ℕ` is implemented in Lean. This is

```
inductive nat
| zero : nat
| succ (n : nat) : nat
```

together with

```
notation `ℕ` := nat
```
This means: The type `ℕ` is defined by the fact that `zero` is a term of this type, and that there is a function `succ : ℕ → ℕ`. Thus, in the second example, the input `left,` is closed because by definition `zero : ℕ` holds, so in particular there is a term of type `ℕ`.

**Notes:**

* See also `right,` for the equivalent tactic, which is apply h` for `h : Q → P ∨ Q`.
* As in the second example, `left,` can always be applied when dealing with an inductive type with two constructors (such like `ℕ`).

## `apply?`

**Summary: ** There are already a lot of proven statements in `mathlib`. When using `apply?`, the `mathlib` is statements whose types correspond to those of the statement to be proved. If this is not successful, `Lean` reports a `timeout`. If successful, it also reports which command was found. If you click on it, this is inserted in place of `library_search`.

**Examples**

**Proof state** **Command** **New proof state**
--------------------- -------------------------- -------------------------------
`h1 : a < b` `library_search,` **goals accomplished **
`h2 : b < c` `Try this: `
`⊢ a < c` `exact lt_trans h1 h2`

**Notes** {#anmerkungen-14 .unnumbered}

The tactic `suggest` is similar and also works if
the goal cannot be closed.

## `linarith`

**Summary:** This tactic can prove equations and inequalities with the help of hypotheses. It is important that the hypotheses used are also only equations and inequalities. So here we are working mainly with the transitivity of `<` together with arithmetic rules.

**Examples:**

**Proof state** **Command** **New proof state**
---------------------- -------------------- -------------------------
`h1 : a < b` `linarith,` **goals accomplished **
`h2 : b ≤ c`
`⊢ a < c`[^9]

## `norm_num`

**Summary:** As long as no variables are involved, `norm_num` can perform calculations involving `=`, `<`, `≤`, or '≠'.

**Examples:**

+----------------------------+--------------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:===================+:========================+
| `⊢ 2 + 2 < 5`[^10] | `norm_num,` | **goals accomplished ** |
+----------------------------+--------------------+-------------------------+
| `⊢ | (1 : ℝ) | = 1` | | |
| | | |
| & | | |
| | | |
| `norm_num,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+----------------------------+--------------------+-------------------------+

**Notes:**

`norm_num` knows a few other arithmetic operations, such as the absolute value function, see the second example.

## `nth_rewrite`

**Proof state** **Command** **New proof state**
--------------------------- -------------------- -------------------------
`⊢ 2 + 2 < 5`[^11] `norm_num,` **goals accomplished **

**Summary:**

This tactic is related to `rw`. The difference is that you can specify the occurrence number of the term to be replaced on which `rw` is to be applied. The exact syntax is `nth_rewrite k h`, where `k` is the number (starting with $0$) of the term to be replaced and `h` is the hypothesis to be replaced. As with `rw`, this must be in the form `h : x=y` or `h : A↔B`.

**Examples:**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `n : ℕ`\ | | |
| `⊢ 0 + n = 0 + 0 + n` | | |
| | | |
| & | | |
| | | |
| `nth_rewrite 0 zero_add,` | | |
| | | |
| & | | |
| | | |
| `n: ℕ`\ | | |
| `⊢ n = 0 + 0 + n` | | |
+----------------------------------+--------------+-----------------------+

In the above example, Lean sees three terms of the form `0 + _`: Number 0 is on the left-hand side, for numbers 1 and 2, on the right side (because of the parenthesis `0 + 0 + n = (0 + 0) + n`),  the second = is checked first. To the left of it is `0 + 0`, which is by definition identical to `0`. applying `rw zero_add` here, the term is converted to `n`. For number 2, you see `0 + 0`, determine that it is of the desired form and convert it to `0`.

## `obtain`

**Summary:** The `obtain` tactic can be used to merge `have` and `cases` into one command.

**Examples:**

**Proof state** **Command** **New proof state**
------------------------------------------ --------------------------- -------------------------------------
`f : ℕ → ℕ → Prop` `obtain ⟨ m, hm ⟩` `f: ℕ → ℕ → Prop`
`h : ∀ (n : ℕ), ∃ (m : ℕ), f n m` ` := h 27,` `h : ∀ (n : ℕ), ∃ (m : ℕ), `
` f n m`
`m : ℕ`
`hm : f 27 m`

## `push_neg`

**Summary:** In many steps of a proof, a negation must be carried out. In order to process the corresponding quantifiers etc. as well and to better reusable, the tactic `push_neg` is available.

**Examples**
+---------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:====================+:=============+:======================+
| `⊢ ¬(P ∨ Q)` | | |
| | | |
| & | | |
| | | |
| `push_neg,` | | |
| | | |
| & | | |
| | | |
| `⊢ ¬P ∧ ¬Q` | | |
+---------------------+--------------+-----------------------+

**Notes:**

This tactic also works with other objects, such as sets.

## `rcases`

+-------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=============+:======================+
| `h : P ∧ Q ∨ P ∧ R`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| `(⟨hP1,hQ⟩|⟨hP2,hR⟩),` | | |
| | | |
| & | | |
| | | |
| `hP1 : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ P`\ | | |
| `hP2 : P `\ | | |
| `hR : R`\ | | |
| `⊢ P` | | |
+-------------------------------+--------------+-----------------------+

**Summary:** `rcases` is a more flexible version of `cases`. Here, it is allowed to use `⟨ hP, hQ ⟩` (or `(hP | hQ)`) to to split the hypotheses `hP` and `hQ` into their cases.  As can be seen in the example above, it is also possible to nest `⟨.,.⟩` and `(.|.)`.

**Examples:**

+----------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:=============+:======================+
| `h : P ∧ Q`\ | | |
| `⊢ R` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| ` ⟨ hP, hQ ⟩` | | |
| | | |
| & | | |
| | | |
| `hP : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ R` | | |
+----------------------------+--------------+-----------------------+

**Notes:**

The last example shows how to use `rcases` to directly resolve a `∃` quantifier in a hypothesis that has more than one constraint (here: `0 ≤ m)` and `m < n` can be resolved directly.

## `refine`

**Summary:** The `refine` tactic is like `exact` with holes. More precisely: if the goal is to apply a combination of hypotheses, you can do that with 'refine' and write an open term '_' for each. You then get each '_' back as a new goal (where those with definitional equality are solved immediately).

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `hQ : Q` | `refin | `hQ : Q` |
| | e ⟨ _, hQ ⟩,` | |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q` | | `⊢ P` |
+----------------------+----------------------+----------------------+
| `⊢ ∃ (n : ℕ) (h | | |
| : n > 0), `\ | | |
| ` | | |
| n ^ 2 = 9` | | |
| | | |
| & | | |
| | | |
| `refine `\ | | |
| `⟨3, _, b | | |
| y norm_num⟩,` | | |
| | | |
| & | | |
| | | |
| `⊢ 3 > 0` | | |
+----------------------+----------------------+----------------------+

## `refl`

**Summary:** This tactic proves the equality (or equivalence) of two definitionally equal terms.

**Examples:**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ P ↔ P` or | `refl,` | **goals accomplished ** |
+-------------------------+----------------+-------------------------+
| `⊢ P = P` | | |
+-------------------------+----------------+-------------------------+
| `⊢ 1 + 2 = 3` | | |
| | | |
| & | | |
| | | |
| `refl,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+-------------------------+----------------+-------------------------+

**Notes:**

The second example works because both sides are by definition equal to `succ succ succ 0`.

## `revert`

**Summary:** `revert` is the opposite of `intro`: It takes a hypothesis from the local context and inserts it as a precondition into the goal.

**Examples**

+--------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:=============+:======================+
| `hP : P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `revert hP` | | |
| | | |
| & | | |
| | | |
| `⊢ P → Q` | | |
+--------------------+--------------+-----------------------+

**Notes:**

`revert` is rarely needed; actually only when you want to apply an already proven result exactly and first want to establish the correct form of the goal.

## `right`

**Summary:** See `left`, where the adjustments are obvious.

**Examples**

**Proof state** **command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∨ Q` `right,` `⊢ Q`

## `ring`

**Summary:** The `ring` uses rules of calculation such as associativity, commutativity, and distributivity to achieve the goal.

**Examples**

+------------------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================================+:===============+:========================+
| `x y : ℝ` | `ring,` | **goals accomplished ** |
+------------------------------------+----------------+-------------------------+
| `⊢ x + y = y + x`[^12] | | |
+------------------------------------+----------------+-------------------------+
| `n : ℕ`\ | | |
| `⊢ (n+1)^2 = n^2 + 2*n + 1` | | |
| | | |
| & | | |
| | | |
| `ring,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+------------------------------------+----------------+-------------------------+

**Notes:**

* The second example works even though `ℕ` is not a ring (but only a half-ring). It would also work with `n : ℝ` (since `ℝ` has more calculation rules than `ℕ`).
* `ring` is only used to close the goal.


## `rintro`

**Summary:** The `rintro` tactic is used to process several `intro` and `cases` tactics on one line.

**Examples**

**Proof state** **Command** **New proof state**
---------------------- ------------------------------ -----------------------
`⊢ P ∨ Q → R` `rintro ( hP | hQ ),` `hP : P`
$=$ `⊢ P`
`intro h,` `hQ : Q`
`cases h with hP hQ,` `⊢ Q`
`⊢ P ∧ Q → R` `rintro ⟨ hP , hQ ⟩,` `hP : P`
$=$ `hQ : Q`
`intro h,` `⊢ Q`
`cases h with h1 h2,`

**Notes:**

Here, more than two `∨` can also be split into cases in one step: With `A ∨ B ∨ C`, `rintro (A | B | C)` introduces three goals.

## `rw`

**Summary:** `rw` stands for *rewrite*. For `rw h` to work, `h` must be an expression of the type `h : x=y` or `h : A↔B`. In this case, `rw h`  replaces every term that is syntactically identical to `x` (or `A`) is replaced by `y` (or `B`). This also works if `h` is an already proven result (i.e. a `lemma` or `theorem`). With `rw ← h` is applied from right to left. (In the above example, `y` is replaced by `x` and `B` by `A`.)

**Examples**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `h : P ↔ Q` | `rw h,` | `h : P ↔ Q` |
+----------------------+----------------------+----------------------+
| `⊢ P` | | `⊢ Q` |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q` | `rw ← h,` | `h : P ↔ Q` |
+----------------------+----------------------+----------------------+
| `⊢ Q` | | `⊢ P` |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q` | `rw h at hP,` | `h : P ↔ Q` |
+----------------------+----------------------+----------------------+
| `hP : P` | | `hP : Q` |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q` | `r | `h : P ↔ Q` |
| | w ← h at hQ,` | |
+----------------------+----------------------+----------------------+
| `hQ : Q` | | `hQ : P` |
+----------------------+----------------------+----------------------+
| `k m: ℕ`\ | | |
| `⊢ k + m + 0 | | |
| = m + k + 0` | | |
| | | |
| & | | |
| | | |
| ` | | |
| rw add_comm,` | | |
| | | |
| & | | |
| | | |
| `k m: ℕ`\ | | |
| `⊢ | | |
| 0 + (k + m)`\ | | |
| ` | | |
| = m + k + 0` | | |
+----------------------+----------------------+----------------------+

For the last four examples, you first need to know that `add_comm` and `add_zero` are the statements

```
add_comm : ∀ {G : Type} [_inst_1 : add_comm_semigroup G] (a b : G),
a + b = b + a
add_zero : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), a + 0 = a
```

In the first of the four examples, `rw` applies to the first occurrence of a term of type `a + b`. Due to the internal bracketing, `(k + m) + 0` is on the left side, so that the `rw` results in a `0 + k + m`. If you want to use the commutativity in the term `k + m`, you need the second (or third) example, where `rw add_comm k m` leads to the desired progress. In the last example, the two `+ 0` terms are first eliminated by `rw add_zero`.

**Notes**

* `rw` is used very often in practice to apply statements from the `mathlib` (at least if they are of the type `=` or `↔`).
* If you want to combine several `rw` commands, you can do so in square brackets, for example `rw [h1, h2]` or `rw [h1, ←h2, h3]`.
* `rw` immediately executes a `refl` after its application. This leads to the second and third examples of the applications of `add_comm` and `add_zero` that the new proof state is not as specified, but **no goals**.
* If you do not want to perform a `rw` in sequence (as in the double elimination of the `+0` above), you can use `nth_rewrite` to rewrite the second occurrence of a term.
* The `rw` tactic does not work when it comes after a *binder*, which could be a `∀ ∃ ∑`. In this case, `simp_rw` will hopefully help.

## `simp`

**Summary:** In `mathlib` there are many lemmas with `=` or `↔` statements that can be applied with `rw` and are marked with `@[simp]`. These marked lemmas have the property that the right side is a simplified form of the left side. With `simp`, `lean` looks for matching lemmas and tries to apply them.

**Examples**

+----------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:=============+:======================+
| `⊢ n + 0 = n` [^13] | | |
| | | |
| & | | |
| | | |
| `simp,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+----------------------------+--------------+-----------------------+

**Notes:**

If you want to know which lemmas were used, try 'simp?` or 'squeeze_simp`. This provides clues.

+---------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:================================+:=============+:======================+
| `⊢ n + 0 = n` | | |
| | | |
| & | | |
| | | |
| `simp?,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished **\ | | |
| Try this:\ | | |
| `simp only [add_zero, `\ | | |
| ` eq_self_iff_true]` | | |
+---------------------------------+--------------+-----------------------+

## `specialize`

**Proof state** **Command** **New proof state**
----------------------------- --------------------------- -----------------------
`f : ℕ → Prop` `specialize h 13,` `f: ℕ → Prop`
`h : ∀ (n : ℕ), f n` `h : f 13`
`⊢ P` `⊢ P`

**Summary:** In a hypothesis `h : ∀ n, ...`, `...` applies to all `n`, but for the proof of the goal, you may only need a specific `n`. If you specify `specialize h` followed by the value for which `h` is needed, the hypothesis changes accordingly.

**Examples** {#beispiele-31 .unnumbered}

+-----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==================================+:=============+:======================+
| `h: ∀ (n : ℕ), 0 < n + 1`\ | | |
| `⊢ 0 < 1` | | |
| | | |
| & | | |
| | | |
| `specialize h 0,` | | |
| | | |
| & | | |
| | | |
| `m : ℕ`\ | | |
| `h: 0 < 0 + 1`\ | | |
| `⊢ 0 < 1` | | |
+-----------------------------------+--------------+-----------------------+

**Notes**

* Just as with `use`, you have to be careful that the goal remains provable.
* If you want to use two values of the hypothesis `h`, then `let h' := h` first provides a duplication of the hypothesis, so that you can then apply `specialize` to `h` and `h'`.

## `constructor`

**Summary:** If the goal is of the type `⊢ P ∧ Q`, it is replaced by `constructor` into two goals `⊢ P` and `⊢ Q`.

**Examples** {#beispiele-32 .unnumbered}

**Proof state** **Command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∧ Q` `split,` `⊢ P`
`⊢ Q`
`⊢ P ↔ Q` `split,` `⊢ P → Q`
`⊢ Q → P`

**Notes**

Note that `⊢ P ↔ Q` is identical to `⊢ (P → Q) ∧ (Q → P)`.

## `tauto`

**Summary:** `tauto` solves all goals that can be solved with a truth table.

**Examples**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `⊢ P | `tauto,` or | **goals accomplished |
| ∧ Q → P`[^15] | `tauto!,` | ** |
+----------------------+----------------------+----------------------+
| `⊢ ((P → | | |
| Q) → P) → P` | | |
| | | |
| & | | |
| | | |
| `tauto!, ` | | |
| | | |
| & | | |
| | | |
| **goals accomplished | | |
| ** | | |
+----------------------+----------------------+----------------------+

The truth tables for `¬P`, `P ∧ Q` and `P ∨ Q` are as follows; if more terms of type `Prop` are involved, there are more lines.

::: center
`P` `¬P`
---------------- ----------------
`true` `false`
`false` `true`

`P` `Q` `(P ∧ Q)`
---------------- ---------------- ------------------
`true` `true` `true`
`false` `true` `false`
`true` `false` `false`
`false` `false` `false`

`P` `Q` `(P ∨ Q)`
---------------- ---------------- ------------------
`true` `true` `true`
`false` `true` `true`
`true` `false` `true`
`false` `false` `false`
:::

**Notes**

The difference between `tauto` and `tauto!` is that in the latter tactic, the rule of the excluded middle is allowed.  The second example can therefore only be solved with `tauto!`, but not with `tauto`.

## `triv`

**Summary**

`triv` solves an objective that is, by definition, identical to `true`. It also solves objectives that can be solved with `refl`
.

**Examples**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ true` | `triv,` | **goals accomplished ** |
+-------------------------+----------------+-------------------------+
| `⊢ x=x` | | |
| | | |
| & | | |
| | | |
| `triv,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+-------------------------+----------------+-------------------------+

## `use`

**Proof state** **Command** **New proof state**
--------------------------- ----------------- -----------------------
`f : α → Prop` `use y,` `f : α → Prop`
`y : α` `y : α`
⊢ ∃ (x : α), f x` ⊢ f y`

**Summary:** The `use` tactic is used for goals that begin with ∃. Here, parameters are used to indicate which object quantified by ∃ is to be reused in the proof.

**Examples**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ ∃ (k : ℕ), k * k = 16` | | |
| | |
| & | | |
| | |
| `use 4, ` | | |
| | | |
| & | | |
| | | |
| `⊢ 4 * 4 = 16` | | |
+----------------------------------+--------------+-----------------------+
