/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro ht
  apply ht
  triv
  done

example : False → ¬True := by
  intro hf
  intro
  exact hf
  done

example : ¬False → True := by
  intro
  triv
  done

example : True → ¬False := by
  intro
  intro hf
  exact hf
  done

example : False → ¬P := by
  intro hf
  intro
  exact hf
  done

example : P → ¬P → False := by
  intro hp
  intro hnp
  apply hnp
  exact hp
  done

example : P → ¬¬P := by
  intro hp
  intro hnp
  apply hnp
  exact hp
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hpq
  intro hnq
  intro hp
  apply hnq
  apply hpq
  exact hp
  done

example : ¬¬False → False := by
  intro hnnf
  apply hnnf
  intro hf
  exact hf
  done

example : ¬¬P → P := by
  intro hnnp
  by_contra hnp
  apply hnnp
  exact hnp
  done

example : (¬Q → ¬P) → P → Q := by
  intro h1
  intro hp
  by_contra h
  apply h1 at h
  apply h
  exact hp
  done
