/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro
  left
  assumption
  done

example : Q → P ∨ Q := by
  intro
  right
  assumption
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases' h1 with hp hq
  . apply h2
    assumption
  . apply h3
    assumption
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases' h1 with hp hq
  . right
    assumption
  . left
    assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . rintro ((hp | hq) | hr)
    . left
      assumption
    . right
      left
      assumption
    . right
      right
      assumption
  . rintro (hp | hq | hr)
    . left
      left
      assumption
    . left
      right
      assumption
    . right
      assumption
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1
  intro h2
  intro h3
  cases' h3 with hp hq
  . left
    apply h1
    assumption
  . right
    apply h2
    assumption
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1
  intro h2
  cases' h2 with hp hr
  . left
    apply h1
    assumption
  . right
    assumption
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1
  intro h2
  constructor
  . intro hpq
    cases' hpq with hp hq
    . left
      rw [h1] at hp
      assumption
    . right
      rw [h2] at hq
      assumption
  . intro hrs
    cases' hrs with hr hs
    . left
      rw [h1]
      assumption
    . right
      rw [h2]
      assumption
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP
    · intro hQ
      apply h
      right
      exact hQ
  · rintro ⟨hnP, hnQ⟩ (hP | hQ)
    · apply hnP; exact hP
    · exact hnQ hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_cases hp : P
    . right
      intro hq
      apply h
      exact ⟨hp, hq⟩
    . left
      exact hp
  . rintro (hnp | hnq) ⟨hp, hq⟩
    . apply hnp; exact hp
    . apply hnq; exact hq
  done
