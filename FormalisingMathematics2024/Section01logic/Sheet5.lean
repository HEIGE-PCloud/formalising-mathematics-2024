/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h
  rw [h]
  intro h
  rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  rw [hpq]
  assumption
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  . rintro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · rintro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩
  done

example : P ↔ P ∧ True := by
  constructor
  . intro hp
    constructor
    . assumption
    . triv
  . intro ⟨hp, _⟩
    assumption
  done

example : False ↔ P ∧ False := by
  constructor
  · rintro ⟨⟩
  · rintro ⟨-, ⟨⟩⟩
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq
  intro hrs
  rw [hpq, hrs]
  done

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  . apply h1 <;>
    assumption
  . apply h1 <;>
    apply h2 <;>
    assumption
  done
