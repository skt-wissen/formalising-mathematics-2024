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
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases' h1 with hP hQ
  apply h2
  exact hP
  apply h3
  exact hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases' h1 with hP hQ
  right
  exact hP
  left
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h1
  cases' h1 with hPQ hR
  cases' hPQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR
  intro h1
  cases' h1 with hP hQR
  left
  left
  exact hP
  cases' hQR with hQ hR
  left
  right
  exact hQ
  right
  exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1
  intro h2
  intro h3
  cases' h3 with hP hQ
  left
  apply h1
  exact hP
  right
  apply h2
  exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1
  intro h2
  cases' h2 with hP hR
  left
  apply h1
  exact hP
  right
  exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1
  intro h2
  constructor
  rw [h1]
  rw [h2]
  intro h
  apply h
  rw [h1]
  rw [h2]
  intro h
  apply h
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h1
  constructor
  intro hP
  apply h1
  left
  exact hP
  intro hQ
  apply h1
  right
  exact hQ
  intro h1
  cases' h1 with hnP hnQ
  intro h2
  cases' h2 with hP hQ
  apply hnP
  exact hP
  apply hnQ
  exact hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro hnPQ
  by_cases hP:P
  right
  intro hQ
  apply hnPQ
  constructor
  exact hP
  exact hQ
  left
  exact hP

  intro h
  cases' h with hnP hnQ
  intro hPQ
  cases' hPQ with hP hQ
  apply hnP
  exact hP
  intro hPQ
  cases' hPQ with hP hQ
  apply hnQ
  exact hQ
  done
