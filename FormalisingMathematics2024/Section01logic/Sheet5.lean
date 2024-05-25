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
  intro h1
  rw [h1]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw [h1]
  intro h2
  rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  constructor
  intro h3
  cases' h2 with h2r h2l
  cases' h1 with h1r h1l
  apply h2r
  apply h1r
  exact h3
  intro h4
  cases' h1 with h1r h1l
  cases' h2 with h2r h2l
  apply h1l
  apply h2l
  exact h4


  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  cases' h1 with h1P h1Q
  constructor
  exact h1Q
  exact h1P
  intro h2
  cases' h2 with h2Q h2P
  constructor
  exact h2P
  exact h2Q
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  --constructor
  cases' h1 with hPQ hR
  cases' hPQ with hP hQ
  constructor
  exact hP
  constructor
  exact hQ
  exact hR
  intro h2
  cases' h2 with hP hQR
  cases' hQR with hQ hR
  constructor
  constructor
  exact hP
  exact hQ
  exact hR
  done

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  triv
  intro hP
  cases' hP with hP1
  exact hP1
  done

example : False ↔ P ∧ False := by
  constructor
  intro h
  constructor
  exfalso
  exact h
  exact h
  intro h1
  cases' h1 with hP hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1
  intro h2
  constructor
  cases' h1 with hPQ hQP
  cases' h2 with hRS hSR
  intro hPR
  cases' hPR with hP hR
  constructor
  apply hPQ
  exact hP
  apply hRS
  exact hR
  rw [h1]
  rw [h2]
  intro h3
  exact h3
  done

example : ¬(P ↔ ¬P) := by
  intro h

  cases' h with hP hnP
  apply hP
  apply hnP
  by_contra hX
  apply hP
  exact hX
  exact hX
  by_contra hY
  apply hP
  apply hnP
  exact hY
  apply hnP
  exact hY
  done
