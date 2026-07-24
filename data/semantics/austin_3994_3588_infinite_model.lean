import JudgeProblem
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

-- Adapted from InfModel.Equation3994_not_implies_Equation3588 in the
-- Equational Theories Project at commit
-- df8184f8ae59c71d6f5463b71682d871823a779c.
def submission : Goal := by
  let magN : Magma ℕ := ⟨fun x y ↦ if Even x ∧ Even y then x ^^^ y else if Even y then y + 2
    else if Even x then x - 2 else 0⟩
  use ℕ, magN
  have range : ∀ x y : ℕ, Even (x ◇ y : ℕ) := by
    intro x y
    unfold magN
    simp
    split_ifs
    · simp_all
    · simpa [Nat.even_add]
    · by_cases x < 2
      · rw [Nat.sub_eq_zero_of_le]
        simp
        omega
      rw [Nat.even_sub]
      · simp_all
      · omega
    · exact .zero
  constructor
  · intro x y z
    generalize h : x ◇ y = v
    have : Even v := by rw [← h]; apply range
    unfold magN
    by_cases hz : Even z
    · simp [this, hz, Nat.xor_comm]
    · simp [hz, this, Nat.even_add]
  simp only [not_forall]
  use 1, 1, 1
  unfold magN
  simp
