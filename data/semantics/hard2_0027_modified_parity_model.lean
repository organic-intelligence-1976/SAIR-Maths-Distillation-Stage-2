import JudgeProblem
import Mathlib.Tactic

-- Provenance: equational-theories@7e276a2d05e84e3eef02432abfd0718e78f7abfa,
-- equational_theories/ManuallyProved/Equation1659.lean, theorem
-- Equation1659_facts. Dualizing that model gives an E2000 model refuting
-- E1721; E2000 implies E1167 and E1763 implies E1721. The operation below is
-- the resulting patched parity walk on the natural numbers.
def submission : Goal := by
  let parity : Nat → Bool :=
    fun n => Nat.rec true (fun _ value => Bool.not value) n
  let op (x y : Nat) :=
    match parity x, parity y with
    | true, true => Nat.succ y
    | false, false => Nat.succ y
    | _, _ => Nat.pred y
  let model : Magma Nat := ⟨op⟩
  use Nat, model
  have parity_zero : parity Nat.zero = true := by
    rfl
  have parity_succ (n : Nat) :
      parity (Nat.succ n) = Bool.not (parity n) := by
    rfl
  have parity_double_succ (n : Nat) :
      parity (Nat.succ (Nat.succ n)) = parity n := by
    calc
      parity (Nat.succ (Nat.succ n)) =
          Bool.not (parity (Nat.succ n)) := parity_succ (Nat.succ n)
      _ = Bool.not (Bool.not (parity n)) :=
        congrArg Bool.not (parity_succ n)
      _ = parity n := by
        cases parity n <;> rfl
  have pred_succ_local (n : Nat) : Nat.pred (Nat.succ n) = n := by
    rfl
  have op_false_false (a x : Nat)
      (ha : parity a = false) (hx : parity x = false) :
      op a x = Nat.succ x := by
    unfold op
    rw [ha, hx]
  have op_false_true (a x : Nat)
      (ha : parity a = false) (hx : parity x = true) :
      op a x = Nat.pred x := by
    unfold op
    rw [ha, hx]
  have op_true_false (a x : Nat)
      (ha : parity a = true) (hx : parity x = false) :
      op a x = Nat.pred x := by
    unfold op
    rw [ha, hx]
  have op_true_true (a x : Nat)
      (ha : parity a = true) (hx : parity x = true) :
      op a x = Nat.succ x := by
    unfold op
    rw [ha, hx]
  have op_self (a : Nat) : op a a = Nat.succ a := by
    cases ha : parity a <;>
      unfold op <;>
      rw [ha] <;>
      rfl
  have op_left_congr (a b x : Nat) (hab : parity a = parity b) :
      op a x = op b x := by
    cases ha : parity a <;> cases hb : parity b
    · unfold op
      rw [ha, hb]
    · exfalso
      rw [ha, hb] at hab
      exact Bool.noConfusion hab
    · exfalso
      rw [ha, hb] at hab
      exact Bool.noConfusion hab
    · unfold op
      rw [ha, hb]
  have op_invol (a x : Nat) : op a (op a x) = x := by
    cases ha : parity a
    · exact Nat.rec
        (motive := fun value => op a (op a value) = value)
        (by
          have h1 : op a Nat.zero = Nat.zero := by
            rw [op_false_true a Nat.zero ha parity_zero]
            rfl
          calc
            op a (op a Nat.zero) = op a Nat.zero := congrArg (op a) h1
            _ = Nat.zero := h1)
        (fun n _ => by
          cases hn : parity n
          · have hs : parity (Nat.succ n) = true := by
              calc
                parity (Nat.succ n) = Bool.not (parity n) := parity_succ n
                _ = true := by
                  rw [hn]
                  rfl
            rw [
              op_false_true a (Nat.succ n) ha hs,
              pred_succ_local n,
              op_false_false a n ha hn,
            ]
          · have hs : parity (Nat.succ n) = false := by
              calc
                parity (Nat.succ n) = Bool.not (parity n) := parity_succ n
                _ = false := by
                  rw [hn]
                  rfl
            have hss : parity (Nat.succ (Nat.succ n)) = true :=
              (parity_double_succ n).trans hn
            rw [
              op_false_false a (Nat.succ n) ha hs,
              op_false_true a (Nat.succ (Nat.succ n)) ha hss,
              pred_succ_local (Nat.succ n),
            ])
        x
    · exact Nat.rec
        (motive := fun value => op a (op a value) = value)
        (by
          have hs : parity (Nat.succ Nat.zero) = false := by
            calc
              parity (Nat.succ Nat.zero) =
                  Bool.not (parity Nat.zero) := parity_succ Nat.zero
              _ = false := by
                rw [parity_zero]
                rfl
          have h1 : op a Nat.zero = Nat.succ Nat.zero :=
            op_true_true a Nat.zero ha parity_zero
          have h2 : op a (Nat.succ Nat.zero) = Nat.zero := by
            calc
              op a (Nat.succ Nat.zero) = Nat.pred (Nat.succ Nat.zero) :=
                op_true_false a (Nat.succ Nat.zero) ha hs
              _ = Nat.zero := pred_succ_local Nat.zero
          calc
            op a (op a Nat.zero) = op a (Nat.succ Nat.zero) :=
              congrArg (op a) h1
            _ = Nat.zero := h2)
        (fun n _ => by
          cases hn : parity n
          · have hs : parity (Nat.succ n) = true := by
              calc
                parity (Nat.succ n) = Bool.not (parity n) := parity_succ n
                _ = true := by
                  rw [hn]
                  rfl
            have hss : parity (Nat.succ (Nat.succ n)) = false :=
              (parity_double_succ n).trans hn
            rw [
              op_true_true a (Nat.succ n) ha hs,
              op_true_false a (Nat.succ (Nat.succ n)) ha hss,
              pred_succ_local (Nat.succ n),
            ]
          · have hs : parity (Nat.succ n) = false := by
              calc
                parity (Nat.succ n) = Bool.not (parity n) := parity_succ n
                _ = false := by
                  rw [hn]
                  rfl
            rw [
              op_true_false a (Nat.succ n) ha hs,
              pred_succ_local n,
              op_true_true a n ha hn,
            ])
        x
  have middle_parity (z y : Nat) :
      parity (op z (op y y)) = parity y := by
    rw [op_self]
    cases hz : parity z
    · cases hy : parity y
      · have hs : parity (Nat.succ y) = true := by
          calc
            parity (Nat.succ y) = Bool.not (parity y) := parity_succ y
            _ = true := by
              rw [hy]
              rfl
        rw [
          op_false_true z (Nat.succ y) hz hs,
          pred_succ_local y,
        ]
        exact hy
      · have hs : parity (Nat.succ y) = false := by
          calc
            parity (Nat.succ y) = Bool.not (parity y) := parity_succ y
            _ = false := by
              rw [hy]
              rfl
        rw [op_false_false z (Nat.succ y) hz hs]
        exact (parity_double_succ y).trans hy
    · cases hy : parity y
      · have hs : parity (Nat.succ y) = true := by
          calc
            parity (Nat.succ y) = Bool.not (parity y) := parity_succ y
            _ = true := by
              rw [hy]
              rfl
        rw [op_true_true z (Nat.succ y) hz hs]
        exact (parity_double_succ y).trans hy
      · have hs : parity (Nat.succ y) = false := by
          calc
            parity (Nat.succ y) = Bool.not (parity y) := parity_succ y
            _ = false := by
              rw [hy]
              rfl
        rw [
          op_true_false z (Nat.succ y) hz hs,
          pred_succ_local y,
        ]
        exact hy
  constructor
  · intro x y z
    change x = op y (op (op z (op y y)) x)
    rw [op_left_congr (op z (op y y)) y x (middle_parity z y)]
    exact (op_invol y x).symm
  · intro goal_holds
    have h := goal_holds Nat.zero (Nat.succ Nat.zero) Nat.zero
    change Eq Nat.zero (
      op
        (op (Nat.succ Nat.zero) Nat.zero)
        (op (op Nat.zero Nat.zero) Nat.zero)
    ) at h
    unfold op parity at h
    exact Nat.noConfusion h
