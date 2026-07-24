import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  intro x y
  have square_const : ∀ v w : G, v ◇ v = w ◇ w := by
    intro v w
    let A : G := (v ◇ (v ◇ v)) ◇ v
    have hvA : v ◇ v = A ◇ (v ◇ v) := by
      simpa [A] using h (v ◇ v) v v
    have hwA : v ◇ v = A ◇ (w ◇ w) := by
      simpa [A] using h (v ◇ v) v w
    have ev : v ◇ v = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by
      calc
        v ◇ v = ((A ◇ (v ◇ v)) ◇ A) ◇ (v ◇ v) := h (v ◇ v) A v
        _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hvA]
    have ew : w ◇ w = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by
      calc
        w ◇ w = ((A ◇ (w ◇ w)) ◇ A) ◇ (v ◇ v) := h (w ◇ w) A v
        _ = ((v ◇ v) ◇ A) ◇ (v ◇ v) := by rw [← hwA]
    exact ev.trans ew.symm
  have right_id_square : ∀ a b : G, a ◇ (b ◇ b) = a := by
    intro a b
    have sqv : a ◇ a = b ◇ b := square_const a b
    have step1 : ((b ◇ b) ◇ a) ◇ (b ◇ b) = a := by
      calc
        ((b ◇ b) ◇ a) ◇ (b ◇ b) = ((a ◇ a) ◇ a) ◇ (b ◇ b) := by rw [← sqv]
        _ = a := (h a a b).symm
    have step2 : a = a ◇ (b ◇ b) := by
      calc
        a = (((b ◇ b) ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b) := h a (b ◇ b) b
        _ = a ◇ (b ◇ b) := by rw [step1]
    exact step2.symm
  have sandwich : ∀ a b : G, (b ◇ a) ◇ b = a := by
    intro a b
    calc
      (b ◇ a) ◇ b = ((b ◇ a) ◇ b) ◇ (a ◇ a) := (right_id_square ((b ◇ a) ◇ b) a).symm
      _ = a := (h a b a).symm
  have left_sandwich : ∀ a b : G, b ◇ (a ◇ b) = a := by
    intro a b
    have d_eq_a : (((a ◇ b) ◇ a) ◇ (a ◇ b)) = a := by
      calc
        (((a ◇ b) ◇ a) ◇ (a ◇ b)) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) ◇ (a ◇ a) := (right_id_square (((a ◇ b) ◇ a) ◇ (a ◇ b)) a).symm
        _ = a := (h a (a ◇ b) a).symm
    calc
      b ◇ (a ◇ b) = (((a ◇ b) ◇ a) ◇ (a ◇ b)) := congrArg (fun u => u ◇ (a ◇ b)) (sandwich b a).symm
      _ = a := d_eq_a
  have sq_chain_1 : (x ◇ (y ◇ x)) = y := by
    exact left_sandwich y x
  have sq_chain_2 : (y ◇ (x ◇ (y ◇ x))) = (x ◇ x) := by
    calc
      (y ◇ (x ◇ (y ◇ x))) = (y ◇ y) := congrArg (fun u => y ◇ u) sq_chain_1
      _ = (x ◇ x) := square_const y x
  have sq_chain_3 : ((y ◇ (x ◇ (y ◇ x))) ◇ x) = x := by
    calc
      ((y ◇ (x ◇ (y ◇ x))) ◇ x) = ((x ◇ x) ◇ x) := congrArg (fun u => u ◇ x) sq_chain_2
      _ = x := sandwich x x
  exact sq_chain_3.symm
