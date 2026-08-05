import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have lemma : ∀ a b c d : G, (a ◇ ((b ◇ c) ◇ d)) = (a ◇ b) := by
    intro a b c d
    have E1 : ∀ (v0 v1 v2 v3 v4 : G), (v0 ◇ (v1 ◇ v2)) = (v0 ◇ (v1 ◇ v3)) := by intro v0 v1 v2 v3 v4; have ia := h ((v0 ◇ (v1 ◇ v3))) v1 v4 v2; have ib := h v0 v1 v3 v4; have step : (((v0 ◇ (v1 ◇ v3)) ◇ (v1 ◇ v4)) ◇ (v1 ◇ v2)) = (v0 ◇ (v1 ◇ v2)) := congrArg (fun __pc_hole => (__pc_hole ◇ (v1 ◇ v2))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E2 : ∀ (v0 v1 v2 v3 v4 v5 : G), ((v0 ◇ v1) ◇ ((v1 ◇ (v2 ◇ v3)) ◇ v4)) = v0 := by intro v0 v1 v2 v3 v4 v5; have ia := h v0 ((v1 ◇ (v2 ◇ v3))) ((v2 ◇ v5)) v4; have ib := h v1 v2 v3 v5; have step : ((v0 ◇ ((v1 ◇ (v2 ◇ v3)) ◇ (v2 ◇ v5))) ◇ ((v1 ◇ (v2 ◇ v3)) ◇ v4)) = ((v0 ◇ v1) ◇ ((v1 ◇ (v2 ◇ v3)) ◇ v4)) := congrArg (fun __pc_hole => ((v0 ◇ __pc_hole) ◇ ((v1 ◇ (v2 ◇ v3)) ◇ v4))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E10 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 : G), (v0 ◇ v1) = (v0 ◇ ((v1 ◇ v2) ◇ v3)) := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8; have ia := E1 v0 ((v1 ◇ v2)) (((v2 ◇ (v4 ◇ v5)) ◇ v6)) v3 v7; have ib := E2 v1 v2 v4 v5 v6 v8; have step : (v0 ◇ ((v1 ◇ v2) ◇ ((v2 ◇ (v4 ◇ v5)) ◇ v6))) = (v0 ◇ v1) := congrArg (fun __pc_hole => (v0 ◇ __pc_hole)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 v2 v3 : G), (v0 ◇ v1) = (v0 ◇ ((v1 ◇ v2) ◇ v3)) := fun v0 v1 v2 v3 => E10 v0 v1 v2 v3 v0 v0 v0 v0 v0
    exact (target a b c d).symm
  intro x y z
  have f49 := lemma x y z x
  calc
    (x ◇ y) = (x ◇ ((y ◇ z) ◇ x)) := by simpa using f49.symm
