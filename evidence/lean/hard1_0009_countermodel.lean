import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000000
def submission : Goal := by
  let m : Magma (Fin 6) := {
    op := finOpTable "[[2, 2, 2, 2, 2, 2], [3, 5, 1, 5, 5, 5], [4, 4, 4, 4, 4, 4], [1, 1, 5, 1, 3, 1], [0, 0, 0, 0, 0, 0], [5, 3, 3, 3, 1, 3]]"
  }
  refine ⟨Fin 6, m, ?_⟩
  decideFin!
