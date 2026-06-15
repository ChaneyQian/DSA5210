import EqualityForward
import EqualityBackward

open scoped BigOperators

/-!
# Mantel.lean — Integration

Combines the forward direction (People2, `EqualityForward.lean`) and the
backward direction (Person 3, `EqualityBackward.lean`) into the full equality
characterization of Mantel's theorem.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Mantel's theorem, equality characterization.**
A triangle-free graph on `n` vertices attains `⌊n²/4⌋` edges if and only if it
is a balanced complete bipartite graph. -/
theorem mantel_equality_characterization :
    (TriangleFree G ∧
      G.edgeFinset.card = (Fintype.card V) * (Fintype.card V) / 4)
    ↔ IsBalancedCompleteBipartite G := by
  constructor
  · intro h
    exact mantel_equality_forward G h.1 h.2
  · intro h
    exact mantel_equality_backward G h

#print axioms mantel_equality_characterization
