# MantelA3 — Mantel's Theorem Equality Characterization (Integrated)

Fully verified Lean 4 + Mathlib formalization of the equality case of Mantel's
theorem, integrating all three team members' work.

## Main result

```lean
theorem mantel_equality_characterization
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (TriangleFree G ∧
      G.edgeFinset.card = (Fintype.card V) * (Fintype.card V) / 4)
    ↔ IsBalancedCompleteBipartite G
```

**`#print axioms mantel_equality_characterization`**
→ `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no custom axioms.**
Zero `sorry` tactics across the entire project.

## Files & ownership

| File | Owner | Content |
|------|-------|---------|
| `Formalization.lean` | A2 (prior) | `TriangleFree`, `mantel_bound`, max-degree partition lemmas |
| `CompleteBipartite.lean` | Person 1 | complete-bipartite predicates + structural lemmas |
| `Arithmetic.lean` | Person 3 | `arithmetic_balanced_of_product_eq_floor`, `balanced_product_eq_floor` |
| `EqualityForward.lean` | **People2** | forward direction `mantel_equality_forward` |
| `EqualityBackward.lean` | Person 3 | backward direction `mantel_equality_backward` + `complete_bipartite_edge_card` |
| `Mantel.lean` | integration | final `mantel_equality_characterization` iff |

## Dependency graph

```
Formalization (A2)
   ├──────────────┐
CompleteBipartite  │
   ├──────┬────────┤
Arithmetic │        │
   │   EqualityForward (People2)
   │        │
EqualityBackward (Person3)
   └────────┴───→ Mantel  (final iff)
```

## Build / verify

```bash
lake exe cache get      # pull prebuilt Mathlib (toolchain v4.31.0-rc1)
lake build              # → 2960 jobs, 0 errors
lake env lean Mantel.lean   # prints the axiom list for the final theorem
```

## Per-theorem axiom status (all clean)

| Theorem | Axioms |
|---------|--------|
| `mantel_equality_forward` | propext, Classical.choice, Quot.sound |
| `mantel_equality_backward` | propext, Classical.choice, Quot.sound |
| `mantel_equality_characterization` | propext, Classical.choice, Quot.sound |
