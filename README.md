```
+-----------------------+
|                       |
+----+   +--------------+
     |   |
     |   |
+----+   +--------------+
|                       |
+----+   +-----+   +----+
     |   |     |   |
     |   |     |   |
     |   +-----+   |
     |             |
     |   +---------+
     |   |
     |   |
     +---+
```

# The Ponens Agda library

This is a library of Agda code with common utilities, functions, and data structures.

Code here is experimental and will change.
It will be used as part of the Ponens optimizer, a tool that solves formally specified optimization problems using proof-space exploration.

## Contents

### Ponens.Data.FinSet

This is finite set of ordered elements.
Its primary denotation is `Pred A`, where `A` is element type.

We attempt a complete set of operations and proofs.
For proofs to be complete, each operation should be proved to respect its denotation's semantics.
To judge whether the set of operations is complete, we compare operations to other libraries, including:

- Agda's `Relation.Unary`. Those operations for unary `Pred` that are applicable to finite ordered sets should be included.
- Haskell's `Data.Set`.
- Rocq's [Stdlib.FSets.FSets](https://rocq-prover.org/doc/V9.1.0/stdlib/Stdlib.FSets.FSets.html)

`Ponens.Data.FinSet` is not yet complete but is closer to complete than the Agda stdlib's `Data.Tree.AVL.Sets`.
`FinSet` is based on the stdlib's `Data.Tree.AVL.Indexed` with more ops and proofs added as needed.

The following table lists intended operations that would make the `FinSet` complete and their current status.
For most operations, *Proved* means that the op respects the meaning of the set as a `Pred`.
Optimal means that the implementation is asymptotically optimal given a balanced tree representation.

| Op | Implemented | Proved | Optimal | Description |
| --- | --- | --- | --- | --- |
| `any?` | Y | Y | Y | Find an element that satisfies predicate |
| `all?` | Y | Y | Y | All elements satisfy predicate |
| `∈?` | Y | Y | Y | Set membership |
| `∅` | Y | Y | Y | The empty set |
| `singleton` | Y | Y | Y | Make a singleton set |
| `insert` | Y | Y | Y | Insert an element |
| `delete` | Y | Y | Y | Delete an element |
| `toList` | Y | Y | Y | Convert to `List` |
| `fromList` | Y | Y | N | Convert from `List` |
| `foldr` | Y | Y | Y | Right fold over elems |
| `foldl` | N | | | Left fold over elems |
| `fold` | N | | | Assoc fold over elems |
| `size` | Y | Y | N | Cardinality |
| `⟦size⟧` | Y | Y | N | Isomorphism to `Fin n` (converts between indices and elems) |
| `filter` | Y | Y | N | Filter on predicate |
| `partition` | Y | Y | N | Parition on predicate |
| `headTail` | Y | Y | Y | Split to head elem, tail set |
| `initLast` | Y | Y | Y | Split to init set, last elem |
| `lookup->` | Y | Y | Y | Lookup closest elem greater-than given |
| `lookup-≥` | N | | | Lookup closest elem greater-than-or-eq given |
| `lookup-<` | N | | | Lookup closest less-than given |
| `lookup-≤` | N | | | Lookup closest less-than-or-eq given |
| `range-exclusive` | Y | Y | N | Select range, excluding low and high |
| `range` | Y | Y | N | Select range, including low, excluding high |
| `split` | Y | Y | N | Split on key to to pair of sets |
| `∪` | Y | Y | N | Set union |
| `∩` | Y | Y | N | Set intersection |
| `∖` | Y | Y | N | Set difference |
| `Empty?` | Y | Y | Y | The set is empty |
| `Satisfiable?` | Y | Y | Y | The set is satisfiable |
| `symmetricDifference` | Y | Y | N | Set symmetric difference |
| `⊆?` | Y | Y | N | Is subset |
| `⊂?` | Y | Y | N | Is strict subset |
| `≐?` | Y | Y | N | Sets have same elements |
| `≬` | Y | Y | N | Sets share an element |
| `⟨×⟩` | N | | | Cartesian product |
| `⟨⊎⟩` | N | | | Disjoint union |
| `⟨⊙⟩` | N | | | Sum over two elements |
| `~` | N | | | Converse (i.e. swap each pair) |
| `⟨∘⟩` | N | | | Composition (i.e. natural join on tables) |
| `//` | N | | | Post division |
| `\\\\` | N | | | Pre division |
| `map` | Y | Y | N | Map a function on the set |
| `powerSet` | N | | | Set of subsets |
| `lex-strictTotalOrder` | Y | Y | Y | Sets are decidably totally ordered, lexicographically |
| `⊂-isStrictPartialOrder` | Y | Y | N | Sets are decidably partially ordered by inclusion |
| `toGeneric` | N | | | Convert to a generic and serializable representation |
| `fromGeneric` | N | | | Convert from a generic and serializable representation |

The following table lists algebraic properties of operations and relations.
Because ops are proved to follow the denotation's semantics, other properties of ops can be inherited from `Pred`'s properties.

| Op | Proved | Description |
| --- | --- | --- |
| `≐` eq | Y | Properties of `≐` being an equivalence relation from `lex-isStrictTotalOrder` |
| `⊂` strict | Y | Properties of `⊂` being a strict partial order from `⊂-isStrictPartialOrder` |
| `⊆` partial | Y | Properties of `⊆` being a partial order from `⊂-isStrictPartialOrder` |
| `∩-cong` | Y | `∩` is congruent |
| `∩-comm` | Y | `∩` is commutative |
| `∩-assoc` | Y | `∩` is associative |
| `∩-idem` | Y | `∩` is idempotent |
| `∩-zeroˡ` | Y | `∅` is `∩`'s left zero |
| `∩-zeroʳ` | Y | `∅` is `∩`'s right zero |
| `∪-cong` | Y | `∪` is congruent |
| `∪-comm` | Y | `∪` is commutative |
| `∪-assoc` | Y | `∪` is associative |
| `∪-idem` | Y | `∪` is idempotent |
| `∪-identityˡ` | Y | `∅` is `∪`'s left identity |
| `∪-identityʳ` | Y | `∅` is `∪`'s right identity |
