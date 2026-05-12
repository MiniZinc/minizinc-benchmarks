# Pattern Set Mining (MiniZinc Model)

## What problem does this model solve?

This model learns a **set of patterns** (itemsets) that separates positive examples from negative examples as well as possible.

You can think of this as a concept-learning task: given transactions labeled **positive** and **negative**, the model builds a small set of rules (patterns). A transaction is predicted positive if it is covered by at least one pattern. The goal is to maximize correct positive coverage while minimizing negative coverage.

In data-mining terms, this is a constrained optimization version of **pattern set mining** linked to learning formulas in disjunctive normal form (DNF).

---

## Inputs (given data)

- `K`: number of patterns to learn.
- `NrI`: number of items.
- `NrT_pos`: number of positive transactions.
- `NrT_neg`: number of negative transactions.
- `TDB_pos[1..NrT_pos]`: positive transaction database (each transaction is a set of item IDs).
- `TDB_neg[1..NrT_neg]`: negative transaction database.

---

## Decision variables

- `Items[d,i]` (boolean): item `i` is included in pattern `d`.
- `TransP[d,t]` (boolean): positive transaction `t` is covered by pattern `d`.
- `TransN[d,t]` (boolean): negative transaction `t` is covered by pattern `d`.
- `Trans_pos[t]` (boolean): positive transaction `t` is covered by at least one pattern.
- `Trans_neg[t]` (boolean): negative transaction `t` is covered by at least one pattern.

---

## Main modeling ideas

1. **Coverage definition for each pattern**  
   A transaction is covered by a pattern if all items selected in that pattern are present in the transaction.

2. **Closedness on positive transactions**  
   Each pattern is forced to be closed w.r.t. positive transactions: if an item appears in all currently covered positive transactions, it must be included in the pattern.

3. **Canonical ordering of patterns**  
   Lexicographic ordering constraints are used to remove symmetric duplicates (same solution represented in different pattern orders).

4. **Joint coverage across the whole pattern set**  
   A transaction is jointly covered when at least one pattern covers it.

---

## Objective

The objective is:

- maximize number of covered positive transactions
- minus number of covered negative transactions

Formally, the model maximizes:

`sum(Trans_pos) - sum(Trans_neg)`

So the best solution has high recall on positives while avoiding false positives on negatives.

---

## Output

The model prints:

- `objective`: final score
- `Items`: the learned pattern set (which items are in each pattern)

---

## Notes / possible interpretation limits

- This model uses a fixed number `K` of patterns; performance and interpretability can depend strongly on this choice.
- The model comments connect the formulation to DNF learning and CP-based itemset mining; however, this README does not map each pattern directly to a specific human-readable DNF clause format.
- If you need a strict theorem-level interpretation (e.g., exact equivalence conditions between this encoding and a DNF variant), a domain expert should verify that for your dataset and preprocessing choices.

---

## References

- Luc De Raedt, Tias Guns, and Siegfried Nijssen. _Constraint Programming for Itemset Mining_ (CP4IM project page): http://dtai.cs.kuleuven.be/CP4IM/
- Tias Guns, Siegfried Nijssen, and Luc De Raedt. _Itemset mining: A constraint programming perspective_. Artificial Intelligence, 175(12–13), 2011. DOI: https://doi.org/10.1016/j.artint.2011.05.002

## Model update summary

Added concise inline comments in pattern_set_mining.mzn to clarify:

- pattern and transaction-coverage decision variable semantics,
- objective interpretation as positive-minus-negative coverage,
- maximization intent for discriminative pattern-set quality.
