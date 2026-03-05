# MiniZinc Model: Elementary Flux Mode (EFM) Identification in Metabolic Networks

## **Overview**

This MiniZinc model focuses on identifying **Elementary Flux Modes (EFMs)** in a metabolic network. EFMs are minimal sets of reactions that can operate at steady state, respecting stoichiometric and reversibility constraints. They are essential in systems biology for analysing metabolic pathways and understanding feasible reaction subsets.

---

## **Problem Description**

- **Goal:** Find a minimal support of reactions (EFM) that satisfies:

  - Steady-state conditions (no net accumulation of metabolites).
  - Reaction reversibility constraints.
  - Positive flux values for active reactions.

- **Context:**  
  Metabolic networks consist of:
  - **Metabolites:** Chemical compounds involved in reactions.
  - **Reactions:** Transformations converting metabolites.
  - **Stoichiometry matrix (S):** Represents how metabolites participate in reactions.

---

## **Inputs**

- `int: n`  
  Number of reactions.
- `int: m`  
  Number of metabolites.
- `int: k`  
  Number of reversible reaction groups.
- `array[Reactions] of string: Rs`  
  Names of reactions.
- `array[Metabolites] of string: Ms`  
  Names of metabolites.
- `array[Metabolites, Reactions] of int: S`  
  Stoichiometry matrix.
- `array[Reversibles, Reactions] of int: Revs`  
  Indicates which reactions belong to reversible pairs.
- `int: iub = 50`  
  Upper bound for integer flux values.

---

## **Decision Variables**

- `array[Reactions] of var 0..iub: Vs`  
  Flux values for each reaction (non-negative integers).
- `array[Reactions] of var bool: Zs :: output`  
  Boolean support vector indicating whether a reaction is active (`true`) or inactive (`false`).

---

## **Constraints**

1. **Non-negativity:**  
   Flux values must be non-negative:

   ```minizinc
   constraint forall(j in Reactions)(Vs[j] >= 0);
   ```

2. **Support Definition:**  
   A reaction is active if and only if its flux is positive:

   ```minizinc
   constraint forall(j in Reactions)((Vs[j] > 0) <-> (Zs[j] == true));
   ```

3. **Steady-State Condition:**  
   No net change in metabolite concentrations:

   ```minizinc
   constraint forall(i in Metabolites)(sum(j in Reactions)(Vs[j] * S[i,j]) = 0);
   ```

4. **Reversibility Constraint:**  
   At most one reaction from each reversible pair can be active:

   ```minizinc
   constraint forall(i in Reversibles)(sum(j in Reactions)(Zs[j] * Revs[i,j]) <= 1);
   ```

5. **Exclude Trivial Solution:**  
   Prevent all-zero solution:
   ```minizinc
   constraint bool_clause(Zs, []);
   ```

---

## **Objective**

Minimise the number of active reactions:

```minizinc
solve minimize sum(Zs);
```

This ensures the smallest possible EFM is found.

---

## **Output**

- Reaction names (`Rs`)
- Flux values (`Vs`)
- Boolean support vector (`Zs`)

---

## **Applications**

- Systems biology and metabolic engineering.
- Identifying minimal pathways for bio-production.
- Analysing robustness and redundancy in metabolic networks.

---

## **References**

- Schuster, S., & Hilgetag, C. (1994). On elementary flux modes in biochemical reaction systems.
- Related concepts: _Stoichiometric analysis_, _Flux balance analysis_.

---
