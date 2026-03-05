# Black Hole Patience — MiniZinc Model Overview

This MiniZinc model represents the solitaire card game **Black Hole Patience**, following the formulation from the research paper:

**"Search in the Patience Game 'Black Hole'"**  
_Ian P. Gent, Chris Jefferson, Tom Kelsey, Inês Lynce, Ian Miguel, Peter Nightingale, Barbara M. Smith, and S. Armagan Tarim._

The model included here is the *basic version* of the problem as presented in that paper, and it follows the structure used in the Gecode distribution.

---

## 🎯 Problem Description

Black Hole Patience is a one-player card-placement puzzle.  
The objective is to build a sequence of all 52 cards such that:

1. The first card is the **Ace of Spades** (represented by card number `1`).
2. Each consecutive card is a *legal neighbour* of the previous one—typically meaning it differs in rank by one (modulo rank cycles), though this model uses a pre‑computed **neighbours table** to define all allowed transitions.
3. Cards are arranged according to a given pile layout. Each pile contains cards stacked in order, so a card must be played *before* the one beneath it.

The challenge is to find any complete sequence of all cards that adheres to these rules.

---

## 🧩 Model Components

### **Parameters**

- **`layout[1..17, 1..3]`**  
  Represents the 17 piles of the game, each containing exactly 3 cards.  
  The integers correspond to card identifiers from 1 to 52.

- **`neighbours[1..416, 1..2]`**  
  A table listing all valid pairs of sequential cards.  
  If `(a, b)` appears in the table, then card `b` may follow card `a`.

These data sets together define the structure of the puzzle instance.

---

## 🧮 Decision Variables

- **`x[1..52]`**  
  The sequence of cards in the order they will be played.  
  For example, `x[1]` is the first card played.

- **`y[1..52]`**  
  The inverse of `x`: `y[c]` gives the position (1–52) at which card `c` is played.

---

## 🔒 Constraints

The model ensures several rules:

### 1. **Starting Condition**
```mzn
x[1] == 1;
```

Card 1 (Ace of Spades) must be the first move.

### 2. **Neighbour Rule**

For every pair of consecutive positions, the model forces compatibility using the neighbours table:

```mzn
table([x[i], x[i+1]], neighbours)
```

This means card `x[i+1]` must be a legal continuation of card `x[i]`.

### 3. **Position Inversion**

```mzn
inverse(x, y)
```

Links card positions (`x`) to card identities (`y`).

### 4. **Pile Ordering**

Cards physically under others in piles cannot be played earlier.  
For each pile and each adjacent pair in that pile:

```mzn
y[layout[i, j]] < y[layout[i, j+1]]
```

This guarantees correct stack order.

***

## 🛠️ Solving

The model uses a standard integer search over `x` to find **any valid complete sequence** satisfying all constraints. There is **no objective function**—this is a pure satisfaction problem.

***

## 📚 References

This model is based on the formal description from:

Gent et al., *Search in the Patience Game “Black Hole”*, presented in work on applying constraint programming to solitaire variants.
