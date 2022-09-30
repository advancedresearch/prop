# Prop
Propositional logic with types in Rust.

A library in Rust for theorem proving with [Intuitionistic Propositional Logic](https://en.wikipedia.org/wiki/Intuitionistic_logic).
Supports theorem proving in [Classical Propositional Logic](https://en.wikipedia.org/wiki/Propositional_calculus).

- Used in research on [Path Semantics](https://github.com/advancedresearch/path_semantics)
- Brought to you by the [AdvancedResearch Community](https://advancedresearch.github.io/)
- [Join us on Discord!](https://discord.gg/JkrhJJRBR2)

Abbreviations:

- IPL: Intuitionistic/Constructive Propositional Logic
- EL: Existential Logic (Excluded Middle of Non-Existence)
- PL: Classical Propositional Logic
- PSI: Path Semantical Intuitionistic/Constructive Propositional Logic
- PSEL: Path Semantical Existential Logic
- PSL: Path Semantical Classical Propositional Logic
- PSQ: Path Semantical Quantum Propositional Logic

### Motivation

[Path Semantics](https://github.com/advancedresearch/path_semantics)
extends dependent types with normal paths and is also used to extend
Classical Propositional Logic with multiple levels of propositions.
It is also used to explore higher dimensional mathematics.
A popular research subject in Path Semantics is [Avatar Extensions](https://advancedresearch.github.io/avatar-extensions/summary.html).

When researching, in some cases it is useful to figure out whether a proof is
provable in classical logic, but not in constructive logic.
This requires comparing proofs easily.

This library uses a lifting mechanism for making it easier
to produce proofs in classical logic and compare them to
proofs in constructive logic.

### Design

This library contains:

- `Prop`: Propositions that might or might not be decidable (constructive logic)
- `EProp`: Existential propositions (existential logic)
- `DProp`: Decidable propositions (classical logic)
- `LProp`: Like `Prop`, but with path semantics (path semantical constructive logic)
- `ELProp`: Like `EProp`, but with path semantics (path semantical existential logic)
- `DLProp`: Like `DProp`, but with path semantics (path semantical classical logic)
- Automatic lifting of Excluded Middle of Non-Existence to existential propositions
- Automatic lifting of Excluded Middle to decidable propositions
- Double Negation for proofs of `Prop`
- A model of Path Semantical Quality/Aquality in IPL (see "quality" module)
- A model of Path Semantical Qubit in IPL (see "qubit" module)
- A model of Path Semantical Con-Quality in IPL (see "con_qubit" module)
- A model of Seshatic Queenity (see "queenity" module)
- Formalization of the core axiom of Path Semantics
- Exponential Propositions (HOOO) for tautological/paradoxical theorem proving
- Tactics organized in modules by constructs (e.g. `and` or `imply`)

### Examples

```rust
use prop::*;

fn proof<A: Prop, B: Prop>(f: Imply<A, B>, a: A) -> B {
    imply::modus_ponens(f, a)
}
```

Notice that there is no `DProp` used here,
which means that it is a constructive proof.

```rust
use prop::*;

fn proof<A: DProp, B: DProp>(f: Imply<Not<A>, Not<B>>) -> Imply<B, A> {
   imply::rev_modus_tollens(f)
}
```

Here, `DProp` is needed because `rev_modus_tollens` needs Excluded Middle.
This limits the proof to decidable propositions.

### Path Semantics

Path Semantics is an extremely expressive language for mathematical programming.
It uses a single core axiom, which models semantics of symbols.

Basically, mathematical languages contain a hidden symmetry due to use of symbols.
Counter-intuitively, symbols are not "inherently" in logic.

One way to put it, is that the symbols "themselves" encode laws of mathematics.
The hidden symmetry can be exploited to prove semantics and sometimes
improve performance of automated theorem provers.

For more information, see the [Path Semantics Project](https://github.com/advancedresearch/path_semantics).
