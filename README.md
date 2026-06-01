# CertIMP: A Lean-Verified Toy Implementation of IMP

Welcome! This repository contains a [Lean 4](https://lean-lang.org/) development of IMP, a simple imperative language commonly used in introductory programming language theory classes. It adapts and expands upon the first five chapters of [Software Foundations Vol. 2: Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html).

### Why?

Our main contribution beyond the textbook presentation is a *verified compiler* from IMP to the instruction set of a simple stack-based machine, by a proof of semantics preservation. This composes neatly with correctness proofs for other code transformations, e.g., constant folding. We therefore provide a very simple *optimizing* compiler, along with its machine-checked proof of correctness.

This work was done as part of the **Program Verification** master's lab at the [Faculty of Mathematics & Computer Science, Univ. of Bucharest](https://fmi.unibuc.ro/). All proofs in this Lean project have been written collaboratively by students over the course of a semester.

### Navigating this project

We embed IMP syntax to Lean via [metaprogramming](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Syntax/Parser.lean), drawing inspiration from the Rocq notations in the Software Foundations book.

On this basis, our project follows with the basic development of IMP:
-  its [big-step](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Eval/Eval.lean) operational semantics;
-  a [Hoare calculus](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Hoare/Logic.lean), along with its [soundness](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Hoare/Soundness.lean) & [completeness](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Hoare/Completeness.lean) theorems;
- a [custom tactic](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Hoare/VCG/Tactic.lean) for automatically proving Hoare triple goals by verification condition generation;
- we also touch upon [weakest precondition calculus](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Hoare/TotalCorrectness.lean) using total correctness triples.

As previously mentioned, this project also contains:
- the definition of an [idealized stack machine](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/StackMachine/MachineState.lean); 
- its corresponding [instruction set](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/StackMachine/ISA.lean), along with its [semantics](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/StackMachine/Semantics.lean);
- a [semantics-preservation proof](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/StackMachine/SemanticsPreservation.lean#L423) for compiling IMP to this ISA;
- a simple [constant folding](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Transformation/ConstantFolding.lean) optimization pass which we similarly [prove correct](https://github.com/alexoltean61/certimp-lean/blob/master/CertIMP/Transformation/Exercises.lean).

### Building
Before you start, make sure you have [Lean installed](https://lean-lang.org/install/) in your environment.

1. Clone this repository.
2. From your cloned directory, run `lake exe cache get`. This will fetch a compressed version of the `Mathlib` library, which would normally be huge.
3. Run `lake build`.

### Acknowledgments

Our semantics preservation proof was initially modelled following [the one developed](https://perry.alexander.name/eecs755//blog/2025/11/16/Imp-Compiler.html) by [@palexand](https://github.com/palexand) and his students for the EECS 755 course, which only covers arithmetic and boolean expressions. For the semantics of the ISA, we took inspiration from [@NethermindEth](https://github.com/NethermindEth)'s formal model of the [Ethereum Virtual Machine in Lean](https://github.com/NethermindEth/EVMYulLean).