
<div align="center">

# Lean Machine Learning

## The Lean library for machine learning research.

</div>


Website: [https://remydegenne.github.io/lean-bandits/](https://remydegenne.github.io/lean-bandits/)

## Goals

- A library of high-quality formalization of machine learning definitions.
- Essential theorems and proofs in machine learning theory.
- A framework for working on machine learning algorithms in Lean.
- An extensive documentation, with examples and tutorials.
- A trusted basis for formalization of machine learning research.

## Contributing

Please see our [contribution guide](CONTRIBUTING.md) and [code of conduct](CODE_OF_CONDUCT.md).

For discussions, you can reach out to us on the [Lean prover Zulip chat](https://leanprover.zulipchat.com/).

## Current state of the library

As a first proof of concept, the repository contains a formalization of regret bounds for several stochastic bandit algorithms.

Main results:
- Framework for working on bandit algorithms in Lean.
- Regret bound for the Explore-Then-Commit algorithm.
- Regret bound for the UCB algorithm.

Contents:
- Definitions of an iterative, stochastic algorithm and a stochastic environment
- Proofs of the existence of probability spaces on which those algorithm-environment interactions are defined, and uniqueness of the resulting laws
- Notations and tools to analyze bandits: number of times an arm was pulled, time of the nth pull, regret, gap. Relations between those.
- Concentration inequalities
- Definitions of ETC and UCB
- Proofs of regret bounds for those two algorithms.
