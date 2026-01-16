# Bandit algorithms in Lean

This repository contains a Lean formalization of regret bounds for several stochastic bandit algorithms.

Authors: Rémy Degenne, Paulo Rauber.

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
