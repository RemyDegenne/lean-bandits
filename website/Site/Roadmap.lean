/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import VersoBlog
import Site.Meta

open Verso Genre
open Blog hiding lean
open Site

#doc (Page) "Roadmap" =>

::::::html div (class := "roadmap-page")

:::::html div (class := "roadmap-header")

*Roadmap*

The development plan for Lean Machine Learning

:::::

:::::html div (class := "roadmap-section")

*Vision*

Lean Machine Learning provides a comprehensive library of formalized definitions and theorems in machine learning theory.
It is a trusted foundation for formalization of machine learning research.
As algorithms are central to machine learning, it provides tools to define and analyze stochastic algorithms in Lean, and to connect formal specifications with executable implementations.


::::html div (class := "roadmap-subsection")

*Key Features*

- High quality, human-checked, general definitions of machine learning concepts
- Tools to prove theoretical properties of machine learning algorithms
- Executable implementations of machine learning algorithms, connected to formal specifications
- Extensive documentation and tutorials to guide users through the library and its applications

::::

::::html div (class := "roadmap-subsection")

*Impact and beneficiaries*

- Researchers can formalize their new results, since the required concepts are available in the library
- AI agents can prove new results or check papers without the risk of using an incorrectly formalized definition
- Students and researchers can access and search a large and trusted knowledge base about machine learning

::::

:::::

:::::html div (class := "roadmap-section")

*Roadmap*

We are currently in the early stages of development, with the core framework for defining and analyzing stochastic algorithms in place, as well as initial results about bandit algorithms.
Since the project is open and collaborative, the direction we will take for the extension of the library of theoretical results will be guided by the needs of the contributors, but we aim to cover a broad range of topics in machine learning theory and algorithms.


::::html div (class := "roadmap-subsection")

*Year 1*

- Library - theoretical foundations: concentration inequalities, decision theory, information theory related to testing
- Library - online learning: bandits, prediction with expert advice, online convex optimization
- Executable algorithms: define a probabilistic monad with do-notation, test it on the existing bandit algorithms, and connect it to the formal specifications of the algorithms
- Documentation: comprehensive documentation of the existing algorithm framework and bandit results, and tutorials to get started with the library
- AI readiness: demonstration of an AI formalization of a bandit or online learning paper using the library

::::


::::html div (class := "roadmap-subsection")

*Year 2*

- Library - statistical learning theory: PAC learning, Rademacher complexity, generalization bounds (PAC-Bayes)
- Library - reinforcement learning: Markov decision processes, value iteration, policy gradient methods
- Executable algorithms: have executable implementations of some online learning algorithms, on which we can run experiments and compare with the theoretical predictions
- Documentation: comprehensive documentation of the new theoretical results and algorithms, with tutorials
- Subject coverage and AI readiness: a folder with formalizations or reports on the feasibility of formalizing a wide array of papers from COLT/NeurIPS/ICML/ICLR using the library

::::


::::html div (class := "roadmap-subsection")

*Year 3*

- Library - deep learning: neural networks, backpropagation, generalization in deep learning
- Library - advanced reinforcement learning: deep Q-learning, actor-critic methods, multi-agent RL
- Executable algorithms: have executable implementations of deep learning and advanced RL algorithms, linked with theory
- Subject coverage and AI readiness: several new papers formalized using the library, and a demonstration of an AI system generating a new theorem about a machine learning algorithm using the library

::::

:::::

::::::
