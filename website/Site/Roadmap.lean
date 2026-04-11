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


::::html div (class := "roadmap-subsection")

*Year 1*

- Theoretical foundations: concentration inequalities, decision theory
- Executable algorithms: define a probabilistic monad with do-notation, test it on the existing bandit algorithms, and connect it to the formal specifications of the algorithms
- todo

::::


::::html div (class := "roadmap-subsection")

*Year 2*

- todo
- todo

::::


::::html div (class := "roadmap-subsection")

*Year 3*

- todo
- todo

::::

:::::

::::::
