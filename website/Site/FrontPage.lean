/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
import VersoBlog
import Site.Meta

open Verso Genre
open Blog hiding lean
open Site

#doc (Page) "Lean Machine Learning" =>

::::::htmlDiv (class := "hero")

:::::htmlDiv (class := "hero-text")

Lean Machine Learning

The Lean library for machine learning research

Lean Machine Learning is a carefully curated library of formalized definitions and theorems in machine learning theory, verified in [Lean](https://lean-lang.org). It provides a trusted foundation for researchers to explore and formalize machine learning algorithms with mathematical rigor.

::::html a (class := "hero-btn primary") (href := "https://github.com/remydegenne/lean-bandits")
:::html img (src := "/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
Get Started
::::

::::html a (class := "hero-btn secondary") (href := "tutorial")
:::html img (src := "/static/book.svg") (alt := "") (width := "20") (height := "20")
:::
Tutorials
::::

::::html a (class := "hero-btn secondary") (href := "docs")
:::html img (src := "/static/book.svg") (alt := "") (width := "20") (height := "20")
:::
Documentation
::::

:::::

::::::

:::::html div (class := "pillars") (id := "about")

::::htmlDiv (class := "pillar")

*Rigorous*

Every definition and theorem is formally verified in Lean. Machine learning algorithms are precisely specified, and regret bounds are rigorously proven. From stochastic bandits to more complex algorithms, every claim is mathematically checked.

::::

::::htmlDiv (class := "pillar")

*Research-Ready*

Built for machine learning researchers. The library provides a framework for formalizing new algorithms and proving theoretical guarantees. Current results include regret bounds for Explore-Then-Commit and UCB algorithms, with infrastructure for expanding to other bandit variants and beyond.

::::

::::htmlDiv (class := "pillar")

*Community-Driven*

Open source and collaborative. Built with mathlib and modern Lean 4. We welcome contributions of new algorithms, theorems, and improvements. Join discussions on Zulip or contribute on GitHub.

::::

:::::

::::::html div (class := "builds") (id := "goals")

*Goals & Features*

Lean Machine Learning is building a comprehensive foundation for formalized machine learning theory. The library provides high-quality formalizations, essential theorems, and a trusted framework for research in machine learning algorithms.

:::::htmlDiv (class := "build-cards")

::::htmlDiv (class := "build-card")

*Formalized Definitions*

Rigorous definitions of machine learning concepts: algorithms, environments, rewards, and regret

::::

::::htmlDiv (class := "build-card")

*Proven Theorems*

Essential theorems in machine learning theory with complete formal proofs

::::

::::htmlDiv (class := "build-card")

*AI-Ready*

Lean Machine Learning provides a common vocabulary of formal definitions that can be used by AI systems to generate theorems about objects we actually care about

::::

::::htmlDiv (class := "build-card")

*Research Framework*

Tools for formalizing new algorithms and proving theoretical guarantees

::::

::::htmlDiv (class := "build-card")

*Documentation*

Comprehensive documentation with examples and tutorials for researchers

::::

::::htmlDiv (class := "build-card")

*Mathlib Integration*

Contributions to probability theory and measure theory for machine learning

::::

:::::

::::::

::::::html div (class := "showcase") (id := "roadmap")

*Roadmap*

:::::htmlDiv (class := "showcase-cards")

::::htmlDiv (class := "showcase-card reference")

[*Algorithm Framework*](https://github.com/remydegenne/lean-bandits/tree/main/LeanMachineLearning/SequentialLearning)

A general framework for proving properties of stochastic machine learning algorithms in Lean

::::

::::htmlDiv (class := "showcase-card course")

*Mathematical Foundations*

Concentration inequalities, martingale theory, sub-Gaussian variables, and other foundational results

::::

::::htmlDiv (class := "showcase-card textbook")

*Bandit Algorithms* ✓

Stochastic multi-armed bandits with regret bounds (ETC, Round-Robin, UCB) — partially complete

::::

::::htmlDiv (class := "showcase-card reference")

*Statistical Learning Theory*

PAC learning, VC dimension, Rademacher complexity, and learning bounds

::::

::::htmlDiv (class := "showcase-card textbook")

*Optimization*

Convex optimization, gradient descent, stochastic optimization algorithms

::::

:::::

::::::

::::::html div (id := "get-started") (class := "get-started")

*Get Started*

Lean Machine Learning provides a trusted foundation for formalized machine learning research. Whether you're exploring bandit algorithms, contributing new proofs, or building on the existing framework, we welcome your participation.

:::::htmlDiv (class := "cta-buttons")

::::html a (class := "cta-btn primary") (href := "https://github.com/remydegenne/lean-bandits")
:::html img (src := "/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
View on GitHub
::::

::::html a (class := "cta-btn secondary") (href := "tutorial")
:::html img (src := "/static/book.svg") (alt := "") (width := "20") (height := "20")
:::
Tutorials
::::

::::html a (class := "cta-btn secondary") (href := "docs")
:::html img (src := "/static/book.svg") (alt := "") (width := "20") (height := "20")
:::
Documentation
::::

::::html a (class := "cta-btn secondary") (href := "https://leanprover.zulipchat.com/")
:::html img (src := "/static/zulip.svg") (alt := "") (width := "20") (height := "20")
:::
Join Zulip
::::

:::::

::::::
