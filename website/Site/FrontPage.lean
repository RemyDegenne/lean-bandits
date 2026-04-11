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

Lean Machine Learning is building a comprehensive foundation for formalized machine learning theory. The library provides high-quality formalizations, essential theorems, and a trusted framework for machine learning research.
You proved that your new algorithm converges at the optimal rate and your LLM formalized the proof.
Lean checked the proof. But who checked the Lean definition of optimal rate? We did. Since your LLM is using a Lean Machine Learning definition, you can trust it proved the right thing.

:::::htmlDiv (class := "build-cards")

::::htmlDiv (class := "build-card")

*Formalized Definitions*

Rigorous definitions of machine learning concepts: algorithms, performance measures, etc. A common vocabulary for researchers and AI systems to build on.

::::

::::htmlDiv (class := "build-card")

*Proven Theorems*

Essential theorems in machine learning theory. Convergence guarantees, regret bounds, and foundational results in probability theory and optimization.

::::

::::htmlDiv (class := "build-card")

*AI-Ready*

Lean Machine Learning provides a common vocabulary of formal definitions that can be used by AI systems to generate theorems about objects we care about.

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

:::::::html div (class := "sponsors") (id := "sponsors")

*Sponsors and Partners*

We are grateful for the support of the following organizations.

::::::htmlDiv (class := "sponsor-cards")

:::::htmlDiv (class := "sponsor-card")
::::html a (href := "https://www.inria.fr/")
:::html img (src := "/static/Inria_logo_RGB.png") (alt := "Inria")
:::
::::
Inria FORMAL exploratory action
:::::

::::::

If you are interested in supporting Lean Machine Learning financially please reach out to Rémy Degenne at `remy [dot] degenne [at] inria [dot] fr` or on the Lean Zulip (preferred).

:::::::


::::::html div (class := "showcase") (id := "maintainers")

*Maintainers*

:::::htmlDiv (class := "showcase-cards")

::::htmlDiv (class := "showcase-card reference")

[*Rémy Degenne*](https://remydegenne.github.io/)

Inria centre at the University of Lille

:::html img (src := "https://remydegenne.github.io/images/avatar2.jpg") (alt := "Rémy Degenne") (style := "border-radius: 50%; width: 150px; height: 150px; object-fit: cover;")
:::

::::

::::htmlDiv (class := "showcase-card reference")

[*Paulo Rauber*](https://www.paulorauber.com/)

Queen Mary University of London

:::html img (src := "https://www.paulorauber.com/files/images/profile.jpg") (alt := "Paulo Rauber") (style := "border-radius: 50%; width: 150px; height: 150px; object-fit: cover;")
:::

::::

:::::

::::::
