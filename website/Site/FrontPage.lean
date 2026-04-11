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

*Rigorous Formalization*

A library of high quality, human-checked, general definitions of machine learning concepts and the main theorems about them. We develop a carefully curated common vocabulary for researchers and AI systems to build on.

::::

::::htmlDiv (class := "pillar")

*Algorithms*

Built for machine learning researchers. The library provides a framework for formalizing new algorithms and proving theoretical guarantees. It also provides executable implementations of machine learning algorithms, connected to formal specifications.

::::

::::htmlDiv (class := "pillar")

*Community-Driven*

Open source and collaborative. The library is built on top of Mathlib and we contribute to it.
We welcome contributions of new algorithms, theorems, and improvements. Join discussions on Zulip or contribute on GitHub.

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

A common vocabulary of formal definitions that can be used by AI systems to generate theorems about objects we care about and avoid misformalization errors.

::::

::::htmlDiv (class := "build-card")

*Algorithmic Tools*

A framework for defining and analyzing stochastic algorithms in Lean, and to connect formal specifications with executable implementations.

::::

::::htmlDiv (class := "build-card")

*Documentation*

Comprehensive documentation with examples and tutorials to guide users through the library and its applications.

::::

::::htmlDiv (class := "build-card")

*Collaborative*

Open source, collaborative, and integrated in the Lean ecosystem.
We welcome contributions from the community.
We build on top of Mathlib and contribute to it in return.

::::

:::::

::::::

::::::html div (id := "get-started") (class := "get-started")

*Get Started*

Learn more about Lean Machine Learning with the tutorials and documentation, or head over to GitHub to explore the code and contribute to the project.

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

::::html a (class := "cta-btn secondary") (href := "roadmap")
:::html img (src := "/static/book.svg") (alt := "") (width := "20") (height := "20")
:::
Roadmap
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
