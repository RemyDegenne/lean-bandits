import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation and Setup" =>
%%%
htmlSplit := .never
%%%

This tutorial guides you through installing Lean and setting up the Lean Machine Learning library.

# Installing Lean

Before using the Lean Machine Learning library, you need to install Lean 4 and its build tool Lake.

Follow the official installation instructions at [https://lean-lang.org/lean4/doc/quickstart.html](https://lean-lang.org/lean4/doc/quickstart.html).

The installation process will set up:
- Lean 4 compiler
- Lake (Lean's build tool and package manager)
- VS Code extension (recommended IDE for Lean)

# Cloning and Building the Library

Once Lean is installed, you can clone and build the Lean Machine Learning library:

```
git clone https://github.com/remydegenne/lean-bandits.git
cd lean-bandits
lake build
```

The `lake build` command will:
1. Download all dependencies (including mathlib)
2. Compile the library
3. Build the project files

This may take some time on the first run as it downloads and compiles dependencies.

# Creating Your First Algorithm

To start working with the library, create a new file in the project. For example, create `Draft.lean` in the root directory:

```
import LeanMachineLearning.Bandit.Bandit
import LeanMachineLearning.SequentialLearning.Algorithm

open LeanMachineLearning

-- Define a simple dummy algorithm that always plays the first action
def dummyAlgorithm (numActions : ℕ) : Algorithm (Fin numActions) ℝ where
  p0 := Measure.dirac 0
  policy _ := fun _ => Measure.dirac 0

-- You can now use this algorithm to prove properties!
example (n : ℕ) : dummyAlgorithm 5 = dummyAlgorithm 5 := rfl
```

Open this file in VS Code with the Lean extension, and you'll see:
- Syntax highlighting
- Error messages if any
- Tactic state in the Infoview panel
- Hover information for definitions

You're now ready to explore the library and formalize machine learning algorithms!
