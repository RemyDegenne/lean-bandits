import Manual.Pages.BasicProbability
import Manual.Pages.DefiningAlgorithm
import Manual.Pages.Installation
import Manual.Pages.Martingales
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LeanMachineLearning"

#doc (Manual) "Lean Machine Learning" =>
%%%
authors := ["Rémy Degenne, Paulo Rauber"]
shortTitle := "Lean Machine Learning"
%%%

These tutorial pages will guide you through using the [Lean Machine Learning](https://leanmachinelearning.github.io) library.

{include 0 Manual.Pages.Installation}

{include 0 Manual.Pages.BasicProbability}

{include 0 Manual.Pages.Martingales}

{include 0 Manual.Pages.DefiningAlgorithm}
