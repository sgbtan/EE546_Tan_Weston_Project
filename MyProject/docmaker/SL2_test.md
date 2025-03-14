

<center><h1>EE 546 : Automated Reasoning</h1></center>
<center><h2>HIERARCHIES</h2></center>

<center>
Department of Electrical and Computer Engineering<br />
Unviersity of Washington<br />
Prof. Eric Klavins<br />
Winter 2025<br />
Solutions: H2Solve.lean
</center>
<br />


```hs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Complex.Basic

import EE546_W25.Lib.ComplexSimps  -- My own libraries
import EE546_W25.Lib.UHP

open Complex
```
 # Documentation Maker

This file can be converted into viewable Markdown by using a new script:

```bash
cd EE546_W25/docmaker/dm.py
python dm.py ../EE546_W25/Lectures/SL2.lean > SL2.md
```

You can then view the file either directly in VSCode using Cmd-V or in your favorite Markdown viewer. I like [this one](https://chromewebstore.google.com/detail/markdown-viewer/ckkdlimhmcjmikdlpkmbgfkaikojcbjk?hl=en&pli=1).

Note that you can use Latex and it will render in the Markdown Viewer:

$$
\sum_{n=0}^\infty r^n = \frac{1}{1-r}.
$$

More sophisticated converters can be used as well. Lean uses `DocGen`, but it seems to want to build your entire project including all the dependencies. The various books like MIL and TIL seem to use Sphinx, which seemed like overkill for the present purposes.

For your final project, you will need to use this script (or figure out how to use one of the other ones) to generate a nicely written up report.


 # Code structure

  * SL2.lean : This file
    * Lots of documentation!
  * Lib/ComplexSimps.lean : A lot of obvious things about complex numbers
  * Lib/UHP.lean : Definitions for the upper half plane of the complex numbers


