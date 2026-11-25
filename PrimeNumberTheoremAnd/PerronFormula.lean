module

public import Architect
public import TauCeti.Analysis.MellinInversion


@[expose] public section

blueprint_comment /--
In this section we record the Perron formula, which plays a key role in our proof of Mellin
inversion. Both cases, Lemma \ref{formulaLtOne} and Lemma \ref{formulaGtOne}, are proved in
Tau Ceti by computing the Mellin transform of the cutoff $(1-x)_+$ and applying Mellin inversion.
-/

attribute [blueprint "formulaLtOne"
  (title := "formulaLtOne")
  (statement := /--
  For $\sigma>0$ and $x>0$, we have
  $$
  \frac1{2\pi i}
  \int_{(\sigma)}\frac{x^{-s}}{s(s+1)}ds = \max(1-x,0).
  $$
  Replacing $x$ by $1/x$: for $x>0$, $\sigma>0$, and $x<1$, we have
  $\frac1{2\pi i}\int_{(\sigma)}\frac{x^s}{s(s+1)}ds =0$.
  -/)
  (proof := /--
  The Mellin transform of $u\mapsto\max(1-u,0)$ is $\frac{1}{s(s+1)}$ for $\Re s>0$, and this
  transform is integrable on the line $\Re s=\sigma$. Mellin inversion recovers the continuous
  function $\max(1-x,0)$.
  -/)
  (latexEnv := "lemma")]
  TauCeti.mellinInv_inv_mul_add_one

attribute [blueprint "formulaGtOne"
  (title := "formulaGtOne")
  (statement := /--
  For $\sigma>0$ and $x>0$, we have
  $$
  \frac1{2\pi i}
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds = \max\left(1-\frac1x,0\right) = \begin{cases}
  1-\frac1x & \text{ if }x>1\\
  0 & \text{ if } x\le 1
  \end{cases}.
  $$
  -/)
  (proof := /-- Apply Lemma \ref{formulaLtOne} at $1/x$. -/)
  (proofUses := ["formulaLtOne"])
  (latexEnv := "lemma")]
  TauCeti.integral_cpow_div_mul_add_one

blueprint_comment /--
The two together give the Perron formula.
-/
