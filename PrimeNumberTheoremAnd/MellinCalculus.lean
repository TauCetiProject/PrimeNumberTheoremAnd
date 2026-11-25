/-
Real/complex derivative coercion arguments below are based on the former Auxiliary module.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Architect
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.MellinTransform.Convolution
public import TauCeti.Analysis.MellinTransform.Decay
public import TauCeti.Analysis.MellinTransform.SmoothCutoff


@[expose] public section

blueprint_comment /--
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler),
prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

Def: (Already in Mathlib)
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of
$f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$

[Note: My preferred way to think about this is that we are integrating over the multiplicative
group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and
integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds
of calculations carried out below. But may be more difficult to formalize as things now stand. So
we might have clunkier calculations, which ``magically'' turn out just right - of course they're
explained by the aforementioned structure...]

-/


blueprint_comment /--
We will use partial integration on $(0,\infty)$ in the following form.
-/
attribute [blueprint "PartialIntegration"
  (title := "PartialIntegration")
  (statement := /--
  Let $u, v$ be differentiable functions on $(a,\infty)$ with values in $\mathbb{C}$ so that
  $uv'$ and $u'v$ are both integrable on $(a,\infty)$, and $u v(x)\to a'$ as $x\to a^+$ and
  $u v(x)\to b'$ as $x\to\infty$. Then
  $$
  \int_a^\infty u(x)v'(x)\, dx = b'-a'-\int_a^\infty u'(x)v(x)\,dx.
  $$
  -/)
  (proof := /-- Integrate $(uv)'=u'v+uv'$ over $(a,\infty)$. -/)
  (latexEnv := "lemma")]
  MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul

blueprint_comment /--
Finally, we need Mellin Convolutions and properties thereof.
-/
attribute [blueprint "MellinConvolution"
  (title := "MellinConvolution")
  (statement := /--
  Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the
  Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$
  to $\mathbb{C}$ defined by
  $$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
  -/)
  (latexEnv := "definition")]
  TauCeti.mellinConv

blueprint_comment /--
Let us start with a simple property of the Mellin convolution.
-/
attribute [blueprint "MellinConvolutionSymmetric"
  (title := "MellinConvolutionSymmetric")
  (statement := /--
  Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. For $x>0$,
  $$
    (f\ast g)(x)=(g\ast f)(x)
    .
  $$
  -/)
  (proof := /--
  By Definition \ref{MellinConvolution},
  $$
    (f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}
  $$
  in which we change variables to $z=x/y$:
  $$
    (f\ast g)(x) = \int_0^\infty f(x/z)g(z)\frac{dz}{z}
    =(g\ast f)(x)
    .
  $$
  -/)
  (proofUses := ["MellinConvolution"])
  (latexEnv := "lemma")]
  TauCeti.mellinConv_comm_of_pos

blueprint_comment /--
The $\nu$ function has Mellin transform $\mathcal{M}(\nu)(s)$ which is entire and decays (at
least) like $1/|s|$.

[Of course it decays faster than any power of $|s|$, and Tau Ceti proves decay of every order
for which $\nu$ is differentiable.]
-/

attribute [blueprint "MellinOfPsi"
  (title := "MellinOfPsi")
  (statement := /--
  Let $f$ be of class $C^N$ on $(0,\infty)$, with $\operatorname{supp}f\cap(0,\infty)$ compact,
  and let $K\subset\mathbb{R}$ be compact. Then there is a constant $C>0$ such that
  $$(1+|\Im s|)^N\,|\mathcal{M}(f)(s)|\le C$$
  for every $s$ with $\Re s\in K$. In particular, for a bumpfunction $\nu$ supported in
  $[1/2,2]$, $\mathcal{M}(\nu)(s)=O(1/|s|)$ uniformly on vertical strips.
  -/)
  (proof := /--
  Integrate by parts $N$ times:
  $$
  \int_0^\infty f(x)x^s\frac{dx}{x} =
  \frac{(-1)^N}{s(s+1)\cdots(s+N-1)}\int_0^\infty f^{(N)}(x)x^{s+N-1}dx,
  $$
  and bound the last integral uniformly for $\Re s\in K$ using the compact support of $f$. This
  handles $|\Im s|\ge 1$; on the compact rest of the strip $\mathcal{M}(f)$ is continuous.
  -/)
  (proofUses := ["PartialIntegration"])
  (latexEnv := "lemma")]
  TauCeti.exists_one_add_abs_im_pow_mul_norm_mellin_le

blueprint_comment /--
We can make a delta spike out of this bumpfunction, as follows.
-/

attribute [blueprint "DeltaSpike"
  (title := "DeltaSpike")
  (statement := /--
  Let $\nu$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the
  delta spike $\nu_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{R}$ defined by
  $$\nu_\epsilon(x) = \frac{1}{\epsilon}\nu\left(x^{\frac{1}{\epsilon}}\right),$$
  and $\nu_\epsilon(x)=0$ for $x\le 0$.
  -/)
  (latexEnv := "definition")]
  TauCeti.deltaSpike

blueprint_comment /--
This spike still has mass one:
-/

attribute [blueprint "DeltaSpikeMass"
  (title := "DeltaSpikeMass")
  (statement := /--
  For any $\epsilon>0$, we have
  $$\int_0^\infty \nu_\epsilon(x)\frac{dx}{x} = \int_0^\infty \nu(x)\frac{dx}{x},$$
  which is $1$ when $\nu$ has mass one.
  -/)
  (proof := /--
  Substitute $y=x^{1/\epsilon}$, and use the fact that $dx/x$ is Haar measure.
  -/)
  (proofUses := ["DeltaSpike"])
  (latexEnv := "lemma")]
  TauCeti.integral_deltaSpike_div

blueprint_comment /--
The Mellin transform of the delta spike is easy to compute.
-/
attribute [blueprint "MellinOfDeltaSpike"
  (title := "MellinOfDeltaSpike")
  (statement := /--
  For any $\epsilon>0$, the Mellin transform of $\nu_\epsilon$ is
  $$\mathcal{M}(\nu_\epsilon)(s) = \mathcal{M}(\nu)\left(\epsilon s\right).$$
  In particular, $\mathcal{M}(\nu_\epsilon)(1) = \mathcal{M}(\nu)(\epsilon)$.
  -/)
  (proof := /-- Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation. -/)
  (proofUses := ["DeltaSpike"])
  (latexEnv := "theorem")]
  TauCeti.mellin_deltaSpike

blueprint_comment /--
In particular, for $s=1$, we have that the Mellin transform of $\nu_\epsilon$ is $1+O(\epsilon)$.
-/

attribute [blueprint "MellinOfDeltaSpikeAt1_asymp"
  (title := "MellinOfDeltaSpikeAt1-asymp")
  (statement := /--
  Let $\nu\ge 0$ be supported in $[1/2,2]$ with $\int_0^\infty\nu(x)\frac{dx}{x}=1$. For
  $0\le\epsilon\le 1$,
  $$|\mathcal{M}(\nu)(\epsilon)-1|\le 2\log 2\cdot\epsilon.$$
  By Theorem \ref{MellinOfDeltaSpike}, this says $\mathcal{M}(\nu_\epsilon)(1) = 1+O(\epsilon)$.
  -/)
  (proof := /--
  Since $\nu$ has mass one,
  $$
    \mathcal M(\nu)(\epsilon)-1=\int_{1/2}^2\nu(x)(x^{\epsilon}-1)\frac{dx}x
    ,
  $$
  and $|x^\epsilon-1|\le 2^\epsilon-1\le 2\log 2\cdot\epsilon$ for $x\in[1/2,2]$ and
  $0\le\epsilon\le1$.
  -/)
  (proofUses := ["MellinOfDeltaSpike", "SmoothExistence"])
  (latexEnv := "lemma")]
  TauCeti.norm_mellin_sub_one_le

blueprint_comment /--
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform $1/s$ for $\Re s>0$ (Mathlib).
-/
blueprint_comment /--
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$.
-/
attribute [blueprint "Smooth1"
  (title := "Smooth1")
  (statement := /--
  Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from
  $\mathbb{R}_{>0}$ to $\mathbb{R}$ by
  $$\widetilde{1_{\epsilon}}(x) = \int_x^\infty \nu_\epsilon(z)\frac{dz}{z},$$
  and $\widetilde{1_{\epsilon}}(x)=0$ for $x\le 0$. For $x>0$ this is the Mellin convolution
  $1_{(0,1]}\ast\nu_\epsilon$.
  -/)
  (proofUses := ["MellinConvolution", "DeltaSpike"])
  (latexEnv := "definition")]
  TauCeti.smoothCutoff

blueprint_comment /--
In particular, we have the following two properties.
-/

attribute [blueprint "Smooth1Properties_below"
  (title := "Smooth1Properties-below")
  (statement := /--
  Let $\nu$ be supported in $[1/2,2]$ with mass one, and $\epsilon>0$. If
  $0 < x \leq 2^{-\epsilon}$, then
  $$\widetilde{1_{\epsilon}}(x) = 1.$$
  Since $1-\epsilon\log 2<2^{-\epsilon}$, this holds in particular for
  $0<x\le 1-\epsilon\log 2$.
  -/)
  (proof := /--
  The support of $\nu_\epsilon$ is contained in $[2^{-\epsilon},2^\epsilon]$. If
  $x\le 2^{-\epsilon}$, then
  $$
  \widetilde{1_\epsilon}(x)=\int_x^\infty \nu_\epsilon(z)\frac{dz}{z}
  =\int_0^\infty \nu_\epsilon(z)\frac{dz}{z},
  $$
  which is equal to one by Lemma \ref{DeltaSpikeMass}.
  -/)
  (proofUses := ["Smooth1", "DeltaSpikeMass"])
  (latexEnv := "lemma")]
  TauCeti.smoothCutoff_eq_one

attribute [blueprint "Smooth1Properties_above"
  (title := "Smooth1Properties-above")
  (statement := /--
  Let $\nu$ be supported in $[1/2,2]$, and $\epsilon>0$. If $x\geq 2^{\epsilon}$, then
  $$\widetilde{1_{\epsilon}}(x) = 0.$$
  Since $2^\epsilon<1+2\epsilon\log 2$ for $0<\epsilon<1$, this holds in particular for
  $x\ge 1+2\epsilon\log 2$.
  -/)
  (proof := /--
  If $x \geq 2^\epsilon$, then the support of $\nu_\epsilon$ meets the region of integration
  $(x,\infty)$ in a null set, and hence the integral is zero.
  -/)
  (proofUses := ["Smooth1"])
  (latexEnv := "lemma")]
  TauCeti.smoothCutoff_eq_zero

attribute [blueprint "Smooth1Nonneg"
  (title := "Smooth1Nonneg")
  (statement := /--
  If $\nu$ is nonnegative on $(0,\infty)$ and $\epsilon\ge 0$, then $\widetilde{1_{\epsilon}}(x)$
  is nonnegative.
  -/)
  (proof := /--
  By Definitions \ref{Smooth1} and \ref{DeltaSpike},
  $\widetilde{1_\epsilon}(x)=\int_x^\infty \nu_\epsilon(z)\frac{dz}{z}$, and the integrand is
  nonnegative.
  -/)
  (proofUses := ["Smooth1"])
  (latexEnv := "lemma")]
  TauCeti.smoothCutoff_nonneg

attribute [blueprint "Smooth1LeOne"
  (title := "Smooth1LeOne")
  (statement := /--
  If $\nu$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$ for all $x$
  and $\epsilon>0$.
  -/)
  (proof := /--
  Since the integrand is nonnegative,
  $$
    \widetilde{1_\epsilon}(x)=\int_x^\infty \nu_\epsilon(z)\frac{dz}{z}
    \le\int_0^\infty \nu_\epsilon(z)\frac{dz}{z},
  $$
  which is $1$ by Lemma \ref{DeltaSpikeMass}.
  -/)
  (proofUses := ["Smooth1", "DeltaSpikeMass"])
  (latexEnv := "lemma")]
  TauCeti.smoothCutoff_le_one

blueprint_comment /--
Combining the above, we have the following three Main Lemmata of this section on the Mellin
transform of $\widetilde{1_{\epsilon}}$.
-/
attribute [blueprint "MellinOfSmooth1a"
  (title := "MellinOfSmooth1a")
  (statement := /--
  Let $\nu$ be supported in $[1/2,2]$ with $\nu(x)/x$ integrable, and $\epsilon>0$. Then for
  $\Re s>0$ the Mellin transform of $\widetilde{1_{\epsilon}}$ is
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(s) =
  \frac{1}{s}\left(\mathcal{M}(\nu)\left(\epsilon s\right)\right).$$
  -/)
  (proof := /--
  By Definition \ref{Smooth1}, $\widetilde{1_\epsilon}=1_{(0,1]}\ast\nu_\epsilon$ on
  $(0,\infty)$. The Mellin transform of a Mellin convolution is the product of the Mellin
  transforms (the integrand $(x,y)\mapsto \nu_\epsilon(y)1_{(0,1]}(x/y)x^{s-1}/y$ has support in
  $y\in[2^{-\epsilon},2^\epsilon]$, $x\in(0,y]$, so Fubini applies). The Mellin transform of
  $1_{(0,1]}$ is $1/s$, and that of $\nu_\epsilon$ is $\mathcal{M}(\nu)(\epsilon s)$ by
  Theorem \ref{MellinOfDeltaSpike}.
  -/)
  (proofUses := ["Smooth1", "MellinConvolutionSymmetric", "MellinOfDeltaSpike"])
  (latexEnv := "lemma")]
  TauCeti.mellin_smoothCutoff

attribute [blueprint "MellinOfSmooth1b"
  (title := "MellinOfSmooth1b")
  (statement := /--
  Let $\nu$ be of class $C^k$ on $(0,\infty)$ and supported in $[1/2,2]$, and let
  $0<\sigma_1$. There is a constant $C$ such that for every $0<\epsilon\le 1$ and every $s$ with
  $\sigma_1\le\Re s\le\sigma_2$,
  $$|\mathcal{M}(\widetilde{1_{\epsilon}})(s)| \le \frac{C}{|s|(1+\epsilon|s|)^k}.$$
  For $k=1$ this gives $\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O(1/(\epsilon|s|^2))$.
  -/)
  (proof := /-- Use Lemma \ref{MellinOfSmooth1a} and the bound in Lemma \ref{MellinOfPsi}. -/)
  (proofUses := ["MellinOfSmooth1a", "MellinOfPsi"])
  (latexEnv := "lemma")]
  TauCeti.exists_norm_mellin_smoothCutoff_le

attribute [blueprint "MellinOfSmooth1c"
  (title := "MellinOfSmooth1c")
  (statement := /--
  Let $\nu\ge 0$ be supported in $[1/2,2]$ with mass one. For $0<\epsilon\le 1$,
  $$|\mathcal{M}(\widetilde{1_{\epsilon}})(1) - 1|\le 2\log 2\cdot\epsilon.$$
  -/)
  (proof := /--
  Follows from Lemmas \ref{MellinOfSmooth1a} and \ref{MellinOfDeltaSpikeAt1_asymp}.
  -/)
  (proofUses := ["MellinOfSmooth1a", "MellinOfDeltaSpikeAt1_asymp"])
  (latexEnv := "lemma")]
  TauCeti.norm_mellin_smoothCutoff_one_sub_one_le

attribute [blueprint "Smooth1ContinuousAt"
  (title := "Smooth1ContinuousAt")
  (statement := /--
  If $\nu(x)/x$ is integrable on $(0,\infty)$ and $\epsilon>0$, then $\widetilde{1_{\epsilon}}$
  is continuous on $(0,\infty)$.
  -/)
  (proof := /--
  $\widetilde{1_\epsilon}(x)=\int_x^\infty\nu_\epsilon(z)\frac{dz}{z}$ is the integral of an
  integrable function over a half-line, which depends continuously on its endpoint.
  -/)
  (proofUses := ["Smooth1"])
  (latexEnv := "lemma")]
  TauCeti.continuousOn_smoothCutoff
