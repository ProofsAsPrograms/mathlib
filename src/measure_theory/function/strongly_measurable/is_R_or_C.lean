/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import measure_theory.function.strongly_measurable.basic
import data.complex.is_R_or_C

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/

variables {α : Type*}
namespace measure_theory

/-! ## Strongly measurable functions -/

namespace ae_strongly_measurable

variables {m : measurable_space α} {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜]

protected lemma re {f : α → 𝕜} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, is_R_or_C.re (f x)) μ :=
is_R_or_C.continuous_re.comp_ae_strongly_measurable hf

protected lemma im {f : α → 𝕜} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, is_R_or_C.im (f x)) μ :=
is_R_or_C.continuous_im.comp_ae_strongly_measurable hf

end ae_strongly_measurable

end measure_theory
