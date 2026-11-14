module

public import ContinuousFlexibility.Blueprint.Statements
public import ContinuousFlexibility.Radial.ReferenceNaturalKernel
public import ContinuousFlexibility.Radial.ReferenceSourceDensity
public import ContinuousFlexibility.Radial.ReferenceSmoothInverse
public import ContinuousFlexibility.Radial.ReferenceSmoothCore
public import ContinuousFlexibility.Radial.ReferenceSmoothGraphGreen

/-!
# Blueprint node R12

The fixed radial reference uses one geometry, border, maximal weak graph,
and inverse at the three reference exponents. The construction interface
retains the homogeneous profile and return margins on that same witness.

Source: `paper/flexible-surface-readable/04-reference-overview.tex` lines 49–201
and `paper/flexible-surface-readable/06-global-reference-inverse.tex` lines 1017–1169.
-/

@[expose] public section

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

theorem R12 (hR06 : R06Statement) (hR08 : R08Statement)
    (hR10 : R10Statement) (hR11 : R11Statement) : R12Statement := by
  obtain ⟨D, hD, hborder, hgeometry, ε, M₀, M₁, hε, hεlt, G, hmodes, hG⟩ := hR11
  have hmodal (j : ℕ) (hj : 2 ≤ j) (he : Even j) :
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H := by
    obtain ⟨H, hH, _⟩ := hmodes j hj he
    exact ⟨H, hH⟩
  have hnatural : RadialNaturalKernels D :=
    radialNaturalKernels_of_modeInverses hD hborder hgeometry.1 hmodal
  refine ⟨⟨D, hD, hnatural, hgeometry.2, hborder, ε, M₀, M₁, hε, hεlt, G, ?_⟩⟩
  intro γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;> dsimp only [referenceBeta] <;> linarith only [hε, hεlt]
  obtain ⟨hinverse, hnormal⟩ := hG γ hγ
  have hcore : ReferenceSmoothCoreClosure D γ M₀ M₁ := by
    apply referenceSmoothCoreClosure_of_dense_inverse_core hD hinverse
      (ReferenceSmoothFiniteSource D)
    · intro F hF
      obtain ⟨Fₙ, hsmooth, _, hmember, hconv⟩ :=
        hF.exists_smoothFinite_approximation hD
      exact ⟨Fₙ, fun n => ⟨hmember n, hsmooth n⟩, hconv⟩
    · intro F hF hfinite
      exact reference_smooth_inverse_image hD hborder hgeometry.1
        (hmodal 2 le_rfl (by decide)) hinverse hnormal hγpos hF hfinite
  exact ⟨hinverse, referenceGraphClosed_of_positive hD hborder hγpos, hcore,
    referenceGreenReciprocity_of_smooth_core hD hborder hγpos hcore, hnormal⟩

end ContinuousFlexibility.Blueprint

#print axioms ContinuousFlexibility.Blueprint.R12
