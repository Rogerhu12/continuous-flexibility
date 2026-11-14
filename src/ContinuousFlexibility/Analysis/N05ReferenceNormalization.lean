module

public import ContinuousFlexibility.Analysis.N05ReferenceAuxiliary
public import ContinuousFlexibility.Scalar.WeightedAngularMeanJets
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The physical source normalization in the reference angular convention

Physical heights are pi-periodic. Their angular slices are continuous,
including the prescribed zero extension outside the open annulus. Actual
interval integrability therefore identifies the normalized averages over
one and two periods. The physical compatibility functional, its kernel,
and its fixed normalizer retain exactly their reference-space integrals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory

/-- One-period integrability and periodicity justify replacing the reference
two-period average by the physical one-period average. -/
theorem n05_radialAngularMean_eq_angularMean {f : ℝ → ℝ}
    (hp : Function.Periodic f Real.pi)
    (hi : IntervalIntegrable f volume 0 Real.pi) :
    radialAngularMean f = angularMean f := by
  have hdouble : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    simpa only [zero_add, two_mul] using
      hp.intervalIntegral_add_eq_add 0 Real.pi
        (hp.intervalIntegrable₀ Real.pi_ne_zero hi)
  rw [radialAngularMean, angularMean, hdouble]
  field_simp [Real.pi_ne_zero] <;> ring

/-- The slice lemma uses both interior smoothness and the zero extension
in `HeightMember`, so this equality holds at every radius. -/
theorem n05_heightMember_radialAngularMean
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (r : ℝ) :
    radialAngularMean (fun θ => f (r, θ)) = angularMean (fun θ => f (r, θ)) := by
  apply n05_radialAngularMean_eq_angularMean
  · intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hf.2.2.1 (r, θ)
  · exact (heightMember_continuous_angularSlice hf r).intervalIntegrable 0 Real.pi

theorem n05_heightMember_referenceIntegral
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ))) =
      physicalSourceIntegral D f := by
  unfold physicalSourceIntegral
  apply intervalIntegral.integral_congr
  intro r _
  exact n05_heightMember_radialAngularMean hf r

/-- The actual decoder and compatibility functional use the same normalized
integral as the radial reference graph. -/
theorem n05_physicalSpaces_referenceIntegral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (u : (S.height (3 / 4 : ℝ)).Space) :
    (∫ r in D.a..D.b,
      radialAngularMean (fun θ => (S.height (3 / 4 : ℝ)).decode u (r, θ))) = S.Q u := by
  rcases hS with ⟨hSob, _, _, _, _, _, _, hQ, _⟩
  exact (n05_heightMember_referenceIntegral ((hSob _).2.2.2.1 u)).trans (hQ u).symm

theorem n05_physicalSpaces_normalizer_referenceIntegral
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    (∫ r in D.a..D.b,
      radialAngularMean (fun θ => (S.height (3 / 4 : ℝ)).decode S.psi (r, θ))) = 1 := by
  have hψ : S.Q S.psi = 1 := by
    rcases hS with ⟨_, _, _, _, _, _, _, _, _, hψ, _⟩
    exact hψ
  exact (n05_physicalSpaces_referenceIntegral hS S.psi).trans hψ

theorem n05_physicalSource_referenceIntegral_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : S.Source) :
    (∫ r in D.a..D.b,
      radialAngularMean (fun θ => (S.height (3 / 4 : ℝ)).decode f.val (r, θ))) = 0 := by
  exact (n05_physicalSpaces_referenceIntegral hS f.val).trans
    (LinearMap.mem_ker.mp f.property)

/-- The prescribed physical normalizer fixes the auxiliary scalar for
compatible representatives at arbitrary positive reference exponents. -/
theorem n05_physicalSpaces_auxiliaryScalar_unique
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    {γ₀ γ₁ M₀ M₁ a b : ℝ} (hγ₀ : 0 < γ₀) (hγ₁ : 0 < γ₁)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g)
    (hf : SourceMember D γ₀ M₀
      ((fun p => f p - a * (S.height (3 / 4 : ℝ)).decode S.psi p), 0))
    (hg : SourceMember D γ₁ M₁
      ((fun p => g p - b * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)) :
    a = b :=
  n05_referenceAuxiliaryScalar_unique hD hγ₀ hγ₁
    (n05_physicalSpaces_normalizer_referenceIntegral hS) hfg hf hg

end ContinuousFlexibility.Statements
