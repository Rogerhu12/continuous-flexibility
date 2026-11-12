import ContinuousFlexibility.Analysis.N07aBaseInverse

/-!
# Feeding the lifted corrected source into the actual reference inverse

Once Step B has produced a weighted realization of `P.inverse z F`, the
existing N05 estimates apply to that realization.  The coherence clause
identifies their field and first radial derivative with the same Banach
solution `n07aBaseInverse`; no new choice of solution is made.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aWeightedSolutionLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _

local instance n07aWeightedSolutionLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _

local instance n07aWeightedSolutionUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance

local instance n07aWeightedSolutionUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance

local instance n07aWeightedSolutionGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _

local instance n07aWeightedSolutionGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private theorem n07a_weighted_reference_estimate
    (h05 : N05Properties D T S C K V b B) (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ U : V.level (3 / 4 : ℝ) t s,
      ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) t s U)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K
          (B.globalInverse (V.forget (3 / 4 : ℝ) t s U)) ≤ C0 * ‖U‖ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.2.1 t s

private theorem n07a_weighted_reference_firstNormal
    (h05 : N05Properties D T S C K V b B) (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ U : V.level (3 / 4 : ℝ) t (s + 1),
      ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W m p * φ p
            ∂canonicalMeasure S K m) =
          -(∫ p, (B.globalInverse (V.forget (3 / 4 : ℝ) t (s + 1) U)).1 m p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧
        ‖W‖ ≤ C0 * ‖U‖ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.2.2 t s

private theorem n07a_weighted_source_coherence
    (h05 : N05Properties D T S C K V b B) {t : ℝ} {s : ℕ}
    {z : AnnularState S × ℝ} {F : V.level (3 / 4 : ℝ) 0 b}
    {U : V.level (3 / 4 : ℝ) t s}
    (hU : V.forget (3 / 4 : ℝ) t s U =
      V.forget (3 / 4 : ℝ) 0 b (P.inverse z F)) :
    B.globalInverse (V.forget (3 / 4 : ℝ) t s U) =
      (n07aBaseInverse B P z F).val.1 :=
  (congrArg B.globalInverse hU).trans (n07aBaseInverse_global h05 z F).symm

/-- The actual field and all three scalars satisfy N05's weighted estimate
for every weighted realization of the corrected source. -/
theorem n07aAngularBaseSolution_weighted
    (h05 : N05Properties D T S C K V b B) (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (z : AnnularState S × ℝ)
      (F : V.level (3 / 4 : ℝ) 0 b) (U : V.level (3 / 4 : ℝ) t s),
      V.forget (3 / 4 : ℝ) t s U = V.forget (3 / 4 : ℝ) 0 b (P.inverse z F) →
      ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W =
          (fun m => (n07aBaseInverse B P z F).val.1.1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (n07aBaseInverse B P z F).val.1 ≤ C0 * ‖U‖ := by
  obtain ⟨C0, hC0, hbound⟩ := n07a_weighted_reference_estimate h05 t s
  refine ⟨C0, hC0, ?_⟩
  intro z F U hU
  have h := hbound U
  have he := n07a_weighted_source_coherence h05 hU
  exact he ▸ h

/-- The same weighted realization gives the genuine first weak radial
derivative with one fewer angular derivative, as recorded by N05. -/
theorem n07aAngularBaseSolution_firstNormal_weighted
    (h05 : N05Properties D T S C K V b B) (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (z : AnnularState S × ℝ)
      (F : V.level (3 / 4 : ℝ) 0 b) (U : V.level (3 / 4 : ℝ) t (s + 1)),
      V.forget (3 / 4 : ℝ) t (s + 1) U = V.forget (3 / 4 : ℝ) 0 b (P.inverse z F) →
      ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W m p * φ p
            ∂canonicalMeasure S K m) =
          -(∫ p, (n07aBaseInverse B P z F).val.1.1 m p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧
        ‖W‖ ≤ C0 * ‖U‖ := by
  obtain ⟨C0, hC0, hbound⟩ := n07a_weighted_reference_firstNormal h05 t s
  refine ⟨C0, hC0, ?_⟩
  intro z F U hU
  have h := hbound U
  have he := n07a_weighted_source_coherence h05 hU
  exact he ▸ h

end ContinuousFlexibility.Statements
