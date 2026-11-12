import ContinuousFlexibility.Analysis.N06ReferenceNormalProjection
import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
import ContinuousFlexibility.Analysis.N05ReferenceAngularJetEstimate
import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakClosure

/-!
# Angular estimates for the same physical first normal derivative

Apply the original first-normal estimate to a genuine singleton source.
The same physical inverse commutes with that high angular projection.
Uniqueness of weak normal coefficients identifies the resulting normal
mode with the original derivative mode. Weighted Parseval then gives all
finite angular orders with the original material exponents and exactly
one additional source angular derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n06_normal_projection_memLp {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : MemLp f 2 (radialPhysicalMeasure D)) (I : Finset ℕ) :
    MemLp (referenceBasisProjection I f) 2 (radialPhysicalMeasure D) := by
  have hprod : MemLp f 2 ((volume.restrict (radialCore D)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    simpa only [radialPhysicalMeasure_eq_prod] using hf
  simpa only [radialPhysicalMeasure_eq_prod] using memLp_referenceBasisProjection_prod hprod I

/-- The finite first angular derivative has the original physical weak
meaning even when its radial coefficient is only L2. -/
theorem n06_referenceHighAngularJet_first_weak (D : ReferenceData)
    (J : Finset ℕ) (f : PolarPoint → ℝ) :
    WeakAngularDerivative D (referenceBasisProjection (J.image (fun n => n + 2)) f)
      (n05_referenceHighAngularJet J 1 f) := by
  intro φ hφ
  have h := n05_referenceHighAngularJet_weak D J 1 f φ hφ
  rw [n06_mixedAngular_one_eq_angularPartial hφ.1] at h
  simp only [pow_one, neg_one_mul] at h
  exact (neg_eq_iff_eq_neg.mpr h).symm

/-- One original first-normal constant controls every actual high normal
mode. The derivative field is the same one before the mode is chosen. -/
theorem n06_referenceInverse_highNormal_mode_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur →
      OutputRealization D γ M₁ 0 (ur, 0) → ∀ n : ℕ,
      0 ≤ n05_referenceHighOutputSquare D γ M₁ (ur, 0) n ∧
      n05_referenceHighOutputSquare D γ M₁ (ur, 0) n ≤
        C0 ^ 2 * (1 + (((2 * (n + 2) : ℕ) : ℝ) ^ 2)) *
          n05_referenceHighSourceSquare D γ M₀ F n := by
  obtain ⟨C0, hC0, hnormal⟩ := hN
  refine ⟨C0, hC0, fun F hF ur hweak hreal n => ?_⟩
  have hab := hD.choose_spec.1.2.1.le
  let I : Finset ℕ := {n + 2}
  have hI : ∀ k ∈ I, 2 ≤ k := by
    intro k hk
    have hk' : k = n + 2 := Finset.mem_singleton.mp hk
    omega
  have hsource : SourceMember D γ M₀ (referenceBasisProjection I F.1, 0) :=
    n05_referenceHighProjection_sourceMember hD hF hI
  have hθ : SourceDerivativeMember D γ M₀ (n05_referenceHighAngularJet {n} 1 F.1) :=
    (n05_referenceHighAngularJet_source_norm hD hF {n} 1).1
  have hθweak : WeakAngularDerivative D (referenceBasisProjection I F.1)
      (n05_referenceHighAngularJet {n} 1 F.1) := by
    simpa only [Finset.image_singleton, I] using
      n06_referenceHighAngularJet_first_weak D {n} F.1
  obtain ⟨d, hdweak, hdreal, hdbound⟩ := hnormal _ _ hsource hθweak hθ
  have hu := r11b_output_memLp hD hborder hγ (hG.1 F hF).1
  have hur : MemLp ur 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using
      r11b_outputRemainder_memLp hD hγ hreal
  have hd : MemLp d 2 (radialPhysicalMeasure D) := by
    simpa only [n06_outputRemainder_zero] using
      r11b_outputRemainder_memLp hD hγ hdreal
  have hGsource := r11b_output_memLp hD hborder hγ (hG.1 _ hsource).1
  have hrep := n05_referenceInverse_highProjection hD hborder hγ hG hF hI
  have hpweak := WeakNormalDerivative.n06_congr_left
    (WeakNormalDerivative.n06_basisProjection hweak hab hu hur I) hab
    (n06_normal_projection_memLp hu I) hGsource hrep.2.symm
  have hcoeff := WeakNormalDerivative.n06_coefficient_unique hpweak hab
    (n06_normal_projection_memLp hur I) hd hdweak (n + 2)
  have hcoeff' : referenceRadialCoefficient ur (n + 2)
      =ᵐ[volume.restrict (radialCore D)] referenceRadialCoefficient d (n + 2) := by
    have hprojection : referenceRadialCoefficient (referenceBasisProjection I ur) (n + 2) =
        referenceRadialCoefficient ur (n + 2) := by
      funext r
      change referenceAngularCoefficient (angularBasisProjection I (fun θ => ur (r, θ)))
        (n + 2) = referenceAngularCoefficient (fun θ => ur (r, θ)) (n + 2)
      simp only [referenceAngularCoefficient_projection, I, Finset.mem_singleton_self, ite_true]
    rw [hprojection] at hcoeff
    exact hcoeff
  have heq : referenceBasisProjection I ur =ᵐ[radialPhysicalMeasure D]
      referenceBasisProjection I d := by
    rw [radialPhysicalMeasure_eq_prod]
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (radialCore D))
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).ae hcoeff'] with p hp
    simp only [I, referenceBasisProjection, angularBasisProjection, Finset.sum_singleton]
    change referenceRadialCoefficient ur (n + 2) p.1 * referenceAngularBasis (n + 2) p.2 =
      referenceRadialCoefficient d (n + 2) p.1 * referenceAngularBasis (n + 2) p.2
    rw [hp]
  obtain ⟨hup, _⟩ := n06_zeroOutput_projection_bound hab hreal I
  obtain ⟨_, hdp⟩ := n06_zeroOutput_projection_bound hab hdreal I
  have hnorm : outputNormSquare D γ M₁ 0 (referenceBasisProjection I ur, 0) =
      outputNormSquare D γ M₁ 0 (referenceBasisProjection I d, 0) :=
    outputNormSquare_congr_ae hab hup ⟨rfl, heq⟩
  have hθnorm : sourceNormSquare D γ M₀ (n05_referenceHighAngularJet {n} 1 F.1, 0) =
      (((2 * (n + 2) : ℕ) : ℝ) ^ 2) * n05_referenceHighSourceSquare D γ M₀ F n := by
    simpa only [Finset.sum_singleton, Nat.mul_one] using
      (n05_referenceHighAngularJet_source_norm hD hF {n} 1).2
  refine ⟨outputNormSquare_nonneg hab hup, ?_⟩
  change outputNormSquare D γ M₁ 0 (referenceBasisProjection I ur, 0) ≤ _
  calc
    _ = outputNormSquare D γ M₁ 0 (referenceBasisProjection I d, 0) := hnorm
    _ ≤ outputNormSquare D γ M₁ 0 (d, 0) := hdp
    _ ≤ C0 ^ 2 * (sourceNormSquare D γ M₀ (referenceBasisProjection I F.1, 0) +
        sourceNormSquare D γ M₀ (n05_referenceHighAngularJet {n} 1 F.1, 0)) := hdbound
    _ = _ := by
      rw [hθnorm]
      change C0 ^ 2 * (n05_referenceHighSourceSquare D γ M₀ F n +
        (((2 * (n + 2) : ℕ) : ℝ) ^ 2) * n05_referenceHighSourceSquare D γ M₀ F n) = _
      ring

/-- Exact finite-jet Parseval turns the mode estimate into the actual
angular derivatives of the original physical normal field. -/
theorem n06_referenceInverse_finiteAngularNormal_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F, SourceMember D γ M₀ F →
      ∀ ur : PolarPoint → ℝ, WeakNormalDerivative D (G F).1 ur →
      OutputRealization D γ M₁ 0 (ur, 0) → ∀ J : Finset ℕ, ∀ b : ℕ,
      outputNormSquare D γ M₁ 0 (n05_referenceHighAngularJet J b ur, 0) ≤
        C0 ^ 2 * (sourceNormSquare D γ M₀ (n05_referenceHighAngularJet J b F.1, 0) +
          sourceNormSquare D γ M₀ (n05_referenceHighAngularJet J (b + 1) F.1, 0)) := by
  obtain ⟨C0, hC0, hbound⟩ :=
    n06_referenceInverse_highNormal_mode_bound hD hborder hγ hG hN
  refine ⟨C0, hC0, fun F hF ur hweak hreal J b => ?_⟩
  rw [(n05_referenceHighAngularJet_output_norm hD hborder hγ hreal J b).2.2,
    (n05_referenceHighAngularJet_source_norm hD hF J b).2,
    (n05_referenceHighAngularJet_source_norm hD hF J (b + 1)).2,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hp : 0 ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) := by positivity
  calc
    _ ≤ (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        (C0 ^ 2 * (1 + (((2 * (n + 2) : ℕ) : ℝ) ^ 2)) *
          n05_referenceHighSourceSquare D γ M₀ F n) :=
      mul_le_mul_of_nonneg_left (hbound F hF ur hweak hreal n).2 hp
    _ = _ := by
      rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
      ring

end ContinuousFlexibility.Radial
