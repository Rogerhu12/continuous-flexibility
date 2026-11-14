module

public import ContinuousFlexibility.Analysis.N06CurrentScalarPairing
public import ContinuousFlexibility.Analysis.N06CurrentPhysicalTests
public import ContinuousFlexibility.Analysis.N06NamedPhysicalRelation

/-!
# The literal current physical residual as a finite Green sum

This is an identity for arbitrary original canonical data. The full
physical height includes its actual left-cutoff scalar, and the source
is the original named periodic reconstruction. All three columns remain
visible. The only scalar remainder after the canonical Green sum is the
left-cutoff Green identity; it is displayed explicitly here.

The physical test need only be an original RadialTest. No periodicity of
the bare corrected operator, finite angular support, or weak PDE is an
input to this change-of-variables identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The finite canonical remainder sum subtracts exactly the three
actual current physical columns, with their original scalar coordinates. -/
theorem n06_currentRemainderSource_full_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    (Real.pi⁻¹ * ∑ m ∈ hfinite.toFinset,
      ∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) =
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) (r, θ) * φ (r, θ))) -
      u.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06CurrentLeftColumn S L z (r, θ) * φ (r, θ))) -
      u.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * φ (r, θ))) -
      u.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) := by
  have hψ (m : ℕ) : MemLp (canonicalHeight S K z m (n06_radialTestAverage φ))
      2 (canonicalMeasure S K m) :=
    n06_current_canonicalHeight_memLp h04 hz hs m
      (n06_radialTestAverage_test hφ).1.continuous.continuousOn
  have hshift : ContDiff ℝ ∞ (fun p : PolarPoint => φ (p + (0, Real.pi))) :=
    hφ.1.comp (contDiff_id.add contDiff_const)
  have hf := n06_fullCanonical_source_pairing h01.1.1.choose_spec.1.2.1.le h04 hz hs
    hfinite F (n06_physical_representation h04 hz hs (0 : CanonicalUnknown S K) F).1.2
    (n06PhysicalSource_periodic h04 hz hs _)
    (fun m => n06_current_canonicalHeight_memLp h04 hz hs m hφ.1.continuous.continuousOn)
    (fun m => n06_current_canonicalHeight_memLp h04 hz hs m hshift.continuous.continuousOn)
    hsupport
  have hc (i : Fin 3) := n06_currentScalarField_full_pairing hT hS h01 h03 h04 hz hs
    hfinite hφ hsupport i
  change _ = (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) (r, θ) * φ (r, θ))) -
      u.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06CurrentScalarField D S C L z 0 (r, θ) * φ (r, θ))) -
      u.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06CurrentScalarField D S C L z 1 (r, θ) * φ (r, θ))) -
      u.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06CurrentScalarField D S C L z 2 (r, θ) * φ (r, θ)))
  rw [hf, hc 0, hc 1, hc 2]
  simp_rw [n06_currentRemainderSource_pairing hT hS h01 h03 h04 hz hs u F _ (hψ _)]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The exact full physical residual equals the negative canonical Green
sum plus the displayed left-column Green defect. All test integrability
is supplied by the original contracts, including the shifted L phi. -/
theorem n06_current_physicalResidual_eq_finiteGreen
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K)
    {J : Set ℝ} (hJ : IsClosed J)
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalHeight K z (fun m => (u.1 m : PolarPoint → ℝ)) u.2.1 (r, θ) *
        divergenceOperator (L.coefficients z) φ (r, θ))) +
      u.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * φ (r, θ))) +
      u.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) -
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) (r, θ) * φ (r, θ)))) =
      -Real.pi⁻¹ * (∑ m ∈ hfinite.toFinset,
        ((∫ p, n06CurrentRemainderSource D S C L K z u F m p *
          canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
        ∫ p, u.1 m p * canonicalSource S K z m
          (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
            ∂canonicalMeasure S K m)) +
      u.2.1 * ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
        S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, θ))) -
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          n06CurrentLeftColumn S L z (r, θ) * φ (r, θ))) := by
  have hL₀ (m : ℕ) : MemLp
      (canonicalSource S K z m (divergenceOperator (L.coefficients z) φ))
        2 (canonicalMeasure S K m) :=
    n06_current_operatorTest_memLp hT hS h01 h03 h04 hz hs m hφ
  have hL₁ (m : ℕ) : MemLp
      (canonicalSource S K z m
        (fun p => divergenceOperator (L.coefficients z) φ (p + (0, Real.pi))))
          2 (canonicalMeasure S K m) := by
    simpa only [Nat.cast_one, one_mul] using
      n06_current_shifted_operatorTest_memLp hT hS h01 h03 h04 hz hs m 1 hφ
  have hLsupport : ∀ r, r ∉ J → ∀ θ,
      divergenceOperator (L.coefficients z) φ (r, θ) = 0 :=
    fun r hr θ => n06_divergenceOperator_zero_off_radial_support
      (L.coefficients z) hJ hsupport hr θ
  have hheight := n06_physicalHeight_affine_pairing hS h04 hz hs u.1 u.2.1
    hfinite hL₀ hL₁ hLsupport
  have hsource := n06_currentRemainderSource_full_pairing hT hS h01 h03 h04 hz hs
    u F hfinite hφ hsupport
  rw [hheight, Finset.sum_sub_distrib]
  linear_combination hsource

end ContinuousFlexibility.Statements
