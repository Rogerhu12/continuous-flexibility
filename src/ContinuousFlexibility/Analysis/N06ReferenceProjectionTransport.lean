import ContinuousFlexibility.Analysis.N06ReferenceModeTransport
import ContinuousFlexibility.Analysis.N06GlobalFourierApproximants
import ContinuousFlexibility.Radial.ReferenceGraphProjection

/-!
# The actual reference chart commutes with physical angular projection

The controlled reference chart preserves the angle and has a radial
height and Jacobian. The original physical cosine projection therefore
commutes with both genuine canonical transformations. A second lemma
identifies the canonical half-period L2 cutoff with that full-period
physical projection. No finite spectrum of the compatibility column or
of an inverse image is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped BigOperators Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The normalized bases used by the full physical projection and the
original canonical modal equation have identical coefficients. -/
theorem n06_referenceAngularCoefficient_eq_evenFourier
    (f : PolarPoint → ℝ) (n : ℕ) (r : ℝ) :
    referenceAngularCoefficient (fun θ => f (r, θ)) n = evenFourierCoefficient f n r := by
  simp only [referenceAngularCoefficient, evenFourierCoefficient, angularPairing,
    angularAverage, radialAngularMean, one_div, n06_referenceAngularBasis_eq_evenCosineBasis]

/-- The finite half-period cosine polynomial depends only on the original
L2 class, even if the selected total representatives are not periodic. -/
theorem n06_canonicalCosineCut_congr_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U W : PolarPoint → ℝ} (hUW : U =ᵐ[canonicalMeasure S K m] W) (N : ℕ) :
    n06CylinderCosineCut N U =ᵐ[canonicalMeasure S K m] n06CylinderCosineCut N W := by
  have hco : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ n : ℕ, n06HalfCosineCoefficient U n r = n06HalfCosineCoefficient W n r :=
    ae_all_iff.mpr (fun n => n06_canonical_halfCosineCoefficient_congr_ae hUW n)
  rw [n06_canonicalMeasure_eq_radial_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hco] with p hp
  change (∑ n ∈ Finset.range (N + 1),
      n06HalfCosineCoefficient U n p.1 * referenceAngularBasis n p.2) = _
  exact Finset.sum_congr rfl (fun n _ => congrArg (· * referenceAngularBasis n p.2) (hp n))

/-- The half-period cutoff equals the full-period projection of a genuine
periodic representative, including the zeroth mode. -/
theorem n06_canonicalCosineCut_eq_referenceProjection_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {W : PolarPoint → ℝ} (hW : MemLp W 2 (canonicalMeasure S K m))
    (hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => W (r, θ)) Real.pi) (N : ℕ) :
    n06CylinderCosineCut N W =ᵐ[canonicalMeasure S K m]
      referenceBasisProjection (Finset.range (N + 1)) W := by
  have hWp : MemLp W 2
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) := by
    simpa only [n06_canonicalMeasure_eq_radial_prod] using hW
  have hc : ∀ᵐ r ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ n : ℕ, n06HalfCosineCoefficient W n r =
        referenceAngularCoefficient (fun θ => W (r, θ)) n := by
    filter_upwards [r11b_memLp_product_sections hWp,
      ae_restrict_mem measurableSet_Ioo] with r hr hrI
    intro n
    have hb : MemLp (referenceAngularBasis n) 2 angleMeasure :=
      memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis n).continuous
    have hi : IntervalIntegrable (fun θ => W (r, θ) * referenceAngularBasis n θ)
        volume 0 Real.pi :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
        (hr.integrable_mul hb)
    exact (n06_halfCosineCoefficient_eq_evenFourierCoefficient W n r (hp r hrI) hi).trans
      (n06_referenceAngularCoefficient_eq_evenFourier W n r).symm
  rw [n06_canonicalMeasure_eq_radial_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hc] with p hp
  change (∑ n ∈ Finset.range (N + 1),
      n06HalfCosineCoefficient W n p.1 * referenceAngularBasis n p.2) = _
  exact Finset.sum_congr rfl (fun n _ => congrArg (· * referenceAngularBasis n p.2) (hp n))

/-- A reflected original L2 field has the physical finite projection of
any actual periodic representative as its precise Fourier cutoff. -/
theorem n06CanonicalFourierCutL2_coe_referenceProjection_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    {W : PolarPoint → ℝ} (hUW : (U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] W)
    (hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => W (r, θ)) Real.pi) (N : ℕ) :
    (n06CanonicalFourierCutL2 N U : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      referenceBasisProjection (Finset.range (N + 1)) W :=
  ((n06CanonicalFourierCutL2_coe_cosine_ae N U he).trans
    (n06_canonicalCosineCut_congr_ae hUW N)).trans
      (n06_canonicalCosineCut_eq_referenceProjection_ae
        ((memLp_congr_ae hUW).mp (Lp.memLp U)) hp N)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped BigOperators Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The genuine inverse preserves every circle, as forced by the actual
reference chart and its inverse identities on the open piece. -/
theorem n06_controlledReference_inverse_circle
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) (θ : ℝ) :
    K.inverseChart (C.referenceState, 0) m (p.1, θ) =
      ((K.inverseChart (C.referenceState, 0) m p).1, θ) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have hc := h04.1.charts
    (C.referenceState, 0) (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m
  rw [h04.1.referenceDomain m] at hc
  let x := K.inverseChart (C.referenceState, 0) m p
  have hx : x ∈ referencePhysicalPieceOpen S K m := hc.2.1 hp
  have hy : (K.chart (C.referenceState, 0) m (x.1, 0)).1 = p.1 := by
    have he := congrArg Prod.fst (hc.2.2.2.1 p hp)
    rw [(hcoordinates.1 m x hx).1] at he
    exact he
  have hq : (x.1, θ) ∈ referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  have he := (hcoordinates.1 m (x.1, θ) hq).1
  rw [hy] at he
  exact (congrArg (K.inverseChart (C.referenceState, 0) m) he).symm.trans
    (hc.2.2.1 _ hq)

/-- The true reference height transform has one radial multiplier along
an entire canonical circle. -/
theorem n06_controlledReferenceHeight_circle
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) (θ : ℝ) :
    let x := K.inverseChart (C.referenceState, 0) m p
    canonicalHeight S K (C.referenceState, 0) m f (p.1, θ) =
      (K.height (C.referenceState, 0) m (x.1, 0))⁻¹ * f (x.1, θ) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have hx := (h04.1.charts (C.referenceState, 0)
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m).2.1 hp
  rw [h04.1.referenceDomain m] at hx
  have hq : ((K.inverseChart (C.referenceState, 0) m p).1, θ) ∈
      referencePhysicalPieceOpen S K m := ⟨hx.1, mem_univ _⟩
  dsimp only [canonicalHeight]
  rw [n06_controlledReference_inverse_circle h hcoordinates m hp θ,
    (hcoordinates.1 m _ hq).2]
  exact div_eq_inv_mul _ _

/-- Physical finite projection commutes pointwise with the actual
reference height transform, without any smoothness assumption on f. -/
theorem n06_controlledReferenceHeight_projection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (I : Finset ℕ) (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K (C.referenceState, 0) m (referenceBasisProjection I f) p =
      referenceBasisProjection I (canonicalHeight S K (C.referenceState, 0) m f) p := by
  have he := n06_controlledReferenceHeight_circle h hcoordinates f m hp
  have hproj := n06_controlledReferenceHeight_circle h hcoordinates
    (referenceBasisProjection I f) m hp p.2
  rw [show (p.1, p.2) = p from Prod.eta p] at hproj
  rw [hproj]
  simp only [referenceBasisProjection, angularBasisProjection]
  simp_rw [he, referenceAngularCoefficient_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

/-- Physical finite projection also commutes with the genuine source
transform, including its actual Jacobian factor. -/
theorem n06_controlledReferenceSource_projection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (I : Finset ℕ) (f : PolarPoint → ℝ) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K (C.referenceState, 0) m (referenceBasisProjection I f) p =
      referenceBasisProjection I (canonicalSource S K (C.referenceState, 0) m f) p := by
  have hproj := n06_controlledReferenceSource_angularJet h hcoordinates
    (referenceBasisProjection I f) m 0 hp
  simp only [spaces_mixedDerivative_zero] at hproj
  have he (θ : ℝ) :
      canonicalSource S K (C.referenceState, 0) m f (p.1, θ) =
        (K.height (C.referenceState, 0) m
            ((K.inverseChart (C.referenceState, 0) m p).1, 0) /
          |deriv (fun r => (K.chart (C.referenceState, 0) m (r, 0)).1)
            (K.inverseChart (C.referenceState, 0) m p).1|) *
          f ((K.inverseChart (C.referenceState, 0) m p).1, θ) := by
    have hj := n06_controlledReferenceSource_angularJet h hcoordinates f m 0
      (p := (p.1, θ)) ⟨hp.1, mem_univ _⟩
    simp only [spaces_mixedDerivative_zero] at hj
    rw [n06_controlledReference_inverse_circle h hcoordinates m hp θ] at hj
    exact hj
  rw [hproj]
  simp only [referenceBasisProjection, angularBasisProjection]
  simp_rw [he, referenceAngularCoefficient_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)

end ContinuousFlexibility.Statements
