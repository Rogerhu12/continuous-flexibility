import ContinuousFlexibility.Analysis.N07aCanonicalModeEquation
import ContinuousFlexibility.Analysis.N07aIntervalEquationUnit
import ContinuousFlexibility.Analysis.N07aReferenceUnitJets

/-!
# Actual cosine modes on the unit interval

These are genuine L² classes of the prescribed canonical representatives.
Affine normalization retains the exact interval length in both weak
derivatives and the second-order equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_interval_compact_pairing_congr {a b : ℝ} {f g φ : ℝ → ℝ}
    (he : f =ᵐ[volume.restrict (Ioo a b)] g) (hs : tsupport φ ⊆ Ioo a b) :
    (∫ x, f x * φ x) = ∫ x, g x * φ x := by
  have h := (ae_restrict_iff' measurableSet_Ioo).mp he
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxi : x ∈ Ioo a b
  · rw [hx hxi]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxi (hs ht)), mul_zero, mul_zero]

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n07aCanonicalRadialMode (u : CanonicalL2 S K m) (n : ℕ) :
    Lp ℝ 2 (volume.restrict (Ioo (K.left m) (K.right m))) :=
  (n07aCanonicalRadialCoefficient_memLp u n).toLp (n07aHalfRadialCoefficient u n)

theorem n07aCanonicalRadialMode_ae (u : CanonicalL2 S K m) (n : ℕ) :
    (n07aCanonicalRadialMode u n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
      n07aHalfRadialCoefficient u n :=
  (n07aCanonicalRadialCoefficient_memLp u n).coeFn_toLp

def n07aCanonicalUnitMode (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (n : ℕ) : N07aIntervalL2 :=
  n07aIntervalUnitPullback hm (n07aCanonicalRadialMode u n)

theorem n07aCanonicalUnitMode_ae (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (n : ℕ) :
    (n07aCanonicalUnitMode hm u n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x => n07aHalfRadialCoefficient u n (n07aIntervalUnitMap (K.left m) (K.right m) x) := by
  have hraw := n07aCanonicalRadialMode_ae u n
  have hscaled := Measure.ae_smul_measure hraw (ENNReal.ofReal (K.right m - K.left m)⁻¹)
  have hp := (n07aIntervalUnitMap_preserving hm).quasiMeasurePreserving.ae hscaled
  exact (n07aIntervalUnitPullback_ae hm (n07aCanonicalRadialMode u n)).trans hp

theorem n07aCanonicalUnitMode_norm_sq (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (n : ℕ) :
    ‖n07aCanonicalUnitMode hm u n‖ ^ 2 =
      (K.right m - K.left m)⁻¹ * ‖n07aCanonicalRadialMode u n‖ ^ 2 :=
  n07aIntervalUnitPullback_norm_sq hm (n07aCanonicalRadialMode u n)

theorem n07aCanonicalUnitMode_firstNormal (hm : K.left m < K.right m)
    {u d : CanonicalL2 S K m}
    (hd : N07aWeakCanonicalMixedDerivative S K m u d 1 0) (n : ℕ) :
    HasIntervalWeakDerivative 0 1 (n07aCanonicalUnitMode hm u n)
      ((K.right m - K.left m) • n07aCanonicalUnitMode hm d n) := by
  apply n07a_intervalWeakDerivative_congr
    (g := fun x => (K.right m - K.left m) *
      n07aHalfRadialCoefficient d n (n07aIntervalUnitMap (K.left m) (K.right m) x))
    (n07aCanonicalUnitMode_ae hm u n).symm
  · filter_upwards [n07aCanonicalUnitMode_ae hm d n,
      Lp.coeFn_smul (K.right m - K.left m) (n07aCanonicalUnitMode hm d n)] with x hx hd
    simp only [Pi.smul_apply, smul_eq_mul, hx]
  · exact n07a_interval_weakDerivative_unit hm (n07a_canonical_firstNormal_coefficient hd n)

variable {D : ReferenceData} {T : MaterialData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}

theorem n07aReferenceUnitAtom_A_map (x : ℝ) :
    n07aReferenceUnitAtom D T S C L K m .principalA x =
      (K.coefficients (C.referenceState, 0) m).a
        (n07aIntervalUnitMap (K.left m) (K.right m) x, 0) := by
  simp only [n07aReferenceUnitAtom, CanonicalGeometry.atom,
    CanonicalGeometry.canonicalUnitPoint, n07aIntervalUnitMap, add_comm]

theorem n07aReferenceUnitC_map (x : ℝ) :
    n07aReferenceUnitC D T S C L K m x =
      (K.right m - K.left m) ^ 2 * (K.coefficients (C.referenceState, 0) m).c
        (n07aIntervalUnitMap (K.left m) (K.right m) x, 0) := by
  simp only [n07aReferenceUnitC, n07aReferenceUnitAtom, CanonicalGeometry.atom,
    CanonicalGeometry.canonicalUnitPoint, n07aIntervalUnitMap, add_comm]

/-- The actual reference weak equation in normalized radial coordinates. -/
theorem n07a_reference_canonical_unitMode_equation
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (hP : CanonicalGeometry.ReferencePrincipal T S C K)
    (hm : K.left m < K.right m) {u G : CanonicalL2 S K m}
    (heq : N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G)
    (n : ℕ) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
      (∫ x, n07aCanonicalUnitMode hm u n x *
        deriv (fun y => n07aReferenceUnitAtom D T S C L K m .principalA y * deriv φ y) x) =
      ∫ x, ((2 * (n : ℝ)) ^ 2 * n07aReferenceUnitC D T S C L K m x *
        n07aCanonicalUnitMode hm u n x +
          (K.right m - K.left m) ^ 2 * n07aCanonicalUnitMode hm G n x) * φ x := by
  intro φ hφ hc hs
  have h := n07a_interval_equation_unit hm
    (fun r => (K.coefficients (C.referenceState, 0) m).a (r, 0))
    (fun r => (2 * (n : ℝ)) ^ 2 * (K.coefficients (C.referenceState, 0) m).c (r, 0))
    (n07aHalfRadialCoefficient u n) (n07aHalfRadialCoefficient G n)
    (n07a_reference_canonical_mode_equation hJ hP hm heq n) φ hφ hc hs
  have hA : (fun y => (K.coefficients (C.referenceState, 0) m).a
      (n07aIntervalUnitMap (K.left m) (K.right m) y, 0) * deriv φ y) =
      fun y => n07aReferenceUnitAtom D T S C L K m .principalA y * deriv φ y := by
    funext y
    rw [n07aReferenceUnitAtom_A_map]
  rw [hA] at h
  have hsflux : tsupport (fun x => deriv
      (fun y => n07aReferenceUnitAtom D T S C L K m .principalA y * deriv φ y) x) ⊆
      Ioo (0 : ℝ) 1 :=
    tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hs))
  calc
    _ = _ := n07a_interval_compact_pairing_congr (n07aCanonicalUnitMode_ae hm u n) hsflux
    _ = _ := h
    _ = _ := n07a_interval_compact_pairing_congr (by
      filter_upwards [n07aCanonicalUnitMode_ae hm u n, n07aCanonicalUnitMode_ae hm G n]
        with x hu hG
      rw [hu, hG, n07aReferenceUnitC_map]
      ring) hs

end ContinuousFlexibility.Analysis
