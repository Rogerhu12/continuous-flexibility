import ContinuousFlexibility.Radial.ReferenceOutputCosine
import ContinuousFlexibility.Radial.ReferenceCosineCoordinates

/-!
# Actual angular coefficients of reconstructed reference outputs

The left constant contributes only to index zero. The addition identity
uses integrability of the genuine products of two angular L² functions;
the radial identities then follow from the already proved reconstruction
coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem referenceCircleCosine_memLp (n : ℕ) :
    MemLp (fun θ : ℝ => referenceCircleCosine n (θ : AddCircle Real.pi))
      2 referenceAngularMeasure := by
  have hb : MemLp (referenceCircleCosine n) 2
      (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)) :=
    (memLp_congr_ae (referenceCircleCosineLp_ae n)).mp
      (Lp.memLp (referenceCircleCosineLp n))
  exact hb.comp_measurePreserving referenceCircle_measurePreserving

theorem referenceCosineCoeff_add {f g : ℝ → ℝ}
    (hf : MemLp f 2 referenceAngularMeasure)
    (hg : MemLp g 2 referenceAngularMeasure) (n : ℕ) :
    referenceCosineCoeff (fun θ => f θ + g θ) n =
      referenceCosineCoeff f n + referenceCosineCoeff g n := by
  have hfi : Integrable (fun θ : ℝ =>
      f θ * referenceCircleCosine n (θ : AddCircle Real.pi))
      referenceAngularMeasure :=
    hf.integrable_mul (referenceCircleCosine_memLp n)
  have hgi : Integrable (fun θ : ℝ =>
      g θ * referenceCircleCosine n (θ : AddCircle Real.pi))
      referenceAngularMeasure :=
    hg.integrable_mul (referenceCircleCosine_memLp n)
  unfold referenceCosineCoeff
  simp_rw [add_mul]
  exact integral_add hfi hgi

theorem referenceCosineCoeff_const (c : ℝ) (n : ℕ) :
    referenceCosineCoeff (fun _ : ℝ => c) n = if n = 0 then c else 0 := by
  cases n with
  | zero =>
    simp only [referenceCosineCoeff, referenceCircleCosine_zero, mul_one, if_pos rfl]
    simp
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n), referenceCosineCoeff_succ,
      radialAngularMean_const_mul]
    have hz : radialAngularMean (Radial.cosineMode (2 * (n + 1))) = 0 := by
      simpa only [radialAngularMean, Radial.angularAverage, one_div] using
        Radial.angularAverage_cosineMode (2 * (n + 1)) (by omega)
    rw [hz, mul_zero]

/-- Every true output coefficient is the prescribed radial mode, with
the left constant appearing exactly in index zero. -/
theorem referenceOutputCosine_coefficient_ae
    (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2)
    (n : ℕ) :
    referenceCosineCoefficient (referenceOutputCosine D γ M aL ν a).1 n
      =ᵐ[referenceRadialWeightedMeasure D γ (-M)]
        fun r => (if n = 0 then aL * D.chiLeft r else 0) + a n r := by
  filter_upwards [memLp_two_prod_sections (referenceCosineRepresentative_memLp a),
    referenceCosineCoefficient_representative_ae a n] with r hR hr
  change referenceCosineCoeff
    (fun θ => aL * D.chiLeft r + referenceCosineRepresentative a (r, θ)) n =
      (if n = 0 then aL * D.chiLeft r else 0) + a n r
  rw [referenceCosineCoeff_add (memLp_const (aL * D.chiLeft r)) hR n,
    referenceCosineCoeff_const]
  change (if n = 0 then aL * D.chiLeft r else 0) +
    referenceCosineCoefficient (referenceCosineRepresentative a) n r = _
  rw [hr]

theorem referenceOutputCosine_mean_ae
    (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2) :
    (fun r => radialAngularMean
      (fun θ => (referenceOutputCosine D γ M aL ν a).1 (r, θ)))
      =ᵐ[referenceRadialWeightedMeasure D γ (-M)]
        fun r => aL * D.chiLeft r + a 0 r := by
  filter_upwards [referenceOutputCosine_coefficient_ae D γ M aL ν a 0] with r hr
  simpa only [referenceCosineCoefficient, referenceCosineCoeff_zero, if_pos rfl,
    ite_true] using hr

theorem referenceOutputCosine_referenceMode_ae
    (D : ReferenceData) (γ M aL ν : ℝ)
    (a : lp (fun _ : ℕ => Lp ℝ 2 (referenceRadialWeightedMeasure D γ (-M))) 2)
    (n : ℕ) :
    referenceMode (referenceOutputCosine D γ M aL ν a).1 (2 * (n + 1))
      =ᵐ[referenceRadialWeightedMeasure D γ (-M)] a (n + 1) := by
  have hh := referenceOutputCosine_coefficient_ae D γ M aL ν a (n + 1)
  rw [referenceCosineCoefficient_succ_eq_referenceMode] at hh
  filter_upwards [hh] with r hr
  simpa only [if_neg (Nat.succ_ne_zero n), ite_false, zero_add] using hr

end ContinuousFlexibility.Statements
