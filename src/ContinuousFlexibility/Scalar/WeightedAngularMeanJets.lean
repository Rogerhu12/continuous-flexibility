module

public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveJets
public import ContinuousFlexibility.Scalar.WeightedStateRegularity

/-!
# The actual normalized angular-mean field and its weighted jets

Averaging always uses the prescribed interval from zero to pi and its
normalization. It commutes with the material pullback and all radial jets.
Every positive angular jet of the resulting radial field is zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def scalarAngularMeanField (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  angularMean (fun θ => f (p.1, θ))

theorem scalarAngularMeanField_contDiff {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarAngularMeanField f) :=
  (contDiff_angularMean_radial hf).comp contDiff_fst

theorem scalarAngularMeanField_contDiffOn {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    ContDiffOn ℝ ∞ (scalarAngularMeanField f) (annularOpen D) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hrad : ContDiffOn ℝ ∞
      (fun r => angularMean (fun θ => f (r, θ))) (Ioo D.a D.b) := by
    intro r hr
    exact (contDiffAt_const.mul
      (contDiffAt_intervalIntegral_parameter (f := f) (O := Ioo D.a D.b)
        isOpen_Ioo Real.pi_pos.le
        (fun q hq _ _ => hf.contDiffAt (hU.mem_nhds ⟨hq, mem_univ _⟩)) hr)).contDiffWithinAt
  exact hrad.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)

theorem scalarAngularMeanField_eq_zero_outside {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ∀ p, p ∉ annularOpen D → f p = 0) (p : PolarPoint)
    (hp : p ∉ annularOpen D) : scalarAngularMeanField f p = 0 := by
  have hz : (fun θ => f (p.1, θ)) = fun _ => (0 : ℝ) := by
    funext θ
    exact hf (p.1, θ) (fun h => hp ⟨h.1, mem_univ _⟩)
  simp only [scalarAngularMeanField, hz, angularMean, intervalIntegral.integral_zero, mul_zero]

theorem heightMember_continuous_angularSlice
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (r : ℝ) : Continuous (fun θ => f (r, θ)) := by
  by_cases hr : r ∈ Ioo D.a D.b
  · apply continuous_iff_continuousAt.mpr
    intro θ
    have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
    exact (hf.1.contDiffAt (hU.mem_nhds ⟨hr, mem_univ _⟩)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  · have hz : (fun θ => f (r, θ)) = fun _ => (0 : ℝ) :=
      funext (fun θ => hf.2.2.2.1 (r, θ) (fun h => hr h.1))
    rw [hz]
    exact continuous_const

theorem scalarAngularMeanField_add {f g : PolarPoint → ℝ}
    (hf : ∀ r, Continuous (fun θ => f (r, θ)))
    (hg : ∀ r, Continuous (fun θ => g (r, θ))) :
    scalarAngularMeanField (fun p => f p + g p) =
      fun p => scalarAngularMeanField f p + scalarAngularMeanField g p := by
  funext p
  simp only [scalarAngularMeanField, angularMean]
  rw [intervalIntegral.integral_add ((hf p.1).intervalIntegrable 0 Real.pi)
    ((hg p.1).intervalIntegrable 0 Real.pi), mul_add]

theorem scalarAngularMeanField_const_mul (c : ℝ) (f : PolarPoint → ℝ) :
    scalarAngularMeanField (fun p => c * f p) = fun p => c * scalarAngularMeanField f p := by
  funext p
  simp only [scalarAngularMeanField, angularMean, intervalIntegral.integral_const_mul]
  ring

theorem scalarAngularMeanField_idempotent (f : PolarPoint → ℝ) :
    scalarAngularMeanField (scalarAngularMeanField f) = scalarAngularMeanField f := by
  funext p
  simp only [scalarAngularMeanField, angularMean, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero] <;> ring

theorem materialPullback_scalarAngularMeanField (T : MaterialData) (γ : ℝ)
    (f : PolarPoint → ℝ) :
    materialPullback T γ (scalarAngularMeanField f) =
      scalarAngularMeanField (materialPullback T γ f) := by
  funext p
  simp only [materialPullback, scalarAngularMeanField, angularMean,
    intervalIntegral.integral_const_mul]
  ring

theorem mixedDerivative_scalarAngularMeanField_zero {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℕ) :
    mixedDerivative a 0 (scalarAngularMeanField f) =
      scalarAngularMeanField (mixedDerivative a 0 f) := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero, scalarAngularMeanField, angularMean]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_intervalIntegral_parameter hf a 0 Real.pi p.1]

theorem mixedDerivative_scalarAngularMeanField_succ (f : PolarPoint → ℝ) (a b : ℕ) :
    mixedDerivative a (b + 1) (scalarAngularMeanField f) = 0 := by
  funext p
  simp only [mixedDerivative, scalarAngularMeanField, iteratedDeriv_const,
    Nat.succ_ne_zero, ↓reduceIte, ite_self, Pi.zero_apply]

theorem weightedPhysicalJet_scalarAngularMeanField_zero
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (a c : ℕ) :
    weightedPhysicalJet T γ a 0 c (scalarAngularMeanField f) =
      scalarAngularMeanField (weightedPhysicalJet T γ a 0 c f) := by
  have hG : ContDiff ℝ ∞ (materialPullback T γ f) := contDiff_materialPullback hT hf
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularMeanField,
    mixedDerivative_scalarAngularMeanField_zero hG, scalarAngularMeanField, angularMean,
    intervalIntegral.integral_const_mul]
  ring

theorem weightedPhysicalJet_scalarAngularMeanField_succ
    (T : MaterialData) (γ : ℝ) (f : PolarPoint → ℝ) (a b c : ℕ) :
    weightedPhysicalJet T γ a (b + 1) c (scalarAngularMeanField f) = 0 := by
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularMeanField,
    mixedDerivative_scalarAngularMeanField_succ, Pi.zero_apply, mul_zero]

end ContinuousFlexibility.Statements
