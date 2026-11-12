import ContinuousFlexibility.Analysis.N06PrimitivePositiveModeEnergy
import ContinuousFlexibility.Analysis.N07aCanonicalRadialCoefficients
import ContinuousFlexibility.Analysis.N06WeakModeRegularity
import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# Actual H2 modal representatives on the original positive intervals

The two true normal weak derivatives supplied by the original N05 graph
give H2 representatives of its actual cosine coefficients.  This step
uses the constant leading coefficient only to identify a second weak
derivative; no unit interval, smooth source, or new graph bound is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial CanonicalGeometry
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem n06_interval_second_weak_regular {l r : ℝ} (hlr : l < r)
    {u d g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo l r)))
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hd : HasIntervalWeakDerivative l r u d)
    (hdd : HasIntervalWeakDerivative l r d g) :
    ∃ v : ℝ → ℝ, u =ᵐ[volume.restrict (Ioo l r)] v ∧
      ContDiff ℝ 1 v ∧ AbsolutelyContinuousOnInterval (deriv v) l r ∧
      MemLp v 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv v) 2 (volume.restrict (Ioo l r)) ∧
      MemLp (deriv (deriv v)) 2 (volume.restrict (Ioo l r)) := by
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo l r →
      (∫ x in l..r, u x * deriv (fun y => (1 : ℝ) * deriv φ y) x) =
        ∫ x in l..r, g x * φ x := by
    intro φ hφ hc hs
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hds := tsupport_deriv_subset.trans hs
    have h₁ := hd (deriv φ) hφd hc.deriv hds
    have h₂ := hdd φ hφ hc hs
    have he₁ : (∫ x in Ioo l r, u x * deriv (deriv φ) x) =
        ∫ x, u x * deriv (deriv φ) x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport
        (fun hh => hx ((tsupport_deriv_subset.trans hds) hh)), mul_zero]
    have he₂ : (∫ x in Ioo l r, g x * φ x) = ∫ x, g x * φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)), mul_zero]
    simp only [one_mul]
    rw [intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo, he₁, he₂]
    linarith only [h₁, h₂]
  obtain ⟨v, huv, hv, hvAC, hv₂, hvd₂, hvdd₂, _⟩ :=
    n06_weak_divergence_L2_regular hlr (a := fun _ => 1) contDiff_const
      (fun _ _ => one_ne_zero) hu hg hweak
  exact ⟨v, huv, hv, hvAC, hv₂, hvd₂, hvdd₂⟩

/-- One coherent family of representatives of the original cosine modes.
All differentiability is deduced from the two actual weak normal fields. -/
theorem N06PrimitivePositiveJets.modes_regular
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U : CanonicalL2 S K m} (P : N06PrimitivePositiveJets U)
    (hlen : K.left m < K.right m) :
    ∃ v : ℕ → ℝ → ℝ, ∀ i,
      n06HalfCosineCoefficient U i =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i ∧
      ContDiff ℝ 1 (v i) ∧
      AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m) ∧
      MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv (v i)) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (K.left m) (K.right m))) := by
  have hex (i : ℕ) := n06_interval_second_weak_regular hlen
    (n07aCanonicalRadialCoefficient_memLp U i)
    (n07aCanonicalRadialCoefficient_memLp P.secondRadial i)
    (n07a_canonical_firstNormal_coefficient P.radial_weak i)
    (n07a_canonical_firstNormal_coefficient P.secondRadial_weak i)
  choose v hv using hex
  refine ⟨v, fun i => ⟨?_, (hv i).2⟩⟩
  have heq : n06HalfCosineCoefficient (U : PolarPoint → ℝ) i =
      n07aHalfRadialCoefficient (U : PolarPoint → ℝ) i := by
    funext r
    rfl
  rw [heq]
  exact (hv i).1

/-- The same original N05 graph supplies the representatives on every
positive piece, with its original interval and source projection. -/
theorem n06N05_primitive_positive_modes_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (href : ReferenceJets D T S C L K) (hprincipal : ReferencePrincipal T S C K)
    (u : B.Space) (m : ℕ) (hm : K.positive m = true) :
    ∃ v : ℕ → ℝ → ℝ, ∀ i,
      n06HalfCosineCoefficient (u.val.1.1 m) i
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i ∧
      ContDiff ℝ 1 (v i) ∧
      AbsolutelyContinuousOnInterval (deriv (v i)) (K.left m) (K.right m) ∧
      MemLp (v i) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv (v i)) 2 (volume.restrict (Ioo (K.left m) (K.right m))) ∧
      MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (K.left m) (K.right m))) := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have hinverse : B.inverse u.val.2 = u := h.2.2.2.2.2.2.2.2.2.1 u
  obtain ⟨P⟩ := n06_primitiveReferenceInverse_positiveJets_nonempty hS h.1.1.1.1
    h.1.1.2 h04 h.2 href hprincipal u.val.2 m hm
  have hv := P.modes_regular (h04.1.referenceBounds m).2.1
  simpa only [n07aReferenceInverseField, hinverse] using hv

end ContinuousFlexibility.Analysis
