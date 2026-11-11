import ContinuousFlexibility.Radial.InnerRadialTrace

/-!
# Fixed physical affine lifts and the full piece domain

The two affine hats are realized in the actual physical L² space.
Their canonical traces are the two coordinate vectors. Subtracting the
lift of the canonical trace defines the full first-order piece domain,
and its zero-trace part is exactly the actual zero-endpoint closure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

section AffineLift

variable (D : ReferenceData) (hw : Continuous D.w)
  {a b : ℝ} (hab : a < b) (ha : 0 < a)
  (hcore : Ioo a b ⊆ radialCore D)
  (hpos : ∀ r ∈ Icc a b, 0 < D.w r)

/-- One actual affine hat and its normalized derivative. -/
def innerRadialAffineUnitPair (i : Fin 2) : InnerRadialH1Pair D :=
  (innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (innerIntervalAffineLift a b (innerEndpointValues i))
    (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).continuous.continuousOn,
   innerRadialIntervalToLp D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (innerGapGradientField (innerIntervalAffineLift a b (innerEndpointValues i)))
    (innerGapGradientField_continuous
      (innerIntervalAffineLift_contDiff a b (innerEndpointValues i))).continuousOn)

theorem innerRadialAffineUnitPair_value_ae (i : Fin 2) :
    ((innerRadialAffineUnitPair D hw ha hcore hpos i).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D]
        (Ioo a b).indicator (innerIntervalAffineLift a b (innerEndpointValues i)) := by
  exact innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (innerIntervalAffineLift a b (innerEndpointValues i))
    (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).continuous.continuousOn

theorem innerRadialAffineUnitPair_gradient_ae (i : Fin 2) :
    ((innerRadialAffineUnitPair D hw ha hcore hpos i).2 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D]
        (Ioo a b).indicator
          (innerGapGradientField (innerIntervalAffineLift a b (innerEndpointValues i))) := by
  exact innerRadialIntervalToLp_ae D hw ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
    (innerGapGradientField (innerIntervalAffineLift a b (innerEndpointValues i)))
    (innerGapGradientField_continuous
      (innerIntervalAffineLift_contDiff a b (innerEndpointValues i))).continuousOn

theorem innerRadialAffineUnitPair_trace (i : Fin 2) :
    innerRadialH1Trace D hw ha hcore hpos
      (innerRadialAffineUnitPair D hw ha hcore hpos i) = innerEndpointValues i := by
  funext k
  rw [innerRadialH1Trace_smooth D hw hab ha hcore hpos
    (fun _ _ => (innerIntervalAffineLift_contDiff a b (innerEndpointValues i)).contDiffAt)
    (innerRadialAffineUnitPair_value_ae D hw ha hcore hpos i)
    (innerRadialAffineUnitPair_gradient_ae D hw ha hcore hpos i)]
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  by_cases hk : k = 0
  · subst k
    simpa only [if_pos rfl] using hends.1
  · have hk1 : k = 1 := by omega
    subst k
    simpa only [show (1 : Fin 2) ≠ 0 by decide, if_false] using hends.2

/-- The fixed linear affine lift of both endpoint values. -/
def innerRadialAffineLift : (Fin 2 → ℝ) →ₗ[ℝ] InnerRadialH1Pair D where
  toFun z := z 0 • innerRadialAffineUnitPair D hw ha hcore hpos 0 +
    z 1 • innerRadialAffineUnitPair D hw ha hcore hpos 1
  map_add' z w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]

@[simp] theorem innerRadialAffineLift_apply (z : Fin 2 → ℝ) :
    innerRadialAffineLift D hw ha hcore hpos z =
      z 0 • innerRadialAffineUnitPair D hw ha hcore hpos 0 +
        z 1 • innerRadialAffineUnitPair D hw ha hcore hpos 1 := rfl

/-- The lift has exactly the prescribed canonical endpoint values. -/
theorem innerRadialH1Trace_affineLift (z : Fin 2 → ℝ) :
    innerRadialH1Trace D hw ha hcore hpos
      (innerRadialAffineLift D hw ha hcore hpos z) = z := by
  rw [innerRadialAffineLift_apply, map_add, map_smul, map_smul,
    innerRadialAffineUnitPair_trace D hw hab ha hcore hpos 0,
    innerRadialAffineUnitPair_trace D hw hab ha hcore hpos 1]
  funext i
  by_cases hi : i = 0
  · subst i
    norm_num [innerEndpointValues]
  · have hi1 : i = 1 := by omega
    subst i
    norm_num [innerEndpointValues]

/-- The full physical piece domain. The boundary values are recovered
from the field/gradient pair, rather than supplied as extra data. -/
def innerRadialH1Domain : Submodule ℝ (InnerRadialH1Pair D) :=
  (innerRadialH1Zero D a b).toSubmodule.comap
    (LinearMap.id -
      (innerRadialAffineLift D hw ha hcore hpos).comp
        (innerRadialH1Trace D hw ha hcore hpos))

theorem mem_innerRadialH1Domain (q : InnerRadialH1Pair D) :
    q ∈ innerRadialH1Domain D hw ha hcore hpos ↔
      q - innerRadialAffineLift D hw ha hcore hpos
        (innerRadialH1Trace D hw ha hcore hpos q) ∈ innerRadialH1Zero D a b := Iff.rfl

theorem innerRadialH1Zero_mem_domain {q : InnerRadialH1Pair D}
    (hq : q ∈ innerRadialH1Zero D a b) :
    q ∈ innerRadialH1Domain D hw ha hcore hpos := by
  apply (mem_innerRadialH1Domain D hw ha hcore hpos q).mpr
  rw [innerRadialH1Trace_zero D hw hab ha hcore hpos hq, map_zero, sub_zero]
  exact hq

theorem innerRadialAffineLift_mem_domain (z : Fin 2 → ℝ) :
    innerRadialAffineLift D hw ha hcore hpos z ∈
      innerRadialH1Domain D hw ha hcore hpos := by
  apply (mem_innerRadialH1Domain D hw ha hcore hpos _).mpr
  rw [innerRadialH1Trace_affineLift D hw hab ha hcore hpos, sub_self]
  exact (innerRadialH1Zero D a b).zero_mem

/-- A field with prescribed endpoint values is precisely a zero-endpoint
closed-domain field plus the fixed affine lift. -/
theorem innerRadialH1Domain_trace_iff (q : InnerRadialH1Pair D) (z : Fin 2 → ℝ) :
    (q ∈ innerRadialH1Domain D hw ha hcore hpos ∧
      innerRadialH1Trace D hw ha hcore hpos q = z) ↔
    q - innerRadialAffineLift D hw ha hcore hpos z ∈ innerRadialH1Zero D a b := by
  constructor
  · rintro ⟨hq, hz⟩
    simpa only [hz] using (mem_innerRadialH1Domain D hw ha hcore hpos q).mp hq
  · intro hq
    have hz := innerRadialH1Trace_zero D hw hab ha hcore hpos hq
    rw [map_sub, innerRadialH1Trace_affineLift D hw hab ha hcore hpos] at hz
    have he := sub_eq_zero.mp hz
    refine ⟨?_, he⟩
    apply (mem_innerRadialH1Domain D hw ha hcore hpos q).mpr
    simpa only [he] using hq

end AffineLift

end ContinuousFlexibility.Radial
