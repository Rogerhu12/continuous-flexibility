module

public import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Componentwise source compatibility of the actual residual error

Every negative component has smooth actual fluxes and zero radial flux
on both end collars. Rectangle conservation gives zero source integral
on that component. The components are pairwise disjoint, and the actual
differential error vanishes on their complement. Countable additivity
then gives the physical source-kernel identity without any hypothesis
about smooth extension of the fluxes at the annulus endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A function supported on disjoint open intervals and having zero
integral on each one has zero integral on the encompassing interval.
This statement uses the standard totalized Bochner integral. -/
theorem intervalIntegral_eq_zero_of_disjoint_components
    {a b : ℝ} (hab : a ≤ b) (l h : ℕ → ℝ)
    (hinside : ∀ m, a < l m ∧ l m < h m ∧ h m < b)
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (l m) (h m)) (Ioo (l n) (h n)))
    (f : ℝ → ℝ)
    (hzero : ∀ r ∈ Ioo a b, (¬ ∃ m, r ∈ Ioo (l m) (h m)) → f r = 0)
    (hcomponent : ∀ m, (∫ r in l m..h m, f r) = 0) :
    (∫ r in a..b, f r) = 0 := by
  have hsub : (⋃ m, Ioo (l m) (h m)) ⊆ Ioo a b := by
    intro r hr
    obtain ⟨m, hm⟩ := mem_iUnion.mp hr
    exact ⟨(hinside m).1.trans hm.1, hm.2.trans (hinside m).2.2⟩
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
    (fun r hr => hzero r hr.1 (fun hm => hr.2 (mem_iUnion.mpr hm)))]
  by_cases hf : IntegrableOn f (⋃ m, Ioo (l m) (h m)) volume
  · rw [integral_iUnion (fun _ => measurableSet_Ioo) hdisj hf]
    have heach (m : ℕ) : (∫ r in Ioo (l m) (h m), f r) = 0 := by
      simpa only [intervalIntegral.integral_of_le (hinside m).2.1.le,
        integral_Ioc_eq_integral_Ioo] using hcomponent m
    simp only [heach, tsum_zero]
  · exact integral_undef hf

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section ActualCompatibility

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (hdisc : ∀ m p, p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
      ((C.left m + 2 * C.right m) / 3) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hS hT hz hsector hdisc

theorem N01Properties.returnCorrectionResidualErrorField_componentIntegral_eq_zero
    (ρ : CircleSpace S) (η : HeightPair S) (m : ℕ) :
    (∫ r in C.left m..C.right m, angularMean (fun θ =>
      returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η (r, θ))) = 0 := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  let F := returnCorrectionRadialErrorFlux D S C R (returnCorrectionCutoffs C) z ρ η
  let G := returnCorrectionAngularErrorFlux D S C R (returnCorrectionCutoffs C) z ρ η
  have hcore (r : ℝ) (hr : r ∈ uIcc (C.left m) (C.right m)) (θ : ℝ) :
      (r, θ) ∈ annularOpen D := by
    rw [uIcc_of_le (hC.1 m).2.1.le] at hr
    exact ⟨⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩, mem_univ _⟩
  have hF : ∀ p ∈ uIcc (C.left m) (C.right m) ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 F p := by
    intro p hp
    exact (hN01.returnCorrectionErrorFluxes_contDiffAt_one hS hT R hz hsector hdisc
      ρ η p (hcore p.1 hp.1 p.2)).1
  have hG : ∀ p ∈ uIcc (C.left m) (C.right m) ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 G p := by
    intro p hp
    exact (hN01.returnCorrectionErrorFluxes_contDiffAt_one hS hT R hz hsector hdisc
      ρ η p (hcore p.1 hp.1 p.2)).2
  have hperiod : ∀ r ∈ uIcc (C.left m) (C.right m), G (r, Real.pi) = G (r, 0) := by
    intro r _
    simpa only [G, Prod.mk_add_mk, add_zero, zero_add] using
      (hN01.returnCorrectionErrorFluxes_periodic hS R (returnCorrectionCutoffs C)
        hz hsector (fun n s _ => returnCorrectionCutoff_mem_Icc _ _ s) ρ η).2 (r, 0)
  have hrootzero (r : ℝ) (hr : r ∈ Ioo D.a D.b) (hr0 : deriv D.w r = 0) (θ : ℝ) :
      F (r, θ) = 0 := by
    have heq := (hN01.returnCorrectionCoefficientError_eventually_zero_of_nonnegative
      R z (r, θ) ⟨hr, mem_univ _⟩ (by rw [hr0])).eq_of_nhds
    simp only [F, returnCorrectionRadialErrorFlux, heq, LinearMap.zero_apply,
      Prod.fst_zero, zero_mul]
  have hboundary : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      F (C.right m, θ) = F (C.left m, θ) := by
    intro θ _
    rw [hrootzero (C.right m)
      ⟨(hC.1 m).1.trans (hC.1 m).2.1, (hC.1 m).2.2⟩ (hC.2.1 m).2.1 θ,
      hrootzero (C.left m)
        ⟨(hC.1 m).1, (hC.1 m).2.1.trans (hC.1 m).2.2⟩ (hC.2.1 m).1 θ]
  let α : PlaneOneForm := ⟨fun p => -G p, F⟩
  have h := integral_exteriorCoefficient_eq_zero (α := α)
    (fun p hp => (hG p hp).neg) hF
    (fun r hr => congrArg Neg.neg (hperiod r hr)) hboundary
  change (∫ r in C.left m..C.right m, ∫ θ in (0 : ℝ)..Real.pi,
    radialPartial F (r, θ) - angularPartial (fun p => -G p) (r, θ)) = 0 at h
  simp only [angularPartial_neg_total, sub_neg_eq_add] at h
  calc
    (∫ r in C.left m..C.right m, angularMean (fun θ =>
        returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η (r, θ))) =
      ∫ r in C.left m..C.right m, (1 / Real.pi) *
        ∫ θ in (0 : ℝ)..Real.pi, radialPartial F (r, θ) + angularPartial G (r, θ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      apply congrArg ((1 / Real.pi) * ·)
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [returnCorrectionResidualErrorField, if_pos (hcore r hr θ)]
      rfl
    _ = (1 / Real.pi) * ∫ r in C.left m..C.right m, ∫ θ in (0 : ℝ)..Real.pi,
        radialPartial F (r, θ) + angularPartial G (r, θ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by rw [h, mul_zero]

/-- The actual error satisfies the physical source compatibility
identity. No flux-regularity or annulus-endpoint extension premise remains. -/
theorem N01Properties.returnCorrectionResidualErrorField_sourceIntegral_eq_zero_of_collar
    (ρ : CircleSpace S) (η : HeightPair S) :
    physicalSourceIntegral D
      (returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η) = 0 := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hab : D.a ≤ D.b := ((hC.1 0).1.trans ((hC.1 0).2.1.trans (hC.1 0).2.2)).le
  apply intervalIntegral_eq_zero_of_disjoint_components hab C.left C.right hC.1 hC.2.2.1
  · intro r hr hout
    have hzero (θ : ℝ) :=
      hN01.returnCorrectionResidualErrorField_eq_zero_of_outside_components
        R z ρ η (r, θ) ⟨hr, mem_univ _⟩ hout
    simp only [angularMean, hzero, intervalIntegral.integral_zero, mul_zero]
  · exact hN01.returnCorrectionResidualErrorField_componentIntegral_eq_zero
      hS hT R hz hsector hdisc ρ η

end ActualCompatibility

end ContinuousFlexibility.Statements
