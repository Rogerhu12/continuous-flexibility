import ContinuousFlexibility.Analysis.N04PulledFieldsActualErrorStripGrowth
import ContinuousFlexibility.Analysis.N04PulledFieldsStripZeroPhysicalBounds
import ContinuousFlexibility.Analysis.N04PulledFieldsStripPhysicalCost

/-!
# Full physical height for the actual coefficient correction

The actual velocity and exact finite correction polynomial give strong
mixed bounds on the retained strips. Their sampled positive height is
transferred to the same physical point, and the common zero germs cover
the rest of the annulus. The result applies to every genuine mixed tower
of the actual residual-substituted error, including parameter order zero.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

local instance n04PulledFieldsActualErrorPhysicalStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)
  (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))

include hN hT hhost in
private theorem n04PulledFields_actualErrorStrip_physicalCost :
    ∀ P : ℝ, 0 ≤ P → ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧
      ∀ m (y : PolarPoint), y ∈ Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ →
        T.H (T.sample m) ^ (3 / 4 : ℝ) * radialE (D.cellIndex (Q.cell m)) ^ P ≤
          K * T.E0 y.1 ^ A * T.H y.1 ^ (3 / 4 : ℝ) := by
  intro P hP
  obtain ⟨K, A, hK, hA, hb⟩ := hN.n04PulledFields_controlSample_physicalCost hT hhost
    (by norm_num : 0 < (3 / 4 : ℝ)) hP
  refine ⟨K, A, hK.le, hA, fun m y hy => ?_⟩
  exact (hb m (Q.cell m) y.1 (Q.strip_subset m hy.1)
    (Q.component_cell m (Q.strip_subset m hy.1))).trans_eq (by ring)

include hhost in
private theorem n04PulledFields_actualErrorPhysical_of_stripGrowth
    (π : (ℝ × ℝ) →L[ℝ] ℝ)
    (RF : MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z y => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C z) y (R.residual (liftSectorParameter S C z)))))
    (hg : N04PulledFieldsFixedBaseMixedGrowth
      (pairGrading (sectorGrading S) realGrading)
      (fun m => radialE (D.cellIndex (Q.cell m)))
      (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
      (fun m => solveSmoothDirectionsPostcomp
        (n04PulledFields_actualErrorStripDirections Q hN hS hT hR m) π)) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ z, z ∈ sectorNeighborhood S base ε ε →
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ y (hy : y ∈ annularOpen D), ∀ a b : ℕ, a + b ≤ s →
      ∀ v : Fin k → StateDirections S × ℝ,
        |(RF.parameter a b y hy).D k z v| ≤
          A * T.E0 y.1 ^ P * T.H y.1 ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) B (s + L) z v := by
  refine n04PulledFields_mixedPhysical_of_strips_or_zero
    (pairGrading (sectorGrading S) realGrading)
    (sectorNeighborhood_isOpen S base ε ε)
    (fun m => Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ)
    (fun _ => isOpen_Ioo.prod isOpen_univ)
    (fun m => (sectorNeighborhood_convex S base ε ε).prod
      ((convex_Ioo (Q.stripLeft m) (Q.stripRight m)).prod convex_univ))
    (fun m => radialE (D.cellIndex (Q.cell m)))
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => one_le_radialE_of_nat (D.cellIndex (Q.cell m)))
    (fun m => Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT m)).2.1.le _)
    (fun y => T.E0 y.1) (fun y => T.H y.1 ^ (3 / 4 : ℝ))
    (fun y hy => (hT.2.1 y.1 hy.1).2.2.1.le)
    (fun y hy => Real.rpow_nonneg (hT.2.1 y.1 hy.1).2.1.le _)
    (n04PulledFields_actualErrorStrip_physicalCost Q hN hT hhost)
    RF (fun m => solveSmoothDirectionsPostcomp
      (n04PulledFields_actualErrorStripDirections Q hN hS hT hR m) π) ?_ hg
  intro y hy
  rcases hN.cutoffStrip_or_eventually_zero Q.cutoff Q.support_interior
    Q.endpoint_germs Q.stripLeft Q.stripRight Q.strip_support hy.1 with ⟨m, hm⟩ | hz
  · exact Or.inl ⟨m, hm, mem_univ _⟩
  · exact Or.inr (fun z _ => n04PulledFields_error_zero_germ R Q.cutoff hz
      (liftSectorParameter S C z) (R.residual (liftSectorParameter S C z)) π)

include hN hS hT hR hhost in
/-- Each actual correction coefficient has a physical full-height
bound with one common low base before all parameter orders. The high
loss depends on the parameter order and precedes every spatial order.
The mixed tower is arbitrary but must differentiate the actual error. -/
theorem n04PulledFields_actualError_physicalOneHigh
    (i : Fin 3)
    (RF : MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z y => n04PulledFields_errorProjection i
        (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C z) y (R.residual (liftSectorParameter S C z))))) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ z, z ∈ sectorNeighborhood S base ε ε →
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ y (hy : y ∈ annularOpen D), ∀ a b : ℕ, a + b ≤ s →
      ∀ v : Fin k → StateDirections S × ℝ,
        |(RF.parameter a b y hy).D k z v| ≤
          A * T.E0 y.1 ^ P * T.H y.1 ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) B (s + L) z v := by
  fin_cases i
  · refine ⟨0, fun k => ⟨0, fun s => ⟨0, 0, le_rfl, le_rfl,
      fun z hz _ y hy a b _ v => ?_⟩⟩⟩
    have hzero : (RF.parameter a b y hy).D k z v = 0 := by
      apply (RF.parameter a b y hy).jets_zero_of_eqOn_zero _ k z hz v
      intro x hx
      simp only [n04PulledFields_errorProjection, if_pos rfl, ContinuousLinearMap.zero_apply,
        mixedDerivative, iteratedDeriv_const, ite_self]
    simp only [hzero, abs_zero, zero_mul, le_refl]
  · apply n04PulledFields_actualErrorPhysical_of_stripGrowth Q hN hS hT hR hhost
      (n04PulledFields_errorProjection 1) RF
    have hg := (n04PulledFields_actualErrorStrip_fixedBaseMixedGrowth Q hN hS hT hR
      (n04PulledFields_actualErrorStripDirections Q hN hS hT hR)).1
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    simpa only [n04PulledFields_errorProjection, h10, if_false, if_pos rfl] using hg
  · apply n04PulledFields_actualErrorPhysical_of_stripGrowth Q hN hS hT hR hhost
      (n04PulledFields_errorProjection 2) RF
    have hg := (n04PulledFields_actualErrorStrip_fixedBaseMixedGrowth Q hN hS hT hR
      (n04PulledFields_actualErrorStripDirections Q hN hS hT hR)).2
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simpa only [n04PulledFields_errorProjection, h20, h21, if_false] using hg

end ContinuousFlexibility.Analysis
