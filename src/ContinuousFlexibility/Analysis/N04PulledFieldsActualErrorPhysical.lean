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

private theorem n04PulledFields_errorProjection_zero_eq :
    n04PulledFields_errorProjection 0 = (0 : (ℝ × ℝ) →L[ℝ] ℝ) := by
  simp [n04PulledFields_errorProjection]

private theorem n04PulledFields_errorProjection_one_eq :
    n04PulledFields_errorProjection 1 = ContinuousLinearMap.fst ℝ ℝ ℝ := by
  simp [n04PulledFields_errorProjection]

private theorem n04PulledFields_errorProjection_two_eq :
    n04PulledFields_errorProjection 2 = ContinuousLinearMap.snd ℝ ℝ ℝ := by
  simp [n04PulledFields_errorProjection]

/-- The zero entry is handled at the level of an arbitrary genuine mixed
tower, before specializing its parameter space or its pair-valued field. -/
private theorem n04PulledFields_zeroErrorProjection_physicalOneHigh
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {Ω : Set PolarPoint} (p : ℕ → Seminorm ℝ E)
    (Ephys Hphys : PolarPoint → ℝ) (f : E → PolarPoint → ℝ × ℝ)
    (RF : MixedJetRegularity U Ω (fun z y => n04PulledFields_errorProjection 0 (f z y))) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ z, z ∈ U → p B z ≤ 1 →
      ∀ y (hy : y ∈ Ω), ∀ a b : ℕ, a + b ≤ s → ∀ v : Fin k → E,
        |(RF.parameter a b y hy).D k z v| ≤
          A * Ephys y ^ P * Hphys y * oneHighVariationWeight p B (s + L) z v := by
  refine ⟨0, fun k => ⟨0, fun s => ⟨0, 0, le_rfl, le_rfl,
    fun z hz _ y hy a b _ v => ?_⟩⟩⟩
  have hzero : (RF.parameter a b y hy).D k z v = 0 := by
    apply (RF.parameter a b y hy).jets_zero_of_eqOn_zero _ k z hz v
    intro x hx
    simp only [n04PulledFields_errorProjection_zero_eq, ContinuousLinearMap.zero_apply,
      mixedDerivative, iteratedDeriv_const, ite_self]
  simp only [hzero, abs_zero, zero_mul, le_refl]

/-- Convert the radial alternative to a spatial cover before inserting
any concrete state space or coefficient formula. -/
private theorem n04PulledFields_stripOrZero_of_radialCover
    {I E : Type*} (U : Set E) (Ω : Set PolarPoint) (l h : I → ℝ)
    (Z : PolarPoint → Prop) (f : E → PolarPoint → ℝ)
    (hcover : ∀ y ∈ Ω, (∃ i, y.1 ∈ Ioo (l i) (h i)) ∨ Z y)
    (hzero : ∀ y, Z y → ∀ x ∈ U, f x =ᶠ[𝓝 y] fun _ => 0) :
    ∀ y ∈ Ω, (∃ i, y ∈ Ioo (l i) (h i) ×ˢ (univ : Set ℝ)) ∨
      ∀ x ∈ U, f x =ᶠ[𝓝 y] fun _ => 0 := by
  intro y hy
  rcases hcover y hy with ⟨i, hi⟩ | hz
  · exact Or.inl ⟨i, hi, mem_univ _⟩
  · exact Or.inr (hzero y hz)

/-- Projection cases and their dependent mixed towers are handled for
an abstract pair-valued field. No actual tower is unfolded by the case split. -/
private theorem n04PulledFields_pairError_physicalOneHigh
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) {U : Set E} {Ω : Set PolarPoint}
    (hU : IsOpen U) (V : I → Set PolarPoint) (hV : ∀ m, IsOpen (V m))
    (hc : ∀ m, Convex ℝ (U ×ˢ V m))
    (W F : I → ℝ) (hW : ∀ m, 1 ≤ W m) (hF : ∀ m, 0 ≤ F m)
    (Ephys Hphys : PolarPoint → ℝ)
    (hE : ∀ y ∈ Ω, 0 ≤ Ephys y) (hH : ∀ y ∈ Ω, 0 ≤ Hphys y)
    (hcost : ∀ Q : ℝ, 0 ≤ Q → ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧
      ∀ m y, y ∈ V m → F m * W m ^ Q ≤ K * Ephys y ^ A * Hphys y)
    {f : E → PolarPoint → ℝ × ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ V m) (fun x => f x.1 x.2))
    (hcover : ∀ π : (ℝ × ℝ) →L[ℝ] ℝ, ∀ y ∈ Ω,
      (∃ m, y ∈ V m) ∨ ∀ x ∈ U, (fun q => π (f x q)) =ᶠ[𝓝 y] fun _ => 0)
    (hg : N04PulledFieldsFixedBaseMixedGrowth p W F
        (fun m => solveSmoothDirectionsPostcomp (J m) (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∧
      N04PulledFieldsFixedBaseMixedGrowth p W F
        (fun m => solveSmoothDirectionsPostcomp (J m) (ContinuousLinearMap.snd ℝ ℝ ℝ)))
    (i : Fin 3)
    (RF : MixedJetRegularity U Ω (fun z y => n04PulledFields_errorProjection i (f z y))) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ A P : ℝ,
      0 ≤ A ∧ 0 ≤ P ∧ ∀ z, z ∈ U → p B z ≤ 1 →
      ∀ y (hy : y ∈ Ω), ∀ a b : ℕ, a + b ≤ s → ∀ v : Fin k → E,
        |(RF.parameter a b y hy).D k z v| ≤
          A * Ephys y ^ P * Hphys y * oneHighVariationWeight p B (s + L) z v := by
  fin_cases i
  · exact n04PulledFields_zeroErrorProjection_physicalOneHigh p Ephys Hphys f RF
  · apply n04PulledFields_mixedPhysical_of_strips_or_zero
      p hU V hV hc W F hW hF Ephys Hphys hE hH hcost RF
      (fun m => solveSmoothDirectionsPostcomp (J m) (n04PulledFields_errorProjection 1))
      (hcover (n04PulledFields_errorProjection 1))
    rw [n04PulledFields_errorProjection_one_eq]
    exact hg.1
  · apply n04PulledFields_mixedPhysical_of_strips_or_zero
      p hU V hV hc W F hW hF Ephys Hphys hE hH hcost RF
      (fun m => solveSmoothDirectionsPostcomp (J m) (n04PulledFields_errorProjection 2))
      (hcover (n04PulledFields_errorProjection 2))
    rw [n04PulledFields_errorProjection_two_eq]
    exact hg.2

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

include hN in
private theorem n04PulledFields_actualError_stripOrZero
    (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    ∀ y ∈ annularOpen D,
      (∃ m, y ∈ Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ (univ : Set ℝ)) ∨
      ∀ z ∈ sectorNeighborhood S base ε ε,
        (fun q => π (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C z) q (R.residual (liftSectorParameter S C z))))
            =ᶠ[𝓝 y] (fun _ => 0) := by
  exact n04PulledFields_stripOrZero_of_radialCover
    (I := ℕ) (E := StateDirections S × ℝ)
    (sectorNeighborhood S base ε ε) (annularOpen D) Q.stripLeft Q.stripRight
    (fun y => ∀ᶠ r in 𝓝 y.1, ∀ m, deriv (Q.cutoff m) r = 0)
    (fun z q => π (returnCorrectionCoefficientError D S C R Q.cutoff
      (liftSectorParameter S C z) q (R.residual (liftSectorParameter S C z))))
    (fun y hy => hN.cutoffStrip_or_eventually_zero Q.cutoff Q.support_interior
      Q.endpoint_germs Q.stripLeft Q.stripRight Q.strip_support hy.1)
    (fun y hz z _ => n04PulledFields_error_zero_germ R Q.cutoff hz
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
  exact n04PulledFields_pairError_physicalOneHigh
    (I := ℕ) (E := StateDirections S × ℝ)
    (U := sectorNeighborhood S base ε ε) (Ω := annularOpen D)
    (f := fun z y => returnCorrectionCoefficientError D S C R Q.cutoff
      (liftSectorParameter S C z) y (R.residual (liftSectorParameter S C z)))
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
    (n04PulledFields_actualErrorStripDirections Q hN hS hT hR)
    (n04PulledFields_actualError_stripOrZero Q hN)
    (n04PulledFields_actualErrorStrip_fixedBaseMixedGrowth Q hN hS hT hR
      (n04PulledFields_actualErrorStripDirections Q hN hS hT hR)) i RF

end ContinuousFlexibility.Analysis
