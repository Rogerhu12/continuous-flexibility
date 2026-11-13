import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOrientationDirections

/-!
# Inward radial orientation preserves the actual normalized prefix

The original physical trace bound is transported by the fixed inward
orientation. Its selected low base, spatial loss and material cost are
unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

local instance n04PositiveOrientationStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

theorem n04PositiveGeometry_orientedRootTrace_finiteShift_power
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ r ∈ radialCore D, deriv D.w r = 0 →
      ∀ σ : ℝ, |σ| ≤ 1 → ∀ a d : ℕ, a + d ≤ N →
      ∀ π : PolarPoint →L[ℝ] ℝ, ‖π‖ ≤ 1 → ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => iteratedDeriv (b + d) (radialBoundaryJet
          (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C z)
            (rootProfileShift r σ p))) 0 a) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections S × ℝ),
      (∀ j, pairGrading (sectorGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading S) realGrading (s + inputLoss) z ≤ R →
      (∀ j, pairGrading (sectorGrading S) realGrading (s + inputLoss) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  let data := n04PositiveGeometry_physicalRootTrace_finiteShift_power
    hT hS hN hε hE N requestedBase
  let B : ℕ := data.choose
  let inputLoss : ℕ := data.choose_spec.choose
  have hB := data.choose_spec.choose_spec.1
  have hp := data.choose_spec.choose_spec.2
  refine ⟨B, inputLoss, hB, fun K s => ?_⟩
  let orderData := hp K s
  let C0 : ℝ := orderData.choose
  let A : ℝ := orderData.choose_spec.choose
  have hC0 := orderData.choose_spec.choose_spec.1
  have hA := orderData.choose_spec.choose_spec.2.1
  have hb := orderData.choose_spec.choose_spec.2.2
  refine ⟨C0, A, hC0, hA, ?_⟩
  intro r hr hroot σ hσ a d had π hπ b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let JP : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun y : (StateDirections S × ℝ) × ℝ => radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C y.1) p)) r a y.2) :=
    n04PositiveGeometry_physicalRootTrace_joint hT hS hN hε hr hroot π a
  let JA := smoothDirections_angularStateSlice JP (b + d) θ
  have hbound := hb r hr hroot a d had π hπ b hbs θ JA k hk z hz hzlow v hv R hR hzR hvR
  have he : EqOn
      (fun y => iteratedDeriv (b + d) (radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C y)
          (rootProfileShift r σ p))) 0 a) θ)
      (fun y => σ ^ a * iteratedDeriv (b + d) (radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C y) p)) r a) θ)
      (sectorNeighborhood S base ε ε) := by
    intro y hy
    have htrace : radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C y)
          (rootProfileShift r σ p))) 0 a = fun η => σ ^ a * radialBoundaryJet
        (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C y) p)) r a η := by
      funext η
      exact n04PositiveGeometry_radialBoundaryJet_rootShift a
        (π.contDiff.contDiffAt.comp (r, η)
          (n06_physicalRootFields_contDiffAt_root hT hS hN
            (liftSectorParameter_mem_stateNeighborhood hy le_rfl)
            (hN.2.2.1.liftSectorParameter_sector y) hr hroot η))
    exact (congrArg (fun f : ℝ → ℝ => iteratedDeriv (b + d) f θ) htrace).trans
      (iteratedDeriv_const_mul_field (σ ^ a) _)
  have hσa : |σ ^ a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg σ) hσ
  have hM : 0 ≤ C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
      R ^ ((b : ℝ) / ((s : ℝ) + 1)) := (norm_nonneg _).trans hbound
  exact (n04PositiveGeometry_parameter_constMul_bound JA J (σ ^ a) he k z hz v hbound).trans
    (mul_le_of_le_one_left hM hσa)

end ContinuousFlexibility.Analysis
