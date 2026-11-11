import ContinuousFlexibility.Analysis.SectorParameterGeometry
import ContinuousFlexibility.Analysis.N01FlowAngularSmoothness

/-!
# The actual N01 flow tower in sector coordinates

Affine restriction keeps both the genuine directional derivatives and
the precise one-high-factor weight. Angular jets of the same actual
flow are continuous up to the closed radial endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01SectorFlowTowerStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01SectorFlowTowerParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := Prod.instSMul
local instance n01SectorFlowTowerRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

private theorem sector_drop_zero_power_factor {a b c : ℝ}
    (h : c ^ (0 : ℕ) * a ≤ b) : a ≤ b := by
  simpa only [pow_zero, one_mul] using h

theorem N01Properties.sectorFlow_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  obtain ⟨B, hB, hdata⟩ := hN.2.2.2.2.2.2.2.2.2.2.2.2 k s
  have hpoint : ∀ (m b : ℕ) (θ r : ℝ), b ≤ s → r ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
    intro m b θ r hb hr
    obtain ⟨J, hJ⟩ := hdata m 0 b (r, θ) (by simpa only [zero_add] using hb) hr
    have hmap : MapsTo (fun z : StateDirections S × ℝ =>
        (C.referenceState, 0) + sectorParameterInclusion S z)
        (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
      intro z hz
      exact Eq.mp
        (congrArg (fun u : AnnularState S × ℝ => u ∈ stateNeighborhood S C base ε)
          (liftSectorParameter_eq_affine S C z))
        (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    let K : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)) :=
      (J.compAffine (sectorParameterInclusion S) (C.referenceState, 0)
      (sectorNeighborhood_isOpen S base ε ε) hmap).congrOn
      (fun z hz => congrArg (ordinaryFlowFamily S C m 0 b (r, θ))
        (liftSectorParameter_eq_affine S C z).symm)
    refine ⟨K, ?_⟩
    intro z hz v
    have hraw := hJ (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (fun i => sectorParameterInclusion S (v i))
    have heq : K.D k z v = J.D k (liftSectorParameter S C z)
        (fun i => sectorParameterInclusion S (v i)) :=
      congrArg (fun y => J.D k y (fun i => sectorParameterInclusion S (v i)))
        (liftSectorParameter_eq_affine S C z).symm
    have hb' := (sector_drop_zero_power_factor hraw).trans_eq
      (congrArg (fun W : ℝ => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B * W)
        (oneHighVariationWeight_sector_lift S C base (s + loss) z v))
    exact (congrArg abs heq).trans_le hb'
  exact Exists.intro B (And.intro hB hpoint)

theorem N01Properties.reference_mem_stateNeighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) :
    (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
  constructor
  · change stateGrading S base (C.referenceState - C.referenceState) < ε
    have hz : stateGrading S base (C.referenceState - C.referenceState) = 0 :=
      (congrArg (fun u : AnnularState S => stateGrading S base u)
        (sub_self C.referenceState)).trans (stateGrading S base).map_zero'
    exact hz.trans_lt hN.2.1
  · simpa only [abs_zero] using hN.2.1

theorem N01Properties.ordinaryFlowFamily_radial_continuousOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m b : ℕ) (θ : ℝ) :
    ContinuousOn (fun r => ordinaryFlowFamily S C m 0 b (r, θ) z)
      (Icc (C.left m) (C.right m)) := by
  have href : referenceStateConditions D S C := hN.2.2.1
  have hz0 := hN.reference_mem_stateNeighborhood
  have hc := (hN.minusFlow_angular_iteratedDeriv_continuousOn hS hT hz hsector m b).sub
    (hN.minusFlow_angular_iteratedDeriv_continuousOn hS hT hz0 href.stateSector m b)
  have hcr := hc.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun r hr => ⟨hr, mem_univ θ⟩)
  apply hcr.congr
  intro r hr
  simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero]
  exact iteratedDeriv_fun_sub
    (((hN.minusFlow_angular_contDiff hS hT hz hsector m hr).of_le
      (show (b : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
    (((hN.minusFlow_angular_contDiff hS hT hz0 href.stateSector m hr).of_le
      (show (b : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)

end ContinuousFlexibility.Statements
