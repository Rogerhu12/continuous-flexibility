import ContinuousFlexibility.Analysis.N04RealizationSelectedRootFactorJets

/-!
# Genuine towers for the retained root drift and speed traces

The supplied factors may be chosen independently at each state by the
actual matched-collar construction. Their positive-side physical
identities determine the same boundary traces. The original state-angle
domain is retained; no smooth dependence of that choice is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The actual retained drift and speed traces inherit genuine parameter
and angular towers from the original physical fields. -/
def n04Realization_selectedRootFactorTrace_jointDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε r σ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hε : ε ≤ 1) (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (hsign : σ * deriv (deriv D.w) r < 0)
    (d c : (AnnularState S × ℝ) → PolarPoint → ℝ)
    (hfactors : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∃ ρ : ℝ, 0 < ρ ∧ ContDiff ℝ ∞ (d z) ∧ ContDiff ℝ ∞ (c z) ∧
        (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
          Real.sqrt x * c z (x, θ) =
            n04bCharacteristicHalfGap (L.coefficients z) (rootProfileShift r σ (x, θ))) ∧
        (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
          d z (x, θ) =
            σ * n04bCharacteristicDrift (L.coefficients z) (rootProfileShift r σ (x, θ))))
    (n : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ =>
        radialBoundaryJet (d (liftSectorParameter S C z.1)) 0 n z.2) ×
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ =>
        radialBoundaryJet (c (liftSectorParameter S C z.1)) 0 n z.2) := by
  let hmodel := n04Realization_exists_selectedRootFactor_trace_model
    hT hS h03 hr hroot hsign
  let g : ℝ → ℝ := hmodel.choose
  have hg : ContDiff ℝ ∞ g := hmodel.choose_spec.1
  have hg0 : 0 < g 0 := hmodel.choose_spec.2.1
  have hN : N01Properties D T S C base loss ε := h03.1.1
  have heq (z : (StateDirections S × ℝ) × ℝ)
      (hz : z ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ)) :
      radialBoundaryJet (d (liftSectorParameter S C z.1)) 0 n z.2 =
        radialBoundaryJet (orientedCharacteristicDrift
          (stateProfile D S C (liftSectorParameter S C z.1).1)
          (stateHeight D S C (liftSectorParameter S C z.1)) r σ) 0 n z.2 ∧
      radialBoundaryJet (c (liftSectorParameter S C z.1)) 0 n z.2 =
        radialBoundaryJet (factoredCharacteristicSpeed D.w g
          (stateProfile D S C (liftSectorParameter S C z.1).1)
          (stateHeight D S C (liftSectorParameter S C z.1)) r σ) 0 n z.2 := by
    have hz' := liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl
    have hs := hN.2.2.1.liftSectorParameter_sector z.1
    obtain ⟨ρ, hρ, hd, hc, hgap, hdrift⟩ :=
      hfactors (liftSectorParameter S C z.1) hz' hs
    exact hmodel.choose_spec.2.2 (liftSectorParameter S C z.1) hz' hs
      ρ _ _ hρ hd hc hgap hdrift n z.2
  let Jd := n04Realization_orientedRootFieldTrace_joint hT hS hN hε hr hroot σ
    (σ • ContinuousLinearMap.fst ℝ ℝ ℝ) n
  let Jc := n04Realization_factoredRootSpeedTrace_joint
    hT hS hN hε hr hroot σ g hg hg0 n
  refine ⟨Jd.congr (fun z hz => ?_), Jc.congr (fun z hz => (heq z hz).2.symm)⟩
  simpa only [orientedCharacteristicDrift, n06PhysicalRootFields, smul_apply,
    smul_eq_mul, ContinuousLinearMap.fst_apply] using (heq z hz).1.symm

end ContinuousFlexibility.Analysis
