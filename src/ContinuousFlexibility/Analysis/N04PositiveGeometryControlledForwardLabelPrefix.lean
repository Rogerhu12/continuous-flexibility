import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledForwardLabelDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledLabelPrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelSample

/-!
# Fixed-base normalized prefixes of the actual forward-root slope

The low parameter order is selected before the parameter prefix. Five
intrinsic angular derivatives are included at that fixed low order; a
finite parameter prefix changes only its high-order shift. The resulting
bounds apply to every genuine tower of the literal forward-label slope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

local instance n04ControlledForwardLabelPrefixStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The full forward-label displacement, with five intrinsic angular
orders absorbed at a single low base before all parameter prefixes. -/
theorem n04PositiveGeometry_rootForwardDefect_fixedBase_prefix_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ b : ℕ, b ≤ u + 5 →
        ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
          iteratedDeriv b (fun α =>
            n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low x ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ j, pairGrading (sectorGrading S) realGrading low (v j) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R →
          pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) x ≤ R →
          (∀ j, pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
          |J.D k x v| ≤ A * T.H (T.sample m) ^ (3 / 4 : ℝ) *
            R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  exact n04PositiveGeometry_labelDefect_prefix_of_oneHigh
    (pairGrading (sectorGrading S) realGrading) (sectorPairGrading_monotone S)
    (hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading))
    (sectorNeighborhood S base ε ε)
    (fun b side m θ x => iteratedDeriv b (fun α => n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _)
    base 5 (n04PositiveGeometry_rootForwardDefect_fixedBase_oneHigh_of_flow hT hS hN hflow)

/-- The literal forward slope has the same fixed low base. Its zeroth
parameter order includes the reference slope; every positive parameter
order retains the complete circle sample height factor. -/
theorem n04PositiveGeometry_rootForwardDerivative_fixedBase_prefix_of_flow
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ 4 → ∀ u : ℕ, u ≤ s →
        ∀ side : Bool, ∀ m : ℕ, ∀ θ : ℝ,
        ∀ J : SmoothDirections (sectorNeighborhood S base ε ε) (fun x =>
          iteratedDeriv (u + d)
            (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ),
        ∀ x ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low x ≤ 1 →
        ∀ v : Fin k → (StateDirections S × ℝ),
          (∀ j, pairGrading (sectorGrading S) realGrading low (v j) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R →
          pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) x ≤ R →
          (∀ j, pairGrading (sectorGrading S) realGrading (low + s + shift * K + 1) (v j) ≤ R) →
          |J.D k x v| ≤ A * parameterHeightWeight (T.H (T.sample m) ^ (3 / 4 : ℝ)) k *
            R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  refine (materialHeight_E0_weight_bounded hT
    (by norm_num : (0 : ℝ) < 3 / 4) 0).elim ?_
  intro RH hRHData
  have hRH := hRHData.1
  have hheight := hRHData.2
  have hHbound (m : ℕ) : T.H (T.sample m) ^ (3 / 4 : ℝ) ≤ RH := by
    simpa only [Real.rpow_zero, mul_one] using
      hheight _ (materialSample_mem_interval hN.1.1 hT m)
  exact n04PositiveGeometry_labelSlope_prefix_of_defect
    (pairGrading (sectorGrading S) realGrading) (sectorNeighborhood S base ε ε)
    (fun b side m θ x => iteratedDeriv b (fun α => n01RootLabel S C (liftSectorParameter S C x) m side α - α) θ)
    (fun b side m θ x => iteratedDeriv b (deriv (n01RootLabel S C (liftSectorParameter S C x) m side)) θ)
    (fun m => T.H (T.sample m) ^ (3 / 4 : ℝ))
    (fun m => Real.rpow_nonneg ((material_circle_sample_weights_pos hT hN.1.1).2 m).le _)
    base 4 hRH hHbound
    (n04PositiveGeometry_rootForwardDefect_angularDirections hT hS hN)
    (fun side m b θ x hx => n04PositiveGeometry_rootForwardDerivative_angular_eq
      hT hS hN hx side m b θ)
    (n04PositiveGeometry_rootForwardDefect_fixedBase_prefix_of_flow hT hS hN hflow)

/-- N01 chooses one common neighborhood before all parameter orders.
Both actual stored-root slopes then satisfy the normalized finite intrinsic
prefix at the supplied positive midpoint sample, with its full `3/4`
height gain at every positive parameter order. -/
theorem n04PositiveGeometry_rootForwardDerivative_fixedBase_samplePrefix
    (W : N04RealizationStart) (X : N04RealizationChoice W) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      W.base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ W.ε ∧
      ∃ low : ℕ, newBase ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
        ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
          ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ 4 → ∀ u : ℕ, u ≤ s →
          ∀ i side m, (X.src i side).val = some m → ∀ θ : ℝ,
          ∀ J : SmoothDirections (sectorNeighborhood W.S newBase ε' ε') (fun x =>
            iteratedDeriv (u + d)
              (deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m (!side))) θ),
          ∀ x ∈ sectorNeighborhood W.S newBase ε' ε',
            pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
          ∀ v : Fin k → (StateDirections W.S × ℝ),
            (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
          ∀ R : ℝ, 1 ≤ R →
            pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
            (∀ j, pairGrading (sectorGrading W.S) realGrading
              (low + s + shift * K + 1) (v j) ≤ R) →
            |J.D k x v| ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
              parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
              R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  refine (exists_ordinaryFlowJacobianBounds_of_n01 W.hT W.through03.1.1).elim ?_
  intro newBase hbaseData
  refine hbaseData.elim ?_
  intro ε' hneighborhood
  have hb := hneighborhood.1
  have hε := hneighborhood.2.1
  have hεW := hneighborhood.2.2.1
  have hflow := hneighborhood.2.2.2
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine (n04PositiveGeometry_rootForwardDerivative_fixedBase_prefix_of_flow
    W.hT W.hS hN hflow).elim ?_
  intro low hlowData
  have hlow := hlowData.1
  have hprefix := hlowData.2
  refine ⟨newBase, ε', hb, hε, hεW, low, hlow, fun K => ?_⟩
  refine (hprefix K).elim ?_
  intro shift hshift
  refine ⟨shift, fun s => ?_⟩
  refine (hshift s).elim ?_
  intro A hAData
  have hA := hAData.1
  have hbound := hAData.2
  refine (n04PositiveGeometry_positiveSource_circle_parameter_weight W X (3 / 4 : ℝ)
    (A := 0) (C := A) (by norm_num) (zero_le_one.trans hA)).elim ?_
  intro B hBData
  have hB := hBData.1
  have hsample := hBData.2
  refine ⟨B, hB, ?_⟩
  intro k hk d hd u hu i side m hm θ J x hx hxlow v hvlow R hR hxR hvR
  have hj := hbound k hk d hd u hu (!side) m θ J x hx hxlow v hvlow R hR hxR hvR
  have hcost : A * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
      B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k := by
    simpa only [Real.rpow_zero, mul_one] using hsample i side m hm k
  exact hj.trans (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
