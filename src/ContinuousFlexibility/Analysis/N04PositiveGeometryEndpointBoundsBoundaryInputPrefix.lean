import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsBoundaryInputs

/-!
# One fixed low base for all nine actual root inputs

The physical coefficients have a fixed spatial loss. The actual forward
label has a loss for each finite parameter prefix. A single low base is
selected before that prefix, and their budgets then agree exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04BoundaryInputPrefixStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_rootBoundaryInput_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
      ∀ ρ : ℝ, 0 < ρ →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) ρ →
      ∀ j : Fin 9, ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ d : ℕ, d ≤ 4 →
      ∀ θ : ℝ, ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => iteratedDeriv (u + d)
          (fun η => n04PositiveGeometry_rootBoundaryInput W.D W.S W.C g m (!side) j
            (z, η)) θ),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ l, pairGrading (sectorGrading W.S) realGrading low (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      (∀ l, pairGrading (sectorGrading W.S) realGrading
        (low + s + shift * K + 1) (v l) ≤ R) →
      ‖J.D k z v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  obtain ⟨Bβ, hBβ, hβ⟩ :=
    n04PositiveGeometry_rootForwardDerivative_fixedBase_prefix_of_flow W.hT W.hS hN hflow
  obtain ⟨Bc, Lc, hBc, hc⟩ := n04PositiveGeometry_rootRawCoefficient_sample_prefix
    W X hb hε hεW hεone 7 Bβ
  let low := max Bc Lc
  have hBlow : Bβ ≤ low := hBc.trans (le_max_left _ _)
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨low, hBβ.trans hBlow, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hβ K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨Aβ, hAβ, hβbound⟩ := hshift s
  obtain ⟨Dβ, hDβ, hβsample⟩ :=
    n04PositiveGeometry_positiveSource_circle_parameter_weight W X (3 / 4 : ℝ)
      (A := 0) (C := Aβ) (by norm_num) (zero_le_one.trans hAβ)
  obtain ⟨Dc, hDc, hcBound⟩ := hc K (s + shift * K)
  let A := max Dc Dβ
  have hA : 1 ≤ A := hDc.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro i side m hm g hg hg0 hfactor ρ hρ hstrip j k hk u hu d hd θ J z hz hzlow v hv R hR hzR hvR
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let P : ℝ := R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hcost {D : ℝ} (hD : D ≤ A) : D * E ^ D ≤ A * E ^ A :=
    mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le hE hD)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hhighc : s + shift * K + Lc ≤ low + s + shift * K + 1 := by
    have : Lc ≤ low := le_max_right _ _
    omega
  have hhighβ : Bβ + s + shift * K + 1 ≤ low + s + shift * K + 1 := by omega
  have hpower : R ^ ((u : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) ≤ P := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show u ≤ u + shift * k by omega)
  have hcoeff (speed : Bool) (a : ℕ) (ha : a ≤ 3)
      (Q : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun y => iteratedDeriv (u + d) (radialBoundaryJet
          (n04PositiveGeometry_rootRawCoefficient W.D W.S W.C g
            (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) speed
            (liftSectorParameter W.S W.C y)) 0 a) θ)) :
      ‖Q.D k z v‖ ≤ A * E ^ A * parameterHeightWeight H k * P := by
    have hraw := hcBound i side m hm g hg hg0 hfactor ρ hρ hstrip speed a d
      (by omega) u (by omega) θ Q k hk z hz
      ((hp (le_max_left Bc Lc) z).trans hzlow) v
      (fun l => (hp (le_max_left Bc Lc) (v l)).trans (hv l)) R hR
      ((hp hhighc z).trans hzR) (fun l => (hp hhighc (v l)).trans (hvR l))
    exact hraw.trans ((mul_le_mul_of_nonneg_left hpower
      (mul_nonneg (mul_nonneg (zero_le_one.trans hDc)
        (Real.rpow_nonneg (zero_le_one.trans hE) _)) (parameterHeightWeight_nonneg hH k))).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcost (le_max_left Dc Dβ))
          (parameterHeightWeight_nonneg hH k)) hP))
  have hlabel (Q : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun y => iteratedDeriv (u + d)
        (deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y) m (!side))) θ)) :
      ‖Q.D k z v‖ ≤ A * E ^ A * parameterHeightWeight H k * P := by
    have hraw := hβbound k hk d (by omega) u hu (!side) m θ Q z hz
      ((hp hBlow z).trans hzlow) v (fun l => (hp hBlow (v l)).trans (hv l)) R hR
      ((hp hhighβ z).trans hzR) (fun l => (hp hhighβ (v l)).trans (hvR l))
    have hsample : Aβ * parameterHeightWeight (W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) k ≤
        Dβ * E ^ Dβ * parameterHeightWeight H k := by
      simpa only [Real.rpow_zero, mul_one] using hβsample i side m hm k
    rw [Real.norm_eq_abs]
    exact hraw.trans ((mul_le_mul_of_nonneg_right hsample hP).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcost (le_max_right Dc Dβ))
          (parameterHeightWeight_nonneg hH k)) hP))
  fin_cases j
  · exact hcoeff false 0 (by decide) J
  · exact hcoeff false 1 (by decide) J
  · exact hcoeff false 2 (by decide) J
  · exact hcoeff false 3 (by decide) J
  · exact hcoeff true 0 (by decide) J
  · exact hcoeff true 1 (by decide) J
  · exact hcoeff true 2 (by decide) J
  · exact hcoeff true 3 (by decide) J
  · exact hlabel J

end ContinuousFlexibility.Analysis
