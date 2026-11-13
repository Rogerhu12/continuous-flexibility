import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceTraceSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryBudget

/-!
# One sampled prefix for all actual angular source traces

The displacement at order zero and the four positive radial traces use
one low order and one later shift. Only their angular horizons change;
the actual traces, sample and height factor are retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04PositiveGeometry_sourceAngleTrace_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ j : ℕ, j ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceAngleTrace W X i side j),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds Q K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  let zeroData := n04PositiveGeometry_sourceAngleTrace_zero_sample_prefix W X hb hε hεW hflow
  let positiveData := n04PositiveGeometry_sourceProjectedTrace_sample_prefix
    W X hb hε hεW hεone hflow
  let low := max zeroData.choose positiveData.choose
  have hzl : zeroData.choose ≤ low := le_max_left _ _
  have hpl : positiveData.choose ≤ low := le_max_right _ _
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨low, zeroData.choose_spec.1.trans hzl, fun K => ?_⟩
  let zeroPrefix := zeroData.choose_spec.2 K
  let positivePrefix := positiveData.choose_spec.2 K
  let cz := zeroPrefix.choose
  let cp := positivePrefix.choose
  let shift := max cz cp
  have hcz : cz ≤ shift := le_max_left _ _
  have hcp : cp ≤ shift := le_max_right _ _
  refine ⟨shift, fun s => ?_⟩
  let zeroOrder := zeroPrefix.choose_spec (s + (shift - cz) * K)
  let positiveOrder := positivePrefix.choose_spec (s + (shift - cp) * K)
  let A := max zeroOrder.choose positiveOrder.choose
  have hzA : zeroOrder.choose ≤ A := le_max_left _ _
  have hpA : positiveOrder.choose ≤ A := le_max_right _ _
  have hA : 1 ≤ A := zeroOrder.choose_spec.1.trans hzA
  refine ⟨A, hA, ?_⟩
  intro i side m hm hctx j hj4 Q z hz hzlow θ R hR hzR
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := A * E ^ A
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans hA)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hhigh (l c : ℕ) (hl : l ≤ low) (hc : c ≤ shift) :
      l + (s + (shift - c) * K) + c * K + 1 ≤ low + s + shift * K + 1 := by
    have he := n04PositiveGeometry_prefix_horizon s K c shift hc
    omega
  have hpower (c : ℕ) (hc : c ≤ shift) :
      R ^ (1 / ((((s + (shift - c) * K) + c * K : ℕ) : ℝ) + 1)) = t :=
    congrArg (fun q : ℕ => R ^ (1 / ((q : ℝ) + 1)))
      (n04PositiveGeometry_prefix_horizon s K c shift hc)
  have hcost {B : ℝ} (hBA : B ≤ A) : B * E ^ B ≤ M :=
    mul_le_mul hBA (Real.rpow_le_rpow_of_exponent_le hE hBA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  by_cases hj : j = 0
  · subst j
    have h := zeroOrder.choose_spec.2 i side Q z hz ((hp hzl z).trans hzlow) θ R hR
      ((hp (hhigh _ _ hzl hcz) z).trans hzR)
    exact h.mono_budget le_rfl (Nat.le_add_right _ _)
      (fun v hv => ⟨(hp hzl v).trans hv.1,
        (hp (hhigh _ _ hzl hcz) v).trans hv.2⟩) hM hH ht (hcost hzA) (hpower cz hcz) hcz
  · have he (y : (StateDirections W.S × ℝ) × ℝ) :
        radialBoundaryJet (fun q => (ContinuousLinearMap.snd ℝ ℝ ℝ)
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
            (liftSectorParameter W.S W.C y.1) q)) (n04PositiveEndpoint i side) j y.2 =
          n04PositiveGeometry_sourceAngleTrace W X i side j y := by
      simp only [n04PositiveGeometry_sourceAngleTrace, if_neg hj, sub_zero,
        ContinuousLinearMap.coe_snd']
    let JP := Q.congr (fun y _ => (he y).symm)
    have h := positiveOrder.choose_spec.2 i side m hm hctx j (by omega) hj4
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      JP z hz ((hp hpl z).trans hzlow) θ R hR
      ((hp (hhigh _ _ hpl hcp) z).trans hzR)
    have h' : N04BoundaryWordBounds Q K (s + (shift - cp) * K) 1 z θ
        (fun v => p positiveData.choose v ≤ 1 ∧
          p (positiveData.choose + (s + (shift - cp) * K) + cp * K + 1) v ≤ R)
        (positiveOrder.choose * E ^ positiveOrder.choose) H
        (R ^ (1 / ((((s + (shift - cp) * K) + cp * K : ℕ) : ℝ) + 1))) cp :=
      h.congr hz (fun y _ => he y)
    exact h'.mono_budget le_rfl (Nat.le_add_right _ _)
      (fun v hv => ⟨(hp hpl v).trans hv.1,
        (hp (hhigh _ _ hpl hcp) v).trans hv.2⟩) hM hH ht (hcost hpA) (hpower cp hcp) hcp

end ContinuousFlexibility.Analysis
