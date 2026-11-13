import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceTraceSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryUniformSeminorm

/-!
# One common sector for the actual source trace seminorm bounds

The two sampled prefixes select the low order before all future orders.
A single smaller sector then supplies the uniform angular seminorm
bounds used by the actual controlled-transport factory.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04PositiveGeometry_sourceAngleTrace_uniform_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ larger : ℕ, low ≤ larger →
      ∀ η : ℝ, η ≤ ε → η ≤ 1 / 2 →
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side),
      ∀ j : ℕ, j ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S larger η η ×ˢ univ)
        (n04PositiveGeometry_sourceAngleTrace W X i side j), ∀ b : ℕ,
      UniformScalarJetSeminormBounds (smoothDirections_angularStateSlice Q b) := by
  let zeroData := n04PositiveGeometry_sourceAngleTrace_zero_sample_prefix
    W X hb hε hεW hflow
  let positiveData := n04PositiveGeometry_sourceProjectedTrace_sample_prefix
    W X hb hε hεW hεone hflow
  let low : ℕ := max zeroData.choose positiveData.choose
  have hzlow : zeroData.choose ≤ low := le_max_left _ _
  have hplow : positiveData.choose ≤ low := le_max_right _ _
  have hblow : base ≤ low := zeroData.choose_spec.1.trans hzlow
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  refine ⟨low, hblow, ?_⟩
  intro larger hlarge η hη hηhalf i side m hm hctx j hj4 Q b
  let V := sectorNeighborhood W.S larger η η
  have hV : IsOpen V := sectorNeighborhood_isOpen W.S larger η η
  have hVU : V ⊆ sectorNeighborhood W.S base ε ε :=
    sectorNeighborhood_mono W.S (hblow.trans hlarge) hη hη
  have hunit (l : ℕ) (hl : l ≤ low) (z : StateDirections W.S × ℝ) (hz : z ∈ V) :
      p l z ≤ 1 := by
    apply (hp (hl.trans hlarge) z).trans
    have he : p larger z = sectorGrading W.S larger z.1 + |z.2| :=
      pairGrading_apply (sectorGrading W.S) realGrading larger z
    rw [he]
    linarith only [hz.1, hz.2, hηhalf]
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  by_cases hj : j = 0
  · subst j
    let J := n04PositiveGeometry_sourceAngleTrace_zero_joint W X hb hεW i side
    apply n04PositiveGeometry_boundaryPrefix_uniformSeminormBounds p
      (sectorPairGrading_continuous W.S) hp J zeroData.choose H hH ?_
      hV hVU (hunit _ hzlow) Q b
    intro K
    let prefixData := zeroData.choose_spec.2 K
    refine ⟨prefixData.choose, fun s => ?_⟩
    let orderData := prefixData.choose_spec s
    refine ⟨orderData.choose * E ^ orderData.choose,
      mul_nonneg (zero_le_one.trans orderData.choose_spec.1)
        (Real.rpow_nonneg (zero_le_one.trans hE) _), ?_⟩
    intro z hz hzlow θ R hR hzR
    exact orderData.choose_spec.2 i side J z hz hzlow θ R hR hzR
  · let J := n04PositiveGeometry_sourceAngleTrace_joint hb hε hεW hεone hflow
      i side m hm hctx j hj4
    have he (y : (StateDirections W.S × ℝ) × ℝ) :
        radialBoundaryJet (fun q => (ContinuousLinearMap.snd ℝ ℝ ℝ)
          (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
            (liftSectorParameter W.S W.C y.1) q)) (n04PositiveEndpoint i side) j y.2 =
          n04PositiveGeometry_sourceAngleTrace W X i side j y := by
      simp only [n04PositiveGeometry_sourceAngleTrace, if_neg hj, sub_zero,
        ContinuousLinearMap.snd_apply]
    let JP := J.congr (fun y _ => (he y).symm)
    apply n04PositiveGeometry_boundaryPrefix_uniformSeminormBounds p
      (sectorPairGrading_continuous W.S) hp J positiveData.choose H hH ?_
      hV hVU (hunit _ hplow) Q b
    intro K
    let prefixData := positiveData.choose_spec.2 K
    refine ⟨prefixData.choose, fun s => ?_⟩
    let orderData := prefixData.choose_spec s
    refine ⟨orderData.choose * E ^ orderData.choose,
      mul_nonneg (zero_le_one.trans orderData.choose_spec.1)
        (Real.rpow_nonneg (zero_le_one.trans hE) _), ?_⟩
    intro z hz hzlow θ R hR hzR
    have h := orderData.choose_spec.2 i side m hm hctx j (by omega) hj4
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      JP z hz hzlow θ R hR hzR
    exact h.congr hz (fun y _ => he y)

end ContinuousFlexibility.Analysis
