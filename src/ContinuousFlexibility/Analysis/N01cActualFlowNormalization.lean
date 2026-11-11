import ContinuousFlexibility.Analysis.N01cActualFlowUnitDirections
import ContinuousFlexibility.Analysis.N01cFlowNormalizationProperty
import ContinuousFlexibility.Analysis.N01cWeightAbsorption

/-!
# Normalizing the genuine angular flow variation

A raw polynomial bound on actual finite plots is first transported to
the original tuple of directions and physical radius. Interpolation
then acts once on the genuine continuous multilinear derivative.
The low base is fixed, and only the additive high loss depends on the
parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private theorem n01c_normalization_at_compact_preimage
    {path : ℝ → ℝ} {r : ℝ} {Result : Prop}
    (hpreimage : ∃ t ∈ Icc (0 : ℝ) 1, path t = r)
    (close : ∀ t ∈ Icc (0 : ℝ) 1, path t = r → Result) : Result := by
  obtain ⟨t, ht, htr⟩ := hpreimage
  exact close t ht htr

private theorem n01c_normalization_unit_value_transport
    {value actual material high low high' low' : ℝ} {degree : ℕ}
    (hvalue : value = actual) (hhigh : high = high') (hlow : low = low')
    (hbound : |value| ≤ material * high * low ^ degree) :
    ‖actual‖ ≤ material * high' * low' ^ degree := by
  rw [hvalue, hhigh, hlow] at hbound
  simpa only [Real.norm_eq_abs] using hbound

theorem n01_ordinaryFlowAngularOrderBound_of_unitPolynomial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss normLoss n degree : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
      r ∈ Icc (C.left i) (C.right i) →
        0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hε2 : ε ≤ 1 / 2)
    (hNorm : FlowPolynomialNormalization
      (pairGrading (stateGrading S) realGrading) base normLoss)
    (hraw : ∃ offset : ℕ, ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ u : OrdinaryFlowVariationInput D S C base ε (n + 1),
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ : ℝ,
        |(u.data hS hT hA hB hpos).value t b (θ : AddCircle Real.pi)| ≤
          B * T.H (T.sample (C.cell u.component)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell u.component)) ^ B *
            u.aggregate (b + offset) * u.aggregate offset ^ degree) :
    OrdinaryFlowAngularOrderBound hS hT hA hB hpos loss (n + 1) := by
  let p := pairGrading (stateGrading S) realGrading
  let P := fun (b high : ℕ) (B : ℝ) =>
    ∀ m, ∀ J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
      (componentCosineSpeed D S C m),
    ∀ r : ℝ, ∀ hr : r ∈ Icc (C.left m) (C.right m), ∀ θ : ℝ,
    ∀ x ∈ stateNeighborhood S C base ε, ∀ v : Fin (n + 1) → (AnnularState S × ℝ),
      |(ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr b θ).D (n + 1) x v| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight p base high (x - (C.referenceState, 0)) v
  have hmono : ∀ b a a' B B', a ≤ a' → 0 < B → B ≤ B' →
      P b a B → P b a' B' := by
    intro b a a' B B' haa hBpos hBB' hb m J r hr θ x hx v
    have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
    exact (hb m J r hr θ x hx v).trans
      (n01c_materialOneHigh_mono p (jointStateGrading_monotone S) base haa
        hBpos.le hBB' (hT.2.1 _ hsample).2.1.le (hE _ hsample)
        (3 / 4 : ℝ) (x - (C.referenceState, 0)) v)
  have hpoint : ∃ d : ℕ, ∀ b : ℕ, ∃ B : ℝ, 0 < B ∧ P b (b + loss + d) B := by
    refine n01c_transform_offset_constants_map _ _
      (fun offset => (degree + 1) * offset + normLoss) hraw ?_
    intro offset b B hBpos hb
    obtain ⟨C₀, hC₀, hnormalize⟩ := hNorm (n + 1) degree offset b
    obtain ⟨B', hB', habsorb⟩ :=
      exists_sameConstant_materialWeight_bound (B * C₀) B (3 / 4 : ℝ)
    refine ⟨B', hB', ?_⟩
    intro m J r hr θ x hx v
    refine n01c_normalization_at_compact_preimage
      (exists_ordinaryFlowCompactTime_of_radius
        (D := D) (T := T) (S := S) (C := C) (r := r) hA m hr) ?_
    intro t ht htr
    let A := (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr b θ).D (n + 1) x
    let M : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B
    have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
    have hH := (hT.2.1 _ hsample).2.1.le
    have hE₀ := hE _ hsample
    have hM : 0 ≤ M := mul_nonneg
      (mul_nonneg hBpos.le (Real.rpow_nonneg hH _))
      (Real.rpow_nonneg (zero_le_one.trans hE₀) _)
    have hunit : ∀ w : Fin (n + 1) → (AnnularState S × ℝ),
        (∀ i, p base (w i) < 1) →
        ‖A w‖ ≤ M *
          ((1 + p (b + offset) (x - (C.referenceState, 0))) +
            ∑ i, p (b + offset) (w i)) *
          (((1 + p offset (x - (C.referenceState, 0))) +
            ∑ i, p offset (w i)) ^ degree) := by
      intro w hw
      let u := ordinaryFlowVariationInputOfDirections m J x hx w (fun i => (hw i).le)
      exact n01c_normalization_unit_value_transport
        (actual := A w) (material := M) (degree := degree)
        (ordinaryFlowVariationInputOfDirections_value hS hT hA hB hpos
          m J x hx w (fun i => (hw i).le) b θ t r hr htr)
        (ordinaryFlowVariationInputOfDirections_aggregate
          m J x hx w (fun i => (hw i).le) (b + offset))
        (ordinaryFlowVariationInputOfDirections_aggregate
          m J x hx w (fun i => (hw i).le) offset)
        (hb u t ht θ)
    have hn := hnormalize (x - (C.referenceState, 0))
      (jointStateGrading_displacement_lt_one hε2 hx).le A M hM hunit v
    let high : ℕ := b + (degree + 1) * offset + normLoss
    have hn' : |A v| ≤ (B * C₀) *
        T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight p base high (x - (C.referenceState, 0)) v := by
      calc
        |A v| = ‖A v‖ := (Real.norm_eq_abs _).symm
        _ ≤ M * C₀ *
            oneHighVariationWeight p base high (x - (C.referenceState, 0)) v := hn
        _ = _ := by dsimp only [M]; ring
    have hsmall := habsorb
      (T.H (T.sample (C.cell m))) (T.E0 (T.sample (C.cell m)))
      (oneHighVariationWeight p base high (x - (C.referenceState, 0)) v)
      hH hE₀ (oneHighVariationWeight_nonneg p base high _ v)
    exact (hn'.trans hsmall).trans
      (n01c_materialOneHigh_mono p (jointStateGrading_monotone S) base
        (by dsimp only [high]; omega) hB'.le le_rfl hH hE₀
        (3 / 4 : ℝ) (x - (C.referenceState, 0)) v)
  exact n01c_spatialize_offset_bounds P loss hmono hpoint

end ContinuousFlexibility.Blueprint
