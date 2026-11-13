import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredHeightJets

/-! # Sample bounds for the original complete height jets -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_storedHeightPowerJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ γ : ℝ, ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m → ∀ Kcur : CanonicalData W.S,
      N04PositiveGeometryRootContext W.D W.S W.C Kcur base ε m (!side) →
      ∀ n : ℕ, n ≤ 3 →
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedHeightPowerJet W.S W.C Kcur m (!side) γ n),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds J K s 1 z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let data := n04PositiveGeometry_rootHeightPowerTrace_sample_prefix W X hb hε hεW hεone hflow
  let low := data.choose
  refine ⟨low, data.choose_spec.1, fun γ K => ?_⟩
  let shifts := data.choose_spec.2 γ K
  let shift := shifts.choose
  refine ⟨shift, fun s => ?_⟩
  let order := shifts.choose_spec s
  let A₀ := order.choose
  have hA₀ : 1 ≤ A₀ := order.choose_spec.1
  let A := 8 * A₀
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (by norm_num) hA₀
  have hA₀A : A₀ ≤ A := le_mul_of_one_le_left (zero_le_one.trans hA₀) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro i side m hm Kcur hctx n hn J z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := A₀ * E ^ A₀
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le _
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans hA₀)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hP : (p low 0 ≤ 1 ∧ p (low + s + shift * K + 1) 0 ≤ R) :=
    ⟨((p low).map_zero').trans_le zero_le_one,
      ((p (low + s + shift * K + 1)).map_zero').trans_le (zero_le_one.trans hR)⟩
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := by
    rw [hrad]; exact (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := by
    rw [hrad]; exact (W.roots i side).2.1
  have hc := hctx.choose_spec.choose_spec.choose_spec.choose_spec
  let ρ := hctx.choose_spec.choose
  let hρ := hctx.choose_spec.choose_spec.choose
  have href := (hc.2.2.2.2 (W.C.referenceState, 0)
    (reference_mem_stateNeighborhood W.S W.C base hε) hN.2.2.1.stateSector).1
  have hstrip (y : StateDirections W.S × ℝ) (hy : y ∈ sectorNeighborhood W.S base ε ε) :=
    (hc.2.2.2.2 (liftSectorParameter W.S W.C y)
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy le_rfl)
      (hN.2.2.1.liftSectorParameter_sector y)).1
  have hbound := n04PositiveGeometry_storedHeightPowerJet_word_bound W.hT W.hS hN hεone
    hflow hctx hr hroot γ n hn J hz hP hM hH (Real.one_le_rpow hR (by positivity))
    (fun a ha Q => order.choose_spec.2 i side m hm hctx.choose hc.1 hc.2.1 hc.2.2.1
      ρ hρ href hstrip a (ha.trans hn) Q z hz hzlow θ R hR hzR)
  apply hbound.enlarge hH (zero_le_one.trans (Real.one_le_rpow hR (by positivity)))
  have htwo : (2 : ℝ) ^ n ≤ 8 := (pow_le_pow_right₀ (by norm_num) hn).trans_eq (by norm_num)
  calc
    (2 : ℝ) ^ n * M ≤ 8 * M := mul_le_mul_of_nonneg_right htwo hM
    _ = A * E ^ A₀ := by dsimp only [A, M]; ring
    _ ≤ A * E ^ A := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE hA₀A) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
