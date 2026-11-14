import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceWordBounds
import ContinuousFlexibility.Analysis.N04PositiveGeometryStoredInverseSamplePrefix

/-!
# Sampled full spatial jets of the original endpoint source

The reference jets admit every later parameter shift. Their finite
composition with the actual inverse jets therefore preserves the common
high denominator, the material height, and the full angular reserve.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04SourceSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

theorem n04PositiveGeometry_sourceJet_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀)
        base ε m (!side), ∀ n : ℕ, 1 ≤ n → n ≤ 4 →
      ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_sourceJet W.S W.C (X.src i side) (W.A X.e₀) n),
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
  classical
  let inverseData :=
    n04PositiveGeometry_storedInverseJet_sample_prefix W X hb hε hεW hεone hflow
  let low : ℕ := inverseData.choose
  have hlow : base ≤ low := inverseData.choose_spec.1
  let pinverse := inverseData.choose_spec.2
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let RH : ℝ := heightData.choose
  have hheight := heightData.choose_spec.2
  refine ⟨low, hlow, fun K => ?_⟩
  let shiftData := pinverse K
  let shift : ℕ := shiftData.choose
  let pshift := shiftData.choose_spec
  refine ⟨shift, fun s => ?_⟩
  let inverseBoundData := pshift s
  let Ai : ℝ := inverseBoundData.choose
  have hAi : 1 ≤ Ai := inverseBoundData.choose_spec.1
  let hinverse := inverseBoundData.choose_spec.2
  let referenceData :=
    n04PositiveGeometry_referenceForwardJet_sample_prefix W X hb hε hεW hεone hflow s
  let Ar : ℝ := referenceData.choose
  have hAr : 1 ≤ Ar := referenceData.choose_spec.1
  let hreference := referenceData.choose_spec.2
  let B := Ai + Ar + max 1 RH
  have hRHone : 1 ≤ max (1 : ℝ) RH := le_max_left _ _
  have hRHmax : RH ≤ max (1 : ℝ) RH := le_max_right _ _
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hAi, hAr, hRHone]
  have hAiB : Ai ≤ B := by dsimp only [B]; linarith only [hAr, hRHone]
  have hArB : Ar ≤ B := by dsimp only [B]; linarith only [hAi, hRHone]
  have hRHB : RH ≤ B := by dsimp only [B]; linarith only [hAi, hAr, hRHmax]
  let N := K + s + 1
  let wordData := n04PositiveGeometry_sourceJet_word_bound W X hb hε hεW hεone hflow N
  let C : ℝ := wordData.choose
  let hsource := wordData.choose_spec.2
  let degree := 5 + 2 * N
  let packData := n04PositiveGeometry_polynomial_sample_pack C B degree
  let A₀ : ℝ := packData.choose
  let hpack := packData.choose_spec.2
  let A := max 1 A₀
  have hAA : A₀ ≤ A := le_max_right _ _
  have hAone : 1 ≤ A := le_max_left _ _
  refine ⟨A, hAone, ?_⟩
  intro i side m hm hctx n hn hn4 Q z hz hzlow θ R hR hzR
  let p := pairGrading (sectorGrading W.S) realGrading
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M := B * E ^ B
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hBM : B ≤ M := le_mul_of_one_le_right (zero_le_one.trans hB)
    (Real.one_le_rpow hE (zero_le_one.trans hB))
  have hM : 1 ≤ M := hB.trans hBM
  have hHM : H ≤ M := (hheight i).2.trans (hRHB.trans hBM)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {a : ℝ} (ha : a ≤ B) : a * E ^ a ≤ M :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  have hI (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
      (JI : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_storedInverseJet W.S W.C (W.A X.e₀) m (!side) j)) :
      N04BoundaryWordBounds JI K s 1 z θ P M H t shift :=
    (hinverse i side m hm hctx j hj (hjn.trans hn4) JI
      z hz hzlow θ R hR hzR).enlarge hH (zero_le_one.trans ht) (hcost hAiB)
  have hRj (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
      (JR : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (n04PositiveGeometry_referenceForwardJet W.S W.C (W.A X.e₀) m (!side) j)) :
      N04BoundaryWordBounds JR K s 1 z θ P M H t shift :=
    (hreference i side m hm hctx j hj (hjn.trans hn4) JR
      K shift z hz θ P t ht).enlarge hH (zero_le_one.trans ht) (hcost hArB)
  have hout : N04BoundaryWordBounds Q K s 1 z θ P (C * M ^ degree) H t shift :=
    hsource i side m hm hctx n hn hn4 Q K s 1 le_rfl z hz θ P
      M H t hM hH hHM ht shift hI hRj
  apply hout.enlarge hH (zero_le_one.trans ht)
  calc
    C * M ^ degree ≤ A₀ * E ^ A₀ := hpack E hE
    _ ≤ A * E ^ A := mul_le_mul hAA (Real.rpow_le_rpow_of_exponent_le hE hAA)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hAone)

end ContinuousFlexibility.Analysis
