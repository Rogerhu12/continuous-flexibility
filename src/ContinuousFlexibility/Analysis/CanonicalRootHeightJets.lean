module

public import ContinuousFlexibility.Analysis.CanonicalRootRelativeJets

/-!
# Jets of the actual relative root height

Both factors come from the same stored root charts. The current height
is evaluated at the genuine relative transport, whose image stays on
that same root circle. One product-composition estimate covers the
height ratio and its reciprocal without an additional inverse estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def CanonicalRootHeightJetFamily
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (side : Bool) (B : ℕ → ℝ) : Prop :=
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    ContDiffAt ℝ ∞ (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      0 < n04CoordinatesCurrentHeightRatio C K z i (r, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        loss B (z - (C.referenceState, 0))
        (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        loss B (z - (C.referenceState, 0))
        (fun y => (n04CoordinatesCurrentHeightRatio C K z i y)⁻¹) (r, θ)

private theorem relativeHeightQuotient_allJets_fixed_loss
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ f₀ f : PolarPoint → ℝ,
      ∀ g : PolarPoint → PolarPoint, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ f₀ x → ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        f₀ x ≠ 0 → f (g x) ≠ 0 →
        PointwiseMaterialJetBound p inputLoss A z f₀ x →
        PointwiseMaterialJetBound p inputLoss A z (fun y => (f₀ y)⁻¹) x →
        PointwiseMaterialJetBound p inputLoss A z f (g x) →
        PointwiseMaterialJetBound p inputLoss A z (fun y => (f y)⁻¹) (g x) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
          A n * (1 + p (n + inputLoss) z)) →
        PointwiseMaterialJetBound p loss B z (fun y => f₀ y / f (g y)) x ∧
        PointwiseMaterialJetBound p loss B z (fun y => (f₀ y / f (g y))⁻¹) x := by
  obtain ⟨base, loss, hproduct⟩ := relativeHeightProduct_allJets_fixed_loss hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro A hA
  obtain ⟨B, hB, hbnd⟩ := hproduct A hA
  refine ⟨B, hB, ?_⟩
  intro z hz f₀ f g x hf₀ hf hg hf₀0 hf0 h₀ h₀inv h hInv hgjets
  have hq : PointwiseMaterialJetBound p loss B z
      (fun y => f₀ y * (f (g y))⁻¹) x :=
    hbnd z hz f₀ (fun y => (f y)⁻¹) g x hf₀ (hf.inv hf0) hg h₀ hInv hgjets
  have hi : PointwiseMaterialJetBound p loss B z
      (fun y => (f₀ y)⁻¹ * f (g y)) x :=
    hbnd z hz (fun y => (f₀ y)⁻¹) f g x (hf₀.inv hf₀0) hf hg h₀inv h hgjets
  constructor
  · have he : (fun y => f₀ y / f (g y)) =
        (fun y => f₀ y * (f (g y))⁻¹) :=
      funext fun y => div_eq_mul_inv _ _
    exact (congrArg (fun u : PolarPoint → ℝ =>
      PointwiseMaterialJetBound p loss B z u x) he).mpr hq
  · have he : (fun y => (f₀ y / f (g y))⁻¹) =
        (fun y => (f₀ y)⁻¹ * f (g y)) := by
      funext y
      rw [inv_div, div_eq_mul_inv, mul_comm]
    exact (congrArg (fun u : PolarPoint → ℝ =>
      PointwiseMaterialJetBound p loss B z u x) he).mpr hi

private theorem canonicalRootHeightJets_at
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {K : CanonicalData S}
    {z : AnnularState S × ℝ}
    {p : ℕ → Seminorm ℝ (AnnularState S × ℝ)}
    {rootLoss relativeLoss inputLoss outLoss : ℕ} {A R Q B : ℕ → ℝ}
    (hp : Monotone p) (hA0 : ∀ n, 0 ≤ A n)
    (hAQ : ∀ n, A n ≤ Q n) (hRQ : ∀ n, R n ≤ Q n)
    (hrootLoss : rootLoss ≤ inputLoss) (hrelativeLoss : relativeLoss ≤ inputLoss)
    (m : ℕ) (side : Bool) (θ : ℝ)
    (hroot : ∀ t : ℝ, RootPhysicalFieldJetBound p rootLoss A
      (z - (C.referenceState, 0))
      (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (K.height z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (n01ComponentRoot C m side, t))
    (href : ∀ t : ℝ, RootPhysicalFieldJetBound p rootLoss A 0
      (K.chart (C.referenceState, 0) (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (K.height (C.referenceState, 0) (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (n01ComponentRoot C m side, t))
    (hτ : ContDiffAt ℝ ∞
      (canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
      (n01ComponentRoot C m side, θ))
    (hradial : (canonicalCurrentPoint C K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1)
      (n01ComponentRoot C m side, θ)).1 = n01ComponentRoot C m side)
    (hτraw : ∀ n : ℕ, 1 ≤ n →
      ‖iteratedFDeriv ℝ n
        (canonicalCurrentPoint C K z (if side then (K.cutPair m).2 else (K.cutPair m).1))
        (n01ComponentRoot C m side, θ)‖ ≤
      R n * (1 + p (n + relativeLoss) (z - (C.referenceState, 0))))
    (hbnd : ∀ f₀ f : PolarPoint → ℝ, ∀ g : PolarPoint → PolarPoint,
      ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ f₀ x → ContDiffAt ℝ ∞ f (g x) → ContDiffAt ℝ ∞ g x →
        f₀ x ≠ 0 → f (g x) ≠ 0 →
        PointwiseMaterialJetBound p inputLoss Q (z - (C.referenceState, 0)) f₀ x →
        PointwiseMaterialJetBound p inputLoss Q (z - (C.referenceState, 0))
          (fun y => (f₀ y)⁻¹) x →
        PointwiseMaterialJetBound p inputLoss Q (z - (C.referenceState, 0)) f (g x) →
        PointwiseMaterialJetBound p inputLoss Q (z - (C.referenceState, 0))
          (fun y => (f y)⁻¹) (g x) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n g x‖ ≤
          Q n * (1 + p (n + inputLoss) (z - (C.referenceState, 0)))) →
        PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
          (fun y => f₀ y / f (g y)) x ∧
        PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
          (fun y => (f₀ y / f (g y))⁻¹) x) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := n01ComponentRoot C m side
    ContDiffAt ℝ ∞ (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      0 < n04CoordinatesCurrentHeightRatio C K z i (r, θ) ∧
      PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
        (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
        (fun y => (n04CoordinatesCurrentHeightRatio C K z i y)⁻¹) (r, θ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  let τ : PolarPoint → PolarPoint := canonicalCurrentPoint C K z i
  have hy : τ (r, θ) = (r, (τ (r, θ)).2) := Prod.ext hradial rfl
  have hcurrent : RootPhysicalFieldJetBound p rootLoss A
      (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) (τ (r, θ)) := by
    have hrootCurrent : RootPhysicalFieldJetBound p rootLoss A
        (z - (C.referenceState, 0)) (K.chart z i) (K.height z i)
        (r, (τ (r, θ)).2) := hroot (τ (r, θ)).2
    exact (congrArg (fun q : PolarPoint => RootPhysicalFieldJetBound p rootLoss A
      (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) q) hy).mpr hrootCurrent
  have hreference : RootPhysicalFieldJetBound p rootLoss A
      (z - (C.referenceState, 0)) (K.chart (C.referenceState, 0) i)
      (K.height (C.referenceState, 0) i) (r, θ) :=
    RootPhysicalFieldJetBound.from_zero hA0 (href θ) _
  have hheight {f : PolarPoint → ℝ} {x : PolarPoint}
      (hf : PointwiseMaterialJetBound p rootLoss A (z - (C.referenceState, 0)) f x) :
      PointwiseMaterialJetBound p inputLoss Q (z - (C.referenceState, 0)) f x :=
    hf.mono hp hrootLoss hA0 hAQ
  have hτjets (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n τ (r, θ)‖ ≤
        Q n * (1 + p (n + inputLoss) (z - (C.referenceState, 0))) :=
    (hτraw n hn).trans (mul_le_mul (hRQ n)
      (add_le_add le_rfl (hp (Nat.add_le_add_left hrelativeLoss n) _))
      (add_nonneg zero_le_one (apply_nonneg _ _)) ((hA0 n).trans (hAQ n)))
  have hquotient :
      PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
        (fun y => K.height (C.referenceState, 0) i y / K.height z i (τ y)) (r, θ) ∧
      PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
        (fun y => (K.height (C.referenceState, 0) i y / K.height z i (τ y))⁻¹) (r, θ) :=
    hbnd (K.height (C.referenceState, 0) i) (K.height z i) τ (r, θ)
      hreference.2.1 hcurrent.2.1 hτ hreference.2.2.1.ne' hcurrent.2.2.1.ne'
      (hheight hreference.2.2.2.2.1) (hheight hreference.2.2.2.2.2)
      (hheight hcurrent.2.2.2.2.1) (hheight hcurrent.2.2.2.2.2) hτjets
  have hq : ContDiffAt ℝ ∞ (n04CoordinatesCurrentHeightRatio C K z i) (r, θ) ∧
      0 < n04CoordinatesCurrentHeightRatio C K z i (r, θ) :=
    ⟨hreference.2.1.div (hcurrent.2.1.comp (r, θ) hτ) hcurrent.2.2.1.ne',
      div_pos hreference.2.2.1 hcurrent.2.2.1⟩
  refine ⟨hq.1, hq.2, ?_, ?_⟩
  · change PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
      (fun y => K.height (C.referenceState, 0) i y / K.height z i (τ y)) (r, θ)
    exact hquotient.1
  · change PointwiseMaterialJetBound p outLoss B (z - (C.referenceState, 0))
      (fun y => (K.height (C.referenceState, 0) i y / K.height z i (τ y))⁻¹) (r, θ)
    exact hquotient.2

/-- The common neighborhood and loss precede the component. The actual
stored height and transport are unchanged throughout the construction. -/
theorem n04b_exists_common_root_heightJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ outLoss ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ side : Bool, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        CanonicalRootHeightJetFamily S C K newBase outLoss ε' m side B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨rootBase, rootLoss, ηR, hbR, _hRlow, hηR, hηRε, hroots⟩ :=
    n04b_exists_common_root_endpoint_fields hS hT hN hfield hA hB
  obtain ⟨relativeBase, relativeLoss, ηT, hbT, _hTlow, hηT, hηTε, hrelative⟩ :=
    n04b_exists_common_root_relative_positiveJets hS hT hN hfield hA hB
  let inputLoss := max rootLoss relativeLoss
  obtain ⟨low, outLoss, hproduct⟩ :=
    relativeHeightQuotient_allJets_fixed_loss hp hI inputLoss
  let newBase := max rootBase (max relativeBase (max low outLoss))
  let ε' := min (min ηR ηT) (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min (lt_min hηR hηT) (by norm_num)
  have hbaseR : rootBase ≤ newBase := le_max_left _ _
  have hbaseT : relativeBase ≤ newBase := (le_max_left _ _).trans (le_max_right _ _)
  have hbaseLow : low ≤ newBase :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbaseOut : outLoss ≤ newBase :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hε'R : ε' ≤ ηR := (min_le_left _ _).trans (min_le_left _ _)
  have hε'T : ε' ≤ ηT := (min_le_left _ _).trans (min_le_right _ _)
  have hb' : base ≤ newBase := hbR.trans hbaseR
  have hε'ε : ε' ≤ ε := hε'R.trans hηRε
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefR : (C.referenceState, 0) ∈ stateNeighborhood S C rootBase ηR :=
    reference_mem_stateNeighborhood S C rootBase hηR
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  refine ⟨newBase, outLoss, ε', hb', hbaseOut, hε', hε'ε, ?_⟩
  intro m side
  let r := n01ComponentRoot C m side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨κJ, A, _hκJ, hApos, hroot⟩ := hroots m side
  obtain ⟨R, hRpos, hrel⟩ := hrelative m side
  let Q : ℕ → ℝ := fun n => A n + R n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hApos n) (hRpos n)
  have hAQ (n : ℕ) : A n ≤ Q n := le_add_of_nonneg_right (hRpos n).le
  have hRQ (n : ℕ) : R n ≤ Q n := le_add_of_nonneg_left (hApos n).le
  obtain ⟨B, hBpos, hbnd⟩ := hproduct Q hQ
  refine ⟨B, hBpos, ?_⟩
  dsimp only [CanonicalRootHeightJetFamily]
  intro z hz hs θ
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb' hε'ε hz
  have hzR : z ∈ stateNeighborhood S C rootBase ηR :=
    stateNeighborhood_mono S C hbaseR hε'R hz
  have hzT : z ∈ stateNeighborhood S C relativeBase ηT :=
    stateNeighborhood_mono S C hbaseT hε'T hz
  have hzlow : z ∈ stateNeighborhood S C low ε' :=
    stateNeighborhood_mono S C hbaseLow le_rfl hz
  have hsmall : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hrelative := hrel z hzT hs θ
  have hcurrent (t : ℝ) : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A
      (z - (C.referenceState, 0)) (K.chart z i) (K.height z i) (r, t) :=
    (hroot z hzR hs t).2.2
  have hreference (t : ℝ) : RootPhysicalFieldJetBound
      (pairGrading (stateGrading S) realGrading) rootLoss A 0
      (K.chart (C.referenceState, 0) i) (K.height (C.referenceState, 0) i) (r, t) := by
    simpa only [sub_self] using (hroot _ hrefR hsref t).2.2
  exact canonicalRootHeightJets_at (C := C) (K := K) (z := z)
    (p := pairGrading (stateGrading S) realGrading)
    (inputLoss := inputLoss) (outLoss := outLoss) (Q := Q) (B := B)
    hp (fun n => (hApos n).le) hAQ hRQ (le_max_left _ _) (le_max_right _ _)
    m side θ hcurrent hreference hrelative.1
    (canonicalCurrentPoint_root_radial hA hB.1 href hsref hzold hs m side θ)
    hrelative.2.2.1 (hbnd (z - (C.referenceState, 0)) hsmall)

end ContinuousFlexibility.Analysis
