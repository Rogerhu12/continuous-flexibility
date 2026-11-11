import ContinuousFlexibility.Analysis.N01cNormalizedSpeedPowerBounds
import ContinuousFlexibility.Analysis.N01cEndpointSamplePowerBounds
import ContinuousFlexibility.Analysis.N01cOpticalEndpointPowerBounds

/-!
# Actual whole-speed towers and unnormalized endpoint estimates

The record keeps the genuine mixed spatial parameter towers together with
their distributed endpoint estimate. The original normalized drift,
multiplier and optical root are combined before any multilinear
normalization or reference subtraction. The state neighbourhood and all
physical component samples are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Regularity and raw bounds of the same actual component family. -/
structure EndpointPowerControl
    (p : ℕ → Seminorm ℝ X) (center : X) (base loss : ℕ)
    (U : Set X) (Ω : I → Set PolarPoint) (δ H E : I → PolarPoint → ℝ)
    (f : I → X → PolarPoint → ℝ) where
  regular : ∀ m, MixedJetRegularity U (Ω m) (f m)
  bounds : EndpointMixedPowerBounds p center base loss U Ω δ H E f

/-- The algebra is performed on abstract families, including the final
transport to an extensionally equal actual speed. -/
def endpointPowerControl_neg_add_mul
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f₀ f₁ g f : I → X → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : ∀ m, IsOpen (Ω m))
    (hδ : ∀ m q, q ∈ Ω m → 0 ≤ δ m q)
    (hE : ∀ m q, q ∈ Ω m → 1 ≤ E m q)
    {RH : ℝ} (hH : ∀ m q, q ∈ Ω m → 0 ≤ H m q ∧ H m q ≤ RH)
    (F₀ : EndpointPowerControl p center base loss U Ω δ H E f₀)
    (F₁ : EndpointPowerControl p center base loss U Ω δ H E f₁)
    (G : EndpointPowerControl p center base loss U Ω δ H E g)
    (heq : ∀ m x, x ∈ U →
      EqOn (fun q => -(f₀ m x q + f₁ m x q * g m x q)) (f m x) (Ω m)) :
    EndpointPowerControl p center base loss U Ω δ H E f := by
  let Rprod (m : I) : MixedJetRegularity U (Ω m)
      (fun x q => f₁ m x q * g m x q) :=
    (F₁.regular m).mul (G.regular m) hU (hΩ m)
  let Rsum (m : I) : MixedJetRegularity U (Ω m)
      (fun x q => f₀ m x q + f₁ m x q * g m x q) :=
    (F₀.regular m).add (Rprod m) hU (hΩ m)
  let Rneg (m : I) : MixedJetRegularity U (Ω m)
      (fun x q => -(f₀ m x q + f₁ m x q * g m x q)) :=
    (Rsum m).scalarComp (G := fun y : ℝ => -y) hU (hΩ m) isOpen_univ
    (contDiff_id.neg : ContDiff ℝ ∞ (fun y : ℝ => -y)).contDiffOn
    (fun _ _ _ _ => mem_univ _)
  let R (m : I) : MixedJetRegularity U (Ω m) (f m) :=
    (Rneg m).congr (hΩ m)
      (fun x hx => ((Rneg m).spatial x hx).congr (fun q hq => (heq m x hx q hq).symm))
      (heq m)
  have hbprod := F₁.bounds.mul G.bounds F₁.regular G.regular hΩ hδ hE hH
  have hbsum := F₀.bounds.add hbprod F₀.regular Rprod hΩ hδ
    (fun m q hq => (hH m q hq).1) hE
  exact ⟨R, (hbsum.neg Rsum).congr Rneg R hΩ heq⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

/-- The supplied whole minus speed has genuine mixed towers and the
endpoint-weighted raw estimate on exactly the given common neighbourhood. -/
def wholeCharacteristicSpeed_powerControl
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (hI : ∀ s : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ,
      pairGrading (stateGrading S) realGrading base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pairGrading (stateGrading S) realGrading (s + loss) x ≤ R →
        pairGrading (stateGrading S) realGrading (n + 4) x ≤
          B * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (G : ∀ m, MixedJetRegularity (stateNeighborhood S C base ε)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) (stateOpticalRootField D S C))
    (hG : EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
      (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m))) (fun _ => stateOpticalRootField D S C)) :
    EndpointPowerControl (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m)))
      (fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z)) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  let U := stateNeighborhood S C base ε
  let Ω : ℕ → Set PolarPoint := fun m => Ioo (C.left m) (C.right m) ×ˢ univ
  let δ : ℕ → PolarPoint → ℝ := fun m q => min (q.1 - C.left m) (C.right m - q.1)
  let H : ℕ → PolarPoint → ℝ := fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)
  let E : ℕ → PolarPoint → ℝ := fun m _ => T.E0 (T.sample (C.cell m))
  let p := pairGrading (stateGrading S) realGrading
  have hU : IsOpen U := isOpen_stateNeighborhood S C base ε
  have hΩ (m : ℕ) : IsOpen (Ω m) := isOpen_Ioo.prod isOpen_univ
  have hcore (m : ℕ) {q : PolarPoint} (hq : q ∈ Ω m) : q ∈ annularOpen D :=
    ⟨⟨(hA.2.2.1.1 m).1.trans hq.1.1, hq.1.2.trans (hA.2.2.1.1 m).2.2⟩, mem_univ _⟩
  have hs (m : ℕ) := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hδ (m : ℕ) (q : PolarPoint) (hq : q ∈ Ω m) : 0 ≤ δ m q :=
    le_min (sub_nonneg.mpr hq.1.1.le) (sub_nonneg.mpr hq.1.2.le)
  have hEs (m : ℕ) (q : PolarPoint) (_ : q ∈ Ω m) : 1 ≤ E m q := hE _ (hs m)
  let hm := materialHeight_E0_weight_bounded hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH : ℝ := Classical.choose hm
  have hRHb := (Classical.choose_spec hm).2
  have hHs (m : ℕ) (q : PolarPoint) (_ : q ∈ Ω m) : 0 ≤ H m q ∧ H m q ≤ RH := by
    refine ⟨Real.rpow_nonneg (hT.2.1 _ (hs m)).2.1.le _, ?_⟩
    simpa only [H, Real.rpow_zero, mul_one] using hRHb _ (hs m)
  let F (i : Fin 2) := normalizedSpeedFactor_controlled
    hS hT hA hε hε1 hB hE hloc hχloc hI i
  have hF (i : Fin 2) : (F i).value = normalizedSpeedFactor D S C i :=
    normalizedSpeedFactor_controlled_value hS hT hA hε hε1 hB hE hloc hχloc hI i
  let FR (i : Fin 2) (m : ℕ) : MixedJetRegularity U (Ω m) (F i).value :=
    ⟨fun z hz => ((F i).regular.spatial z hz).mono (fun q hq => hcore m hq),
      fun a b q hq => (F i).regular.parameter a b q (hcore m hq)⟩
  have FB (i : Fin 2) : EndpointMixedPowerBounds p (C.referenceState, 0) base loss U Ω δ H E
      (fun _ => (F i).value) :=
    mixedPowerBounds_to_componentSamples hT hA.1.1 hA.2.2.1 hloc hE (F i).bounds
  exact endpointPowerControl_neg_add_mul
    (X := AnnularState S × ℝ) (I := ℕ) (p := p) (center := (C.referenceState, 0))
    (base := base) (loss := loss) (U := U) (Ω := Ω) (δ := δ) (H := H) (E := E)
    (f₀ := fun _ => (F 0).value) (f₁ := fun _ => (F 1).value)
    (g := fun _ => stateOpticalRootField D S C)
    (f := fun _ z => minusCharacteristicSpeed (originalCoefficients D S C z))
    hU hΩ hδ hEs hHs ⟨FR 0, FB 0⟩ ⟨FR 1, FB 1⟩ ⟨G, hG⟩
    (fun m z hz q hq => by
      rw [hF 0, hF 1,
        minusCharacteristicSpeed_normalized_factors hS hT hA hB hz (hcore m hq)]
      dsimp only [stateOpticalRootField]
      ring)

end ContinuousFlexibility.Statements
