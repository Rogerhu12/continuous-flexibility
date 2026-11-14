module

public import ContinuousFlexibility.Analysis.N04NegativeHeightIdentity
public import ContinuousFlexibility.Analysis.NegativeHeightMaterialJets
public import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# The actual negative height inherits the determinant-ratio estimates

The height identity holds on the actual open physical half, hence as a
whole smooth germ at every interior point. All ordinary height jets are
therefore those of the genuine determinant ratio. The fixed low order
and loss come entirely from the previously proved scalar estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private def InteriorHeightGeometry
    (P : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (U : Set PolarPoint) : Prop :=
  ∀ q ∈ U, ContDiffAt ℝ ∞ (fun y => (F y).1) q ∧
    h =ᶠ[𝓝 q] (fun y => ((F y).1 / (P.b y ^ 2 - P.a y * P.c y)) ^ (1 / 4 : ℝ))

private theorem n03_cutPair_heightGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) :
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m : ℕ, ∀ side : Bool,
      InteriorHeightGeometry (L.coefficients z)
        (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1))
        (K.height z (if side then (K.cutPair m).2 else (K.cutPair m).1))
        (physicalPieceOpen S K z (if side then (K.cutPair m).2 else (K.cutPair m).1)) := by
  intro z hz hs m side q hq
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hF : ContDiffAt ℝ ∞ (K.chart z i) q :=
    ((hA.boundary z hz hs i).2.2.2.2.1 q (subset_closure hq)).1
  refine ⟨hF.fst, ?_⟩
  filter_upwards [(hA.domains z hz hs i).1.mem_nhds hq] with y hy
  exact (negativeCutPair_height_eq_fourthRoot hS hT hN hL hA hB hz hs m side y hy).2

private theorem interiorHeight_fixed_loss_of_family
    {E Z : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) (shift : Z → E) (states : Set Z) (sector : Z → Prop)
    (P : Z → SymmetricCoefficients) (F : Z → ℕ → Bool → PolarPoint → PolarPoint)
    (h : Z → ℕ → Bool → PolarPoint → ℝ) (U : Z → ℕ → Bool → Set PolarPoint)
    (hgeometry : ∀ z ∈ states, sector z → ∀ m : ℕ, ∀ side : Bool,
      InteriorHeightGeometry (P z) (F z m side) (h z m side) (U z m side)) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u κ : ℝ, 0 < l → l ≤ u → 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ states, sector z → p low (shift z) ≤ 1 → ∀ m : ℕ, ∀ side : Bool,
      ∀ q ∈ U z m side,
        (F z m side q).1 ∈ Icc l u →
        κ ≤ (P z).b q ^ 2 - (P z).a q * (P z).c q →
        (∀ j : Fin 3, ContDiffAt ℝ ∞ (canonicalCoefficientComponent j (P z)) q ∧
          PointwiseMaterialJetBound p inputLoss A (shift z)
            (canonicalCoefficientComponent j (P z)) q) →
        PointwiseMaterialJetBound p inputLoss A (shift z) (fun y => (F z m side y).1) q →
        PointwiseMaterialJetBound p outLoss B (shift z) (h z m side) q := by
  obtain ⟨low, outLoss, hbound⟩ :=
    negativeHeight_from_coefficients_fixed_loss (E := E) (p := p) hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hApos l u κ hl hlu hκ
  obtain ⟨B, hBpos, hjet⟩ := hbound A hApos l u κ hl hlu hκ
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs hlow m side q hq hvalue hgap hcoeff hξjet
  have ha := hcoeff 0
  have hb := hcoeff 1
  have hc := hcoeff 2
  simp [canonicalCoefficientComponent] at ha hb hc
  rcases hgeometry z hz hs m side q hq with ⟨hF, he⟩
  have hformula := hjet (shift z) hlow (P z) (fun y => (F z m side y).1) q
    ha.1 hb.1 hc.1 hF hvalue hgap ha.2 hb.2 hc.2 hξjet
  intro n
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
  exact hformula.2 n

theorem n03_cutPair_height_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u κ : ℝ, 0 < l → l ≤ u → 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m : ℕ, ∀ side : Bool,
      let i := if side then (K.cutPair m).2 else (K.cutPair m).1
      ∀ q ∈ physicalPieceOpen S K z i,
        (K.chart z i q).1 ∈ Icc l u →
        κ ≤ (L.coefficients z).b q ^ 2 - (L.coefficients z).a q * (L.coefficients z).c q →
        (∀ j : Fin 3,
          ContDiffAt ℝ ∞ (canonicalCoefficientComponent j (L.coefficients z)) q ∧
          PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) inputLoss A
            (z - (C.referenceState, 0)) (canonicalCoefficientComponent j (L.coefficients z)) q) →
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) inputLoss A
          (z - (C.referenceState, 0)) (fun y => (K.chart z i y).1) q →
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) outLoss B
          (z - (C.referenceState, 0)) (K.height z i) q := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation p := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  exact interiorHeight_fixed_loss_of_family
    (E := AnnularState S × ℝ) (Z := AnnularState S × ℝ) (p := p) hp hI inputLoss
    (fun z => z - (C.referenceState, 0)) (stateNeighborhood S C base ε)
    (fun z => stateSector S z.1) L.coefficients
    (fun z m side => K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (fun z m side => K.height z (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (fun z m side => physicalPieceOpen S K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1))
    (n03_cutPair_heightGeometry hS hT hN hL hA hB)

end ContinuousFlexibility.Analysis
