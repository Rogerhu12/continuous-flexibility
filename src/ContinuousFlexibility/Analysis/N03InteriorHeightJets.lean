import ContinuousFlexibility.Analysis.N04NegativeHeightIdentity
import ContinuousFlexibility.Analysis.NegativeHeightMaterialJets
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# The actual negative height inherits the determinant-ratio estimates

The height identity holds on the actual open physical half, hence as a
whole smooth germ at every interior point. All ordinary height jets are
therefore those of the genuine determinant ratio. The fixed low order
and loss come entirely from the previously proved scalar estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

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
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hbound⟩ := negativeHeight_from_coefficients_fixed_loss hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hApos l u κ hl hlu hκ
  obtain ⟨B, hBpos, hjet⟩ := hbound A hApos l u κ hl hlu hκ
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs hlow m side
  dsimp only
  intro q hq hvalue hgap hcoeff hξjet
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have ha := hcoeff 0
  have hb := hcoeff 1
  have hc := hcoeff 2
  simp [canonicalCoefficientComponent] at ha hb hc
  have hF := ((hA.boundary z hz hs i).2.2.2.2.1 q (subset_closure hq)).1
  have hformula := hjet (z - (C.referenceState, 0)) hlow (L.coefficients z)
    (fun y => (K.chart z i y).1) q ha.1 hb.1 hc.1 hF.fst hvalue hgap
    ha.2 hb.2 hc.2 hξjet
  have he : K.height z i =ᶠ[𝓝 q] (fun y => ((K.chart z i y).1 /
      ((L.coefficients z).b y ^ 2 - (L.coefficients z).a y * (L.coefficients z).c y)) ^ (1 / 4 : ℝ)) := by
    filter_upwards [(hA.domains z hz hs i).1.mem_nhds hq] with y hy
    exact (negativeCutPair_height_eq_fourthRoot hS hT hN hL hA hB hz hs m side y hy).2
  intro n
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
  exact hformula.2 n

end ContinuousFlexibility.Analysis
