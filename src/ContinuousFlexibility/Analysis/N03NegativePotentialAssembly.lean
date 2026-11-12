import ContinuousFlexibility.Analysis.N03NegativePotentialPhysicalJets
import ContinuousFlexibility.Analysis.N03CoefficientFDerivJets
import ContinuousFlexibility.Analysis.CanonicalCutPartitionTopology
import ContinuousFlexibility.Analysis.N01ControlledRootInput

/-!
# From the two physical halves to every negative canonical potential

The quantitative physical estimates below are the output to be supplied
by the root-band and interior constructions. Coefficient jets are obtained
from the actual N03 error estimate. The topological classification of
negative indices identifies every negative piece with a genuine cut
half, and the actual inverse-field closure then gives the required
potential estimates on one common state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def PairedNegativePhysicalJetBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ m : ℕ, ∃ κ : ℝ, ∃ A : ℕ → ℝ, 0 < κ ∧ (∀ n, 0 < A n) ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ side : Bool,
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    ∀ q ∈ physicalPieceOpen S K z i,
      κ ≤ |planeJacobian (K.chart z i) q| ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss A
        (z - (C.referenceState, 0)) (K.height z i) q ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (K.chart z i) q‖ ≤
        A n * (1 + pairGrading (stateGrading S) realGrading (n + loss)
          (z - (C.referenceState, 0)))

private theorem negative_physical_grade_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {a b : ℕ} (hab : a ≤ b) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (z : E) :
    A * (1 + p a z) ≤ B * (1 + p b z) :=
  mul_le_mul hAB (add_le_add (le_refl (1 : ℝ)) (hp hab z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB)

private def negativePotentialOrderEnvelope (A : ℕ → ℝ) (s : ℕ) : ℝ :=
  1 + ∑ j : Fin (s + 1), A j

private theorem negativePotentialOrderEnvelope_pos
    {A : ℕ → ℝ} (hA : ∀ n, 0 < A n) (s : ℕ) :
    0 < negativePotentialOrderEnvelope A s :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => (hA j).le))

private theorem le_negativePotentialOrderEnvelope
    {A : ℕ → ℝ} (hA : ∀ n, 0 < A n) {k s : ℕ} (hks : k ≤ s) :
    A k ≤ negativePotentialOrderEnvelope A s := by
  have hsum := Finset.single_le_sum (f := fun j : Fin (s + 1) => A j)
    (fun j _ => (hA j).le)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hks⟩ : Fin (s + 1)))
  exact hsum.trans (le_add_of_nonneg_left zero_le_one)

theorem n03_negativePotential_bounds_of_paired_physical_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss physicalBase physicalLoss : ℕ} {ε εPhysical : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (j : ℕ → ℕ) (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hbasePhysical : base ≤ physicalBase) (hεPhysical : 0 < εPhysical)
    (hεPhysicalOld : εPhysical ≤ ε)
    (hphysical : PairedNegativePhysicalJetBounds S C K physicalBase physicalLoss εPhysical) :
    ∃ base' outLoss : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      NegativeCanonicalPotentialJetBounds S C K base' outLoss ε' := by
  obtain ⟨coefficientLoss, coefficientBase, εCoefficient, hbaseC, hεC, hεCold, hcoefficients⟩ :=
    n03_totalCoefficient_commonNeighborhood_fderiv_fixed_loss
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (K := K)
      (base := base) (loss := loss) (ε := ε)
      hS hT hN01 hN02 hN03 hA hB hfield j hcell
  let inputLoss := max coefficientLoss physicalLoss
  obtain ⟨low, outLoss, hpotential⟩ :=
    n03_negativePotential_from_physicalJets_fixed_loss hS hA hB hfield inputLoss
  let base' := max coefficientBase (max physicalBase low)
  let ε' := min εCoefficient (min εPhysical (1 / 2 : ℝ))
  have hbC : coefficientBase ≤ base' := le_max_left _ _
  have hbP : physicalBase ≤ base' := (le_max_left _ _).trans (le_max_right _ _)
  have hblow : low ≤ base' := (le_max_right _ _).trans (le_max_right _ _)
  have heC : ε' ≤ εCoefficient := min_le_left _ _
  have heP : ε' ≤ εPhysical :=
    (min_le_right εCoefficient (min εPhysical (1 / 2 : ℝ))).trans (min_le_left _ _)
  have hehalf : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : base ≤ base' := hbaseC.trans hbC
  have heold : ε' ≤ ε := heC.trans hεCold
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  refine ⟨base', outLoss, ε', hb, lt_min hεC (lt_min hεPhysical (by norm_num)), heold, ?_⟩
  intro s i hi
  have href := reference_mem_stateNeighborhood S C base hN01.2.1
  have hsref := hN01.2.2.1.stateSector
  obtain ⟨m, hpair⟩ := canonicalNegativePiece_is_paired
    hA hB.1 hN01.2.2.2.1 href hsref i hi
  obtain ⟨side, hside⟩ : ∃ side : Bool,
      i = if side then (K.cutPair m).2 else (K.cutPair m).1 := by
    rcases hpair with hleft | hright
    · exact ⟨false, hleft⟩
    · exact ⟨true, hright⟩
  obtain ⟨AC, hAC, hCbound⟩ := hcoefficients m
  obtain ⟨κ, AP, hκ, hAP, hPbound⟩ := hphysical m
  let A (n : ℕ) : ℝ := 1 + AC n + AP n
  have hAone (n : ℕ) : 1 ≤ A n := by dsimp only [A]; linarith [hAC n, hAP n]
  have hCA (n : ℕ) : AC n ≤ A n := by dsimp only [A]; linarith [hAP n]
  have hPA (n : ℕ) : AP n ≤ A n := by dsimp only [A]; linarith [hAC n]
  obtain ⟨P, hP, hbound⟩ := hpotential A hAone κ hκ
  refine ⟨negativePotentialOrderEnvelope P s, negativePotentialOrderEnvelope_pos hP s, ?_⟩
  intro z hz hs q hq a b hab
  have hzold := stateNeighborhood_mono S C hb heold hz
  have hzC := stateNeighborhood_mono S C hbC heC hz
  have hzP := stateNeighborhood_mono S C hbP heP hz
  have hzlow := stateNeighborhood_mono S C hblow le_rfl hz
  have hlow : pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by linarith only [hehalf])
  let x := K.inverseChart z i q
  have hx : x ∈ physicalPieceOpen S K z i := (hA.charts z hzold hs i).2.1 hq
  have hxside : x ∈ physicalPieceOpen S K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1) := by rw [← hside]; exact hx
  have hxN : x ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    have hu : x ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      cases side with
      | false => exact Or.inl hxside
      | true => exact Or.inr hxside
    rw [(hB.1.2 z hzold hs m).2.2.2.1] at hu
    exact hu.1
  have hphysicalPoint := hPbound z hzP hs side x hxside
  rw [← hside] at hphysicalPoint
  have hcoeff (k : Fin 3) : PointwiseMaterialJetBound
      (pairGrading (stateGrading S) realGrading) inputLoss A (z - (C.referenceState, 0))
        (canonicalCoefficientComponent k (L.coefficients z)) x := by
    intro n
    exact ((hCbound z hzC hs k x hxN).2 n).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_left _ _) n)
        (hAC n).le (hCA n) (z - (C.referenceState, 0)))
  have hheight : PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
      inputLoss A (z - (C.referenceState, 0)) (K.height z i) x := by
    intro n
    exact (hphysicalPoint.2.1 n).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_right _ _) n)
        (hAP n).le (hPA n) (z - (C.referenceState, 0)))
  have hchart (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (K.chart z i) x‖ ≤
      A n * (1 + pairGrading (stateGrading S) realGrading (n + inputLoss)
        (z - (C.referenceState, 0))) :=
    (hphysicalPoint.2.2 n hn).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_right _ _) n)
        (hAP n).le (hPA n) (z - (C.referenceState, 0)))
  exact (hbound z hzold hs hlow i hi q hq hphysicalPoint.1 hcoeff hheight hchart a b).trans
    (negative_physical_grade_mono hp (Nat.add_le_add_right hab outLoss)
      (hP (a + b)).le (le_negativePotentialOrderEnvelope hP hab) (z - (C.referenceState, 0)))

end ContinuousFlexibility.Analysis
