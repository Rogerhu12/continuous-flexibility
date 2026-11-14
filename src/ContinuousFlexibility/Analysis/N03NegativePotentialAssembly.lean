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

private theorem negativePotential_paired_family_bounds
    {E Z : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    (shift : Z → E) (states coefficientStates physicalStates smallerStates : Set Z)
    (sector : Z → Prop) (positive : ℕ → Bool) (pair : ℕ → ℕ × ℕ)
    (coeff : Z → SymmetricCoefficients) (F G : Z → ℕ → PolarPoint → PolarPoint)
    (H v : Z → ℕ → PolarPoint → ℝ)
    (U : Z → ℕ → Set PolarPoint) (V component : ℕ → Set PolarPoint)
    {coefficientLoss physicalLoss low outLoss : ℕ}
    (hsub : smallerStates ⊆ states) (hsubC : smallerStates ⊆ coefficientStates)
    (hsubP : smallerStates ⊆ physicalStates)
    (hlow : ∀ z ∈ smallerStates, p low (shift z) ≤ 1)
    (hpaired : ∀ i, positive i = false → ∃ m, i = (pair m).1 ∨ i = (pair m).2)
    (hGU : ∀ z ∈ states, sector z → ∀ i, MapsTo (G z i) (V i) (U z i))
    (hsubset : ∀ z ∈ states, sector z → ∀ m,
      U z (pair m).1 ∪ U z (pair m).2 ⊆ component m)
    (hcoefficients : ∀ m, ∃ AC : ℕ → ℝ, (∀ n, 0 < AC n) ∧
      ∀ z ∈ coefficientStates, sector z → ∀ k : Fin 3, ∀ x ∈ component m,
        ContDiffAt ℝ ∞ (canonicalCoefficientComponent k (coeff z)) x ∧
        PointwiseMaterialJetBound p coefficientLoss AC (shift z)
          (canonicalCoefficientComponent k (coeff z)) x)
    (hphysical : ∀ m, ∃ κ : ℝ, ∃ AP : ℕ → ℝ, 0 < κ ∧ (∀ n, 0 < AP n) ∧
      ∀ z ∈ physicalStates, sector z → ∀ side : Bool,
      let i := if side then (pair m).2 else (pair m).1
      ∀ x ∈ U z i, κ ≤ |planeJacobian (F z i) x| ∧
        PointwiseMaterialJetBound p physicalLoss AP (shift z) (H z i) x ∧
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) x‖ ≤
          AP n * (1 + p (n + physicalLoss) (shift z)))
    (hpotential : ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) → ∀ κ : ℝ, 0 < κ →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ states, sector z → p low (shift z) ≤ 1 →
      ∀ i, positive i = false → ∀ q ∈ V i,
        κ ≤ |planeJacobian (F z i) (G z i q)| →
        (∀ k : Fin 3, PointwiseMaterialJetBound p (max coefficientLoss physicalLoss)
          A (shift z) (canonicalCoefficientComponent k (coeff z)) (G z i q)) →
        PointwiseMaterialJetBound p (max coefficientLoss physicalLoss)
          A (shift z) (H z i) (G z i q) →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (F z i) (G z i q)‖ ≤
          A n * (1 + p (n + max coefficientLoss physicalLoss) (shift z))) →
        ∀ a b : ℕ, |mixedDerivative a b (v z i) q| ≤
          B (a + b) * (1 + p (a + b + outLoss) (shift z))) :
    ∀ s i : ℕ, positive i = false → ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ smallerStates, sector z → ∀ q ∈ V i, ∀ a b : ℕ, a + b ≤ s →
        |mixedDerivative a b (v z i) q| ≤ B * (1 + p (s + outLoss) (shift z)) := by
  let inputLoss := max coefficientLoss physicalLoss
  intro s i hi
  obtain ⟨m, hpair⟩ := hpaired i hi
  obtain ⟨side, hside⟩ : ∃ side : Bool,
      i = if side then (pair m).2 else (pair m).1 := by
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
  have hzold := hsub hz
  have hzC := hsubC hz
  have hzP := hsubP hz
  have hlz := hlow z hz
  let x := G z i q
  have hx : x ∈ U z i := hGU z hzold hs i hq
  have hxside : x ∈ U z
      (if side then (pair m).2 else (pair m).1) := by rw [← hside]; exact hx
  have hxN : x ∈ component m := by
    apply hsubset z hzold hs m
    cases side with
    | false => exact Or.inl hxside
    | true => exact Or.inr hxside
  have hphysicalPoint := hPbound z hzP hs side x hxside
  rw [← hside] at hphysicalPoint
  have hcoeff (k : Fin 3) : PointwiseMaterialJetBound
      p inputLoss A (shift z)
        (canonicalCoefficientComponent k (coeff z)) x := by
    intro n
    exact ((hCbound z hzC hs k x hxN).2 n).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_left _ _) n)
        (hAC n).le (hCA n) (shift z))
  have hheight : PointwiseMaterialJetBound p
      inputLoss A (shift z) (H z i) x := by
    intro n
    exact (hphysicalPoint.2.1 n).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_right _ _) n)
        (hAP n).le (hPA n) (shift z))
  have hchart (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (F z i) x‖ ≤
      A n * (1 + p (n + inputLoss)
        (shift z)) :=
    (hphysicalPoint.2.2 n hn).trans
      (negative_physical_grade_mono hp (Nat.add_le_add_left (le_max_right _ _) n)
        (hAP n).le (hPA n) (shift z))
  exact (hbound z hzold hs hlz i hi q hq hphysicalPoint.1 hcoeff hheight hchart a b).trans
    (negative_physical_grade_mono hp (Nat.add_le_add_right hab outLoss)
      (hP (a + b)).le (le_negativePotentialOrderEnvelope hP hab) (shift z))

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
  have href := reference_mem_stateNeighborhood S C base hN01.2.1
  have hsref := hN01.2.2.1.stateSector
  have hlow : ∀ z ∈ stateNeighborhood S C base' ε',
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
    intro z hz
    have hzlow := stateNeighborhood_mono S C hblow le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hzlow).trans
      (by linarith only [hehalf])
  have hsubset : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m,
      physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 ⊆
          Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    intro z hz hs m x hx
    rw [(hB.1.2 z hz hs m).2.2.2.1] at hx
    exact hx.1
  exact negativePotential_paired_family_bounds
    (E := AnnularState S × ℝ) (Z := AnnularState S × ℝ)
    (p := pairGrading (stateGrading S) realGrading)
    (coefficientLoss := coefficientLoss) (physicalLoss := physicalLoss)
    (low := low) (outLoss := outLoss) hp
    (fun z => z - (C.referenceState, 0))
    (stateNeighborhood S C base ε) (stateNeighborhood S C coefficientBase εCoefficient)
    (stateNeighborhood S C physicalBase εPhysical) (stateNeighborhood S C base' ε')
    (fun z => stateSector S z.1) K.positive K.cutPair L.coefficients
    K.chart K.inverseChart K.height K.potential (physicalPieceOpen S K)
    (canonicalOpen S K) (fun m => Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (stateNeighborhood_mono S C hb heold) (stateNeighborhood_mono S C hbC heC)
    (stateNeighborhood_mono S C hbP heP) hlow
    (fun i hi => canonicalNegativePiece_is_paired hA hB.1
      hN01.2.2.2.1 href hsref i hi)
    (fun z hz hs i => (hA.charts z hz hs i).2.1) hsubset
    hcoefficients hphysical hpotential

end ContinuousFlexibility.Analysis
