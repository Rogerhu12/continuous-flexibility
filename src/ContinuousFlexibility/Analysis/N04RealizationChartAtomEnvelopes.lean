import ContinuousFlexibility.Analysis.N04RealizationForwardFiniteJets
import ContinuousFlexibility.Analysis.N04RealizationEnvelopeAlgebra

/-!
# One finite envelope for actual charts and scalar atoms

The forward neighborhood is chosen once before the finite jet order.
At each order, one grading dominates the forward, inverse and scalar-atom
requirements. The evaluation index and its state, piece and point maps
are arbitrary. All three families use the same sampled E0 times state
weight; neither an unwrapped angular value nor a new chart is introduced.
-/

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem n04Realization_productEnvelope_of_state_mono
    {X : Type*} {E low high value : X → ℝ}
    (hE : ∀ x, 1 ≤ E x) (hhigh : ∀ x, 1 ≤ high x)
    (hlow : ∀ x, 0 ≤ low x) (hmono : ∀ x, low x ≤ high x)
    {C A : ℝ} {d : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbound : ∀ x, value x ≤ C * E x ^ A * low x ^ d) :
    HasPositiveEnvelope (fun x => E x * high x) value := by
  apply n04Realization_envelope_of_product_bound hE hhigh hC hA
  intro x
  exact (hbound x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hlow x) (hmono x) d)
    (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (hE x)) A)))

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- Actual forward, inverse and scalar fields share one coefficient/state
base. Every point map is quantified independently on its genuine domain. -/
def N04RealizationChartAtomEnvelopesAtOrder
    (X : Type*) (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base high : ℕ) (ε : ℝ) (N : ℕ) : Prop :=
  ∀ (z : X → AnnularState S × ℝ) (m : X → ℕ),
    (∀ x, z x ∈ stateNeighborhood S C base ε) → (∀ x, stateSector S (z x).1) →
    let W : X → ℝ := fun x => T.E0 (T.sample (K.cell (m x))) *
      (1 + stateGrading S high ((z x).1 - C.referenceState) + |(z x).2|)
    (∀ p : X → PolarPoint, (∀ x, p x ∈ physicalPieceOpen S K (z x) (m x)) →
      ∀ j : ℕ, 0 < j → j ≤ N → HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ j (K.chart (z x) (m x)) (p x)‖)) ∧
    (∀ p : X → PolarPoint, (∀ x, p x ∈ canonicalOpen S K (m x)) →
      ∀ j : ℕ, 0 < j → j ≤ N → HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ j (K.inverseChart (z x) (m x)) (p x)‖)) ∧
    (∀ (p : X → PolarPoint) (a : X → Atom) (f : X → PolarPoint → ℝ),
      (∀ x, p x ∈ canonicalOpen S K (m x)) →
      (∀ x, ContDiffOn ℝ ∞ (f x) (canonicalOpen S K (m x))) →
      (∀ x, EqOn (f x ∘ canonicalUnitPoint K (m x))
        (atom D T S C L K (z x) (m x) (a x)) unitStrip) →
      ∀ j : ℕ, j ≤ N → HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ j (f x) (p x)‖))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- The chosen neighborhood precedes every finite order and every state,
piece and point map. Only the common grading order grows with the prefix. -/
theorem n04Realization_chartAtom_envelopes
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ N : ℕ, ∃ r : ℕ, ∀ X : Type u,
        N04RealizationChartAtomEnvelopesAtOrder X D T S C L K base' r η N := by
  obtain ⟨base', hb, η, hη, hηε, hforward⟩ :=
    n04Realization_forwardChart_finite_E0_jets hD hT hε hrefState hgeom href hcur hfloor
  obtain ⟨dInv, hinverse⟩ :=
    n04Realization_inverseChart_positive_E0_jets hD hT hrefState href hcur
      (fun m => (hgeom.referenceBounds m).2.1)
      (fun m => (hgeom.referenceBounds m).1) hfloor
  obtain ⟨dScalar, hscalar⟩ :=
    n04Realization_canonicalAtom_frechet_bounds hD hT hrefState href hcur
      (fun m => (hgeom.referenceBounds m).2.1) hfloor
  refine ⟨base', hb, η, hη, hηε, fun N => ?_⟩
  obtain ⟨rForward, dForward, CForward, AForward, hCForward, hAForward, hF⟩ := hforward N
  let r : ℕ := max rForward (max (N + dInv) (N + dScalar))
  have hrForward : rForward ≤ r := le_max_left _ _
  have hrInv : N + dInv ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hrScalar : N + dScalar ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨r, ?_⟩
  intro X
  intro z m hz hs
  let E : X → ℝ := fun x => T.E0 (T.sample (K.cell (m x)))
  let rho : ℕ → X → ℝ :=
    fun k x => 1 + stateGrading S k ((z x).1 - C.referenceState) + |(z x).2|
  have hE (x : X) : 1 ≤ E x := hfloor (m x)
  have hrho (k : ℕ) (x : X) : 1 ≤ rho k x := by
    dsimp only [rho]
    linarith only [apply_nonneg (stateGrading S k) ((z x).1 - C.referenceState),
      abs_nonneg (z x).2]
  have hrhoMono {a b : ℕ} (hab : a ≤ b) (x : X) : rho a x ≤ rho b x := by
    dsimp only [rho]
    linarith only [stateGrading_monotone S hab ((z x).1 - C.referenceState)]
  have hzold (x : X) : z x ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb hηε (hz x)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j hj hjN
    exact n04Realization_productEnvelope_of_state_mono
      (E := E) (low := rho rForward) (high := rho r) (d := dForward)
      hE (hrho r) (fun x => zero_le_one.trans (hrho rForward x))
      (hrhoMono hrForward) hCForward.le hAForward
      (fun x => hF (z x) (hz x) (hs x) (m x) (p x) (hp x) j hj hjN)
  · intro p hp j hj hjN
    obtain ⟨B, hB, hbound⟩ := hinverse j hj
    have hjr : j + dInv ≤ r := (Nat.add_le_add_right hjN dInv).trans hrInv
    apply n04Realization_productEnvelope_of_state_mono
      (E := E) (low := rho (j + dInv)) (high := rho r) (C := B) (A := B) (d := 1)
      hE (hrho r) (fun x => zero_le_one.trans (hrho (j + dInv) x))
      (hrhoMono hjr) hB.le hB.le
    intro x
    simpa only [pow_one] using
      hbound (z x) (hzold x) (hs x) (m x) (p x) (hp x)
  · intro p a f hp hf heq j hjN
    obtain ⟨B, hB, hbound⟩ := hscalar j
    have hjr : j + dScalar ≤ r := (Nat.add_le_add_right hjN dScalar).trans hrScalar
    apply n04Realization_productEnvelope_of_state_mono
      (E := E) (low := rho (j + dScalar)) (high := rho r) (C := B) (A := B) (d := 1)
      hE (hrho r) (fun x => zero_le_one.trans (hrho (j + dScalar) x))
      (hrhoMono hjr) hB.le hB.le
    intro x
    simpa only [pow_one] using
      hbound (z x) (hzold x) (hs x) (m x) (a x) (f x) (hf x) (heq x) (p x) (hp x)

end ContinuousFlexibility.Analysis
