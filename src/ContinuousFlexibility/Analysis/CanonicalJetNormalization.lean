import ContinuousFlexibility.Blueprint.CanonicalParts
import ContinuousFlexibility.Analysis.N04bGeometryPreservation

/-!
# Normalizing the unused canonical jets

The canonical identities concern sector states, and divided coefficients are
used only on positive pieces. The frozen quantitative conclusion also ranges
over the remaining states and pieces. Those unused coefficients can be set to
zero without changing a chart, a height factor, an operator on sector states,
or a source pairing.

This reduction does not assert the geometric jet estimate. It separates that
estimate from the arbitrary values of fields which the geometric identities
do not constrain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- One order and one constant in the precise quantitative conjunct. -/
def CanonicalJetBoundAtOrder (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
    p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
      |mixedDerivative a b (K.dividedDifference z m).a p| +
      |mixedDerivative a b (K.dividedDifference z m).b p| +
      |mixedDerivative a b (K.dividedDifference z m).c p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)

/-- The precise quantitative conjunct in `N04Properties`, with its body
factored out to keep existential elimination independent of state-space
instance normalization. -/
def CanonicalJetBounds (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ CanonicalJetBoundAtOrder T S C K base loss ε s B

/-- The genuine estimate still required by the coordinate construction:
potential jets on sector states and divided coefficient jets on positive
pieces, at one order and one constant. -/
def SectorCanonicalJetBoundAtOrder (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε,
    stateSector S z.1 → ∀ m p,
    p ∈ canonicalOpen S K m → ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z m) p| +
      (if K.positive m = true then
        |mixedDerivative a b (K.dividedDifference z m).a p| +
        |mixedDerivative a b (K.dividedDifference z m).b p| +
        |mixedDerivative a b (K.dividedDifference z m).c p| else 0) ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          (1 + stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2|)

/-- The sector estimate at every order, with the same fixed derivative loss. -/
def SectorCanonicalJetBounds (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ SectorCanonicalJetBoundAtOrder T S C K base loss ε s B

private def zeroCanonicalCoefficients : SymmetricCoefficients where
  a := fun _ => 0
  b := fun _ => 0
  c := fun _ => 0

/-- Normalize only fields unused by the sector canonical identities. -/
def normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) : CanonicalData S := by
  classical
  exact { K with
    potential := fun z => if stateSector S z.1 then K.potential z else fun _ _ => 0
    dividedDifference := fun z m =>
      if stateSector S z.1 ∧ K.positive m = true then K.dividedDifference z m
      else zeroCanonicalCoefficients }

theorem normalizedCanonicalData_chart (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).chart = K.chart := rfl

theorem normalizedCanonicalData_inverseChart (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).inverseChart = K.inverseChart := rfl

theorem normalizedCanonicalData_height (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).height = K.height := rfl

theorem normalizedCanonicalData_coefficients (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).coefficients = K.coefficients := rfl

theorem normalizedCanonicalData_positive (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).positive = K.positive := rfl

theorem normalizedCanonicalData_left (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).left = K.left := rfl

theorem normalizedCanonicalData_right (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).right = K.right := rfl

theorem normalizedCanonicalData_cell (S : PhysicalSpacesData) (K : CanonicalData S) :
    (normalizedCanonicalData S K).cell = K.cell := rfl

theorem canonicalOpen_normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    canonicalOpen S (normalizedCanonicalData S K) m = canonicalOpen S K m := rfl

theorem physicalPieceOpen_normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) :
    physicalPieceOpen S (normalizedCanonicalData S K) z m = physicalPieceOpen S K z m := rfl

theorem canonicalHeight_normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (u : PolarPoint → ℝ) :
    canonicalHeight S (normalizedCanonicalData S K) z m u =
      canonicalHeight S K z m u := rfl

theorem canonicalSource_normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) :
    canonicalSource S (normalizedCanonicalData S K) z m f =
      canonicalSource S K z m f := rfl

theorem canonicalOperator_normalizedCanonicalData (S : PhysicalSpacesData)
    (K : CanonicalData S) (L : ReturnCorrectionData S) (z : AnnularState S × ℝ)
    (m : ℕ) (W : PolarPoint → ℝ) :
    canonicalOperator S (normalizedCanonicalData S K) L z m W =
      canonicalOperator S K L z m W := rfl

theorem normalizedCanonicalData_potential_of_sector {S : PhysicalSpacesData}
    (K : CanonicalData S) {z : AnnularState S × ℝ} (hz : stateSector S z.1) :
    (normalizedCanonicalData S K).potential z = K.potential z := by
  simp only [normalizedCanonicalData, hz, ite_true]

theorem normalizedCanonicalData_potential_of_not_sector {S : PhysicalSpacesData}
    (K : CanonicalData S) {z : AnnularState S × ℝ} (hz : ¬stateSector S z.1) :
    (normalizedCanonicalData S K).potential z = fun _ _ => 0 := by
  simp only [normalizedCanonicalData, hz, ite_false]

theorem normalizedCanonicalData_dividedDifference_of_sector_positive
    {S : PhysicalSpacesData} (K : CanonicalData S) {z : AnnularState S × ℝ}
    {m : ℕ} (hz : stateSector S z.1) (hm : K.positive m = true) :
    (normalizedCanonicalData S K).dividedDifference z m = K.dividedDifference z m := by
  simp only [normalizedCanonicalData, hz, hm, and_self, ite_true]

/-- The actual-domain geometry is transported with the unchanged
geometric fields of the indexed canonical data. -/
theorem n04PartA_normalizedCanonicalData {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : N04PartA D S C K base ε) :
    N04PartA D S C (normalizedCanonicalData S K) base ε := by
  classical
  exact h.withOperatorFields K.coefficients
    (fun z => if stateSector S z.1 then K.potential z else fun _ _ => 0)
    (fun z m => if stateSector S z.1 ∧ K.positive m = true then K.dividedDifference z m
      else zeroCanonicalCoefficients)

/-- The canonical identities use exactly the coefficients retained by normalization. -/
theorem n04PartB_normalizedCanonicalData {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (h : N04PartB S C L K base ε) :
    N04PartB S C L (normalizedCanonicalData S K) base ε := by
  obtain ⟨hcut, htrans, hop, hneg, hpos⟩ := h
  refine ⟨hcut, htrans, ?_, hneg, ?_⟩
  · intro z hz hs m W hW p hp
    simpa only [canonicalOperator_normalizedCanonicalData,
      normalizedCanonicalData_coefficients, normalizedCanonicalData_positive,
      normalizedCanonicalData_potential_of_sector K hs] using hop z hz hs m W hW p hp
  · intro z hz hs m hm p hp
    simpa only [normalizedCanonicalData_coefficients,
      normalizedCanonicalData_left, normalizedCanonicalData_right,
      normalizedCanonicalData_dividedDifference_of_sector_positive K hs hm]
      using hpos z hz hs m hm p hp

private theorem mixedDerivative_zero (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun _ => 0) p = 0 := by
  simp only [mixedDerivative, iteratedDeriv_fun_const_zero]

private theorem normalizedCanonicalData_jetSum_of_sector
    {S : PhysicalSpacesData} (K : CanonicalData S) {z : AnnularState S × ℝ}
    (hz : stateSector S z.1) (m a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b ((normalizedCanonicalData S K).potential z m) p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).a p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).b p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).c p| =
    |mixedDerivative a b (K.potential z m) p| +
      (if K.positive m = true then
        |mixedDerivative a b (K.dividedDifference z m).a p| +
        |mixedDerivative a b (K.dividedDifference z m).b p| +
        |mixedDerivative a b (K.dividedDifference z m).c p| else 0) := by
  classical
  by_cases hm : K.positive m = true
  · simp only [normalizedCanonicalData, hz, hm, and_self, ite_true, add_assoc]
  · simp only [normalizedCanonicalData, hz, hm, Bool.false_eq_true, true_and, ite_true, ite_false,
      zeroCanonicalCoefficients, mixedDerivative_zero, abs_zero, add_zero]

private theorem normalizedCanonicalData_jetSum_of_not_sector
    {S : PhysicalSpacesData} (K : CanonicalData S) {z : AnnularState S × ℝ}
    (hz : ¬stateSector S z.1) (m a b : ℕ) (p : PolarPoint) :
    |mixedDerivative a b ((normalizedCanonicalData S K).potential z m) p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).a p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).b p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).c p| = 0 := by
  simp only [normalizedCanonicalData, hz, false_and, ite_false,
    zeroCanonicalCoefficients, mixedDerivative_zero, abs_zero, add_zero]

private theorem normalizedCanonicalData_jetSum_le_weight
    {S : PhysicalSpacesData} (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m a b : ℕ) (p : PolarPoint) {B E G q : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (h : stateSector S z.1 →
      |mixedDerivative a b (K.potential z m) p| +
        (if K.positive m = true then
          |mixedDerivative a b (K.dividedDifference z m).a p| +
          |mixedDerivative a b (K.dividedDifference z m).b p| +
          |mixedDerivative a b (K.dividedDifference z m).c p| else 0) ≤
        B * E ^ B * (1 + G + |q|)) :
    |mixedDerivative a b ((normalizedCanonicalData S K).potential z m) p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).a p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).b p| +
      |mixedDerivative a b ((normalizedCanonicalData S K).dividedDifference z m).c p| ≤
      B * E ^ B * (1 + G + |q|) := by
  classical
  by_cases hs : stateSector S z.1
  · exact (normalizedCanonicalData_jetSum_of_sector K hs m a b p).le.trans (h hs)
  · exact (normalizedCanonicalData_jetSum_of_not_sector K hs m a b p).le.trans
      (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hE _))
        (add_nonneg (add_nonneg zero_le_one hG) (abs_nonneg q)))

private theorem canonicalJetBoundAtOrder_normalized_of_sector
    {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    {s : ℕ} {B : ℝ} (hB : 0 < B)
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (K.cell m)))
    (h : SectorCanonicalJetBoundAtOrder T S C K base loss ε s B) :
    CanonicalJetBoundAtOrder T S C (normalizedCanonicalData S K) base loss ε s B := by
  intro z hz m p hp a b hab
  exact normalizedCanonicalData_jetSum_le_weight K z m a b p
    (B := B) (E := T.E0 (T.sample (K.cell m)))
    (G := stateGrading S (s + loss) (z.1 - C.referenceState)) (q := z.2) hB.le (hE m)
    (apply_nonneg (stateGrading S (s + loss)) (z.1 - C.referenceState))
    (fun hs => h z hz hs m p hp a b hab)

/-- The sector estimate gives the exact frozen estimate after normalization.
There is no change in the constants or in the derivative loss. -/
theorem canonicalJetBounds_normalized_of_sector {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (K.cell m)))
    (h : SectorCanonicalJetBounds T S C K base loss ε) :
    CanonicalJetBounds T S C (normalizedCanonicalData S K) base loss ε := by
  intro s
  obtain ⟨B, hB, hb⟩ := h s
  exact ⟨B, hB, canonicalJetBoundAtOrder_normalized_of_sector hB hE hb⟩

/-- Material data supply the sampled weight positivity needed in the zero branches. -/
theorem canonicalJetBounds_normalized_of_sector_of_material
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hD : IsAccumulatingProfile D)
    (h : SectorCanonicalJetBounds T S C K base loss ε) :
    CanonicalJetBounds T S C (normalizedCanonicalData S K) base loss ε := by
  apply canonicalJetBounds_normalized_of_sector ?_ h
  obtain ⟨_, hbounds⟩ := hD
  have hsample : ∀ m, T.sample m ∈ D.cells m := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs, _⟩ := hT
    exact hs
  intro m
  have hmem : T.sample (K.cell m) ∈ Ioo D.a D.b :=
    hbounds.2.1.2.2.2.1 (K.cell m) (hsample (K.cell m))
  exact (hT.2.1 _ hmem).2.2.1.le

end ContinuousFlexibility.Analysis
