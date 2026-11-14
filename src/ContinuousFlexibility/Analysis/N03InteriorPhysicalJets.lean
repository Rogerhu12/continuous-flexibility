module

public import ContinuousFlexibility.Analysis.N03InteriorChartJets
public import ContinuousFlexibility.Analysis.N03InteriorHeightJets
public import ContinuousFlexibility.Analysis.N03InteriorJacobianBounds

/-!
# Closing the physical estimates in the negative interior

The actual first-integral jets and their positive angular derivatives
give the actual chart jets. A positive travel interval bounds its radial
coordinate. The coefficient discriminant lower bound then gives the
height jets and, through the two transport equations, a positive lower
bound on the actual chart Jacobian. One low order and one loss work for
all component constants and all output orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem interior_physical_envelope_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    {j k : ℕ} (hjk : j ≤ k) (z : E) :
    A * (1 + p j z) ≤ B * (1 + p k z) :=
  mul_le_mul hAB (add_le_add (le_refl (1 : ℝ)) (hp hjk z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) (hA.trans hAB)

private theorem interior_zero_bound_le_twice
    {v A t : ℝ} (hA : 0 ≤ A) (ht : t ≤ 1) (hv : v ≤ A * (1 + t)) :
    v ≤ 2 * A := by
  calc
    v ≤ A * (1 + t) := hv
    _ ≤ A * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) ht) hA
    _ = 2 * A := by ring

private theorem interior_speed_gap_lower
    {a b c M κ : ℝ} (ha : 0 < a) (hM : 0 < M) (hκ : 0 < κ)
    (haM : a ≤ 2 * M) (hdisc : κ ≤ b ^ 2 - a * c) :
    Real.sqrt κ / M ≤
      (b / a + Real.sqrt (b ^ 2 - a * c) / a) -
        (b / a - Real.sqrt (b ^ 2 - a * c) / a) := by
  have hsqrt : Real.sqrt κ ≤ Real.sqrt (b ^ 2 - a * c) := Real.sqrt_le_sqrt hdisc
  calc
    Real.sqrt κ / M = (2 * Real.sqrt κ) / (2 * M) := by
      field_simp [hM.ne'] <;> ring
    _ ≤ (2 * Real.sqrt κ) / a :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) ha haM
    _ ≤ (2 * Real.sqrt (b ^ 2 - a * c)) / a :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) ha.le
    _ = _ := by ring

private theorem interior_rootPower_interval
    {l u t : ℝ} (hl : 0 < l) (hlu : l ≤ u) (ht : t ∈ Icc l u) :
    0 < rootTravelPower l ∧ rootTravelPower l ≤ rootTravelPower u ∧
      rootTravelPower t ∈ Icc (rootTravelPower l) (rootTravelPower u) := by
  have hmon {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      rootTravelPower x ≤ rootTravelPower y :=
    Real.rpow_le_rpow (mul_nonneg (by norm_num) hx)
      (mul_le_mul_of_nonneg_left hxy (by norm_num)) (by norm_num)
  exact ⟨Real.rpow_pos_of_pos (mul_pos (by norm_num) hl) _,
    hmon hl.le hlu, hmon hl.le ht.1, hmon (hl.le.trans ht.1) ht.2⟩

private theorem interior_radial_coefficient_value_le
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {w : E}
    {P : SymmetricCoefficients} {q : PolarPoint}
    (ha : PointwiseMaterialJetBound p loss A w
      (canonicalCoefficientComponent (0 : Fin 3) P) q) :
    |P.a q| ≤ A 0 * (1 + p loss w) := by
  have hzero := ha 0
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, zero_add] at hzero
  simpa only [canonicalCoefficientComponent, ↓reduceIte] using hzero

private theorem interior_physical_combine_jets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {inputLoss lossF lossH : ℕ} {A F H M B : ℕ → ℝ} {w : E}
    {P : SymmetricCoefficients} {chart : PolarPoint → PolarPoint}
    {height : PolarPoint → ℝ} {q : PolarPoint}
    (hA : ∀ n, 0 ≤ A n) (hF : ∀ n, 0 ≤ F n) (hH : ∀ n, 0 ≤ H n)
    (hAM : ∀ n, A n ≤ M n) (hFM : ∀ n, F n ≤ M n)
    (hFB : ∀ n, F n ≤ B n) (hHB : ∀ n, H n ≤ B n)
    (hcoeff : ∀ j : Fin 3, ContDiffAt ℝ ∞ (canonicalCoefficientComponent j P) q ∧
      PointwiseMaterialJetBound p inputLoss A w (canonicalCoefficientComponent j P) q)
    (hFjets : PointwiseMaterialJetBound p lossF F w (fun y => (chart y).1) q ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n chart q‖ ≤
        F n * (1 + p (n + lossF) w))
    (hheight :
      (∀ j : Fin 3, ContDiffAt ℝ ∞ (canonicalCoefficientComponent j P) q ∧
        PointwiseMaterialJetBound p (max inputLoss lossF) M w
          (canonicalCoefficientComponent j P) q) →
      PointwiseMaterialJetBound p (max inputLoss lossF) M w (fun y => (chart y).1) q →
      PointwiseMaterialJetBound p lossH H w height q) :
    PointwiseMaterialJetBound p (max lossF lossH) B w height q ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n chart q‖ ≤
        B n * (1 + p (n + max lossF lossH) w) := by
  have hcM (j : Fin 3) : ContDiffAt ℝ ∞ (canonicalCoefficientComponent j P) q ∧
      PointwiseMaterialJetBound p (max inputLoss lossF) M w
        (canonicalCoefficientComponent j P) q := by
    refine ⟨(hcoeff j).1, ?_⟩
    intro n
    exact ((hcoeff j).2 n).trans (interior_physical_envelope_mono hp
      (hA n) (hAM n) (Nat.add_le_add_left (le_max_left _ _) n) w)
  have hξM : PointwiseMaterialJetBound p (max inputLoss lossF) M w
      (fun y => (chart y).1) q := by
    intro n
    exact (hFjets.1 n).trans (interior_physical_envelope_mono hp
      (hF n) (hFM n) (Nat.add_le_add_left (le_max_right _ _) n) w)
  have hHjets := hheight hcM hξM
  constructor
  · intro n
    exact (hHjets n).trans (interior_physical_envelope_mono hp
      (hH n) (hHB n) (Nat.add_le_add_left (le_max_right _ _) n) w)
  · intro n hn
    exact (hFjets.2 n hn).trans (interior_physical_envelope_mono hp
      (hF n) (hFB n) (Nat.add_le_add_left (le_max_left _ _) n) w)

def N03InteriorPhysicalJetEstimate
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base low inputLoss outLoss : ℕ) (ε l u κ α κJ : ℝ) (A B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ m : ℕ, ∀ side : Bool,
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    ∀ q ∈ physicalPieceOpen S K z i,
      (∀ j : Fin 3, ContDiffAt ℝ ∞ (canonicalCoefficientComponent j (L.coefficients z)) q ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) inputLoss A
          (z - (C.referenceState, 0)) (canonicalCoefficientComponent j (L.coefficients z)) q) →
      (∀ plus : Bool,
        ContDiffAt ℝ ∞ (canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) q ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) inputLoss A
          (z - (C.referenceState, 0))
          (fun y => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1) y - y.2) q) →
      canonicalGluedRootTravel S K z m side q ∈ Icc l u →
      κ ≤ (L.coefficients z).b q ^ 2 - (L.coefficients z).a q * (L.coefficients z).c q →
      (∀ plus : Bool, α ≤
        angularPartial (canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) q) →
      κJ ≤ |planeJacobian (K.chart z i) q| ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) outLoss B
        (z - (C.referenceState, 0)) (K.height z i) q ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (K.chart z i) q‖ ≤
        B n * (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
          (z - (C.referenceState, 0)))

theorem n03_interiorPhysical_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ l u κ α : ℝ, 0 < l → l ≤ u → 0 < κ → 0 < α →
      ∃ κJ : ℝ, ∃ B : ℕ → ℝ, 0 < κJ ∧ (∀ n, 0 < B n) ∧
        N03InteriorPhysicalJetEstimate S C L K base low inputLoss outLoss ε l u κ α κJ A B := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨lowF, lossF, hchart⟩ := n03_cutPair_interiorChart_fixed_loss hS hA hB inputLoss
  let midLoss := max inputLoss lossF
  obtain ⟨lowH, lossH, hheight⟩ := n03_cutPair_height_fixed_loss
    hS hT hN01 hN03 hA hB midLoss
  refine ⟨max inputLoss (max lowF lowH), max lossF lossH, ?_⟩
  intro A hApos l u κ α hl hlu hκ hα
  have hApositive (n : ℕ) : 0 < A n := zero_lt_one.trans_le (hApos n)
  obtain ⟨F, hFpos, hFbound⟩ := hchart A hApositive l u hl hlu
  let M (n : ℕ) : ℝ := 1 + A n + F n
  have hM (n : ℕ) : 0 < M n := by dsimp only [M]; linarith [hApositive n, hFpos n]
  have hAM (n : ℕ) : A n ≤ M n := by dsimp only [M]; linarith [hFpos n]
  have hFM (n : ℕ) : F n ≤ M n := by dsimp only [M]; linarith [hApositive n]
  have hξbounds := interior_rootPower_interval hl hlu (show l ∈ Icc l u from ⟨le_rfl, hlu⟩)
  obtain ⟨H, hHpos, hHbound⟩ :=
    hheight M hM (rootTravelPower l) (rootTravelPower u) κ hξbounds.1 hξbounds.2.1 hκ
  let B (n : ℕ) : ℝ := 1 + F n + H n
  have hBpos (n : ℕ) : 0 < B n := by dsimp only [B]; linarith [hFpos n, hHpos n]
  have hFB (n : ℕ) : F n ≤ B n := by dsimp only [B]; linarith [hHpos n]
  have hHB (n : ℕ) : H n ≤ B n := by dsimp only [B]; linarith [hFpos n]
  let gap := Real.sqrt κ / A 0
  have hgapPos : 0 < gap := div_pos (Real.sqrt_pos.mpr hκ) (hApositive 0)
  let κJ := gap * α * α / (2 * Real.sqrt (rootTravelPower u))
  have hκJ : 0 < κJ := div_pos (mul_pos (mul_pos hgapPos hα) hα)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hξbounds.1.trans_le hξbounds.2.1)))
  refine ⟨κJ, B, hκJ, hBpos, ?_⟩
  intro z hz hs hlow m side
  dsimp only
  intro q hq hcoeff hlabels hvalue hdisc hangular
  let w := z - (C.referenceState, 0)
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hzA : p inputLoss w ≤ 1 := (hp (le_max_left _ _) w).trans hlow
  have hzF : p lowF w ≤ 1 :=
    (hp ((le_max_left _ _).trans (le_max_right _ _)) w).trans hlow
  have hzH : p lowH w ≤ 1 :=
    (hp ((le_max_right _ _).trans (le_max_right _ _)) w).trans hlow
  have hFjets := hFbound z hz hs hzF m side q hq hlabels hvalue
  have hξvalue : (K.chart z i q).1 ∈ Icc (rootTravelPower l) (rootTravelPower u) := by
    rw [canonicalCutPair_chart_eq_rootTravel hA hB hz hs m side hq]
    exact (interior_rootPower_interval hl hlu hvalue).2.2
  have hjets := interior_physical_combine_jets
    (p := p) (inputLoss := inputLoss) (lossF := lossF) (lossH := lossH)
    (A := A) (F := F) (H := H) (M := M) (B := B) (w := w)
    (P := L.coefficients z) (chart := K.chart z i) (height := K.height z i) (q := q)
    hp (fun n => (hApositive n).le) (fun n => (hFpos n).le) (fun n => (hHpos n).le)
    hAM hFM hFB hHB hcoeff hFjets
    (hHbound z hz hs hzH m side q hq hξvalue hdisc)
  have haabs : |(L.coefficients z).a q| ≤ A 0 * (1 + p inputLoss w) :=
    interior_radial_coefficient_value_le (p := p) (loss := inputLoss) (A := A)
      (w := w) (P := L.coefficients z) (q := q) (hcoeff (0 : Fin 3)).2
  have haUpper : (L.coefficients z).a q ≤ 2 * A 0 :=
    (le_abs_self _).trans (interior_zero_bound_le_twice (hApositive 0).le hzA haabs)
  have haPositive : 0 < (L.coefficients z).a q := by
    rw [hN03.1 z hz hs q]
    exact n01_originalRadialCoefficient_pos hN01 hz hs ((hA.domains z hz hs i).2.2.1 hq)
  have hgap : gap ≤ plusCharacteristicSpeed (L.coefficients z) q -
      minusCharacteristicSpeed (L.coefficients z) q :=
    interior_speed_gap_lower haPositive (hApositive 0) hκ haUpper hdisc
  refine ⟨?_, hjets.1, hjets.2⟩
  exact canonicalCutPair_jacobian_lower_of_speed_and_angular_bounds
    hS hT hN01 hN02 hN03 hA hB hz hs m side hq hgapPos.le hα.le hgap
      (hangular true) (hangular false) (Real.sqrt_le_sqrt hξvalue.2)

end ContinuousFlexibility.Analysis
