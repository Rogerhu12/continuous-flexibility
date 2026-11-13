import ContinuousFlexibility.Analysis.N04SourceColumnsCollectorBounds
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Selected-piece current data from genuine positive-order towers

The first parameter derivative gives the vanishing reference difference.
Higher positive derivatives retain the same sampled height factor, and the
zeroth tower follows from that value estimate. Every input and every tower
is restricted to the selected pieces, including when the predicate is empty.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- One first-order estimate gives the exact reference-difference value
bound, uniformly over all pieces selected by the predicate. -/
theorem n04NegativeGeometry_values_of_first_towers
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (RF : ∀ m, P m → MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f z m))
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    (hlow : ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S base z ≤ 1)
    (hbound : ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin 1 → Parameter S,
        |((RF m hm).parameter i j q hq).D 1 z v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → ∀ (q : unitStrip) (i j : ℕ),
        i + j ≤ s →
        |mixedDerivative i j (fun y => f z m y - f₀ m y) q.val| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            parameterGrading S (s + loss) z := by
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hz₀ : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hpmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hsegment (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0 : Parameter S) + t • z ∈ sectorNeighborhood S base ε ε := by
    have hs := (sectorNeighborhood_convex S base ε ε) hz₀ hz
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_zero, zero_add] using hs
  refine ⟨base + hbound.choose, fun s => ?_⟩
  have hs := hbound.choose_spec s
  have hpack := coefficientEnvelope_pack (3 * hs.choose) hs.choose
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro z hz m hm q i j hij
  let M : ℝ := hs.choose * T.E0 (T.sample (cell m)) ^ hs.choose *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hs.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    (Real.rpow_nonneg (hH m) _)
  have hv := n04SourceColumns_mixed_difference_value hΩ (RF m hm) (h₀ m hm) (hzero m hm)
    (parameterGrading S) hpmono base (s + hbound.choose) (s + (base + hbound.choose))
    (by omega) (by omega) i j q.property hz (hsegment z hz) (hlow z hz) hM
    (fun y hy v => hs.choose_spec.2 m hm q.val q.property i j hij y hy v)
  exact n04SourceColumns_pack_difference_value
    (Real.rpow_nonneg (hH m) (3 / 4 : ℝ))
    (apply_nonneg (parameterGrading S (s + (base + hbound.choose))) z)
    (hpack.choose_spec.2 (T.E0 (T.sample (cell m))) (hE m)) hv

/-- Assemble the repaired interface from actual selected-piece spatial
regularity and all positive-order parameter towers with the sharp cost. -/
theorem CurrentJetDataOn.of_positive_towers
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (RF : ∀ m, P m → MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z => f z m))
    (hperiod : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m → ∀ q ∈ unitStrip,
      f z m (q + (0, Real.pi)) = f z m q)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hzero : ∀ m, P m → ∀ q ∈ unitStrip, f 0 m q = f₀ m q)
    (hlow : ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S base z ≤ 1)
    (hbound : ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |((RF m hm).parameter i j q hq).D k z v| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  have hU : IsOpen (sectorNeighborhood S base ε ε) := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  let JD : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val) :=
    fun m hm i j q =>
      n04SourceColumns_differenceTower hU hΩ (RF m hm) (h₀ m hm) i j q.val q.property
  have hvalue := n04NegativeGeometry_values_of_first_towers hε hE hH RF h₀ hzero hlow
    (hbound 1 zero_lt_one)
  refine ⟨fun z hz m hm => ⟨(RF m hm).spatial z hz, hperiod z hz m hm⟩, JD, hvalue, ?_⟩
  intro k
  by_cases hk : k = 0
  · subst k
    refine ⟨hvalue.choose, fun s => ⟨(hvalue.choose_spec s).choose,
      (hvalue.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v m hm q i j hij
    have hv := (hvalue.choose_spec s).choose_spec.2 z hz m hm q i j hij
    have hcost : 0 ≤ (hvalue.choose_spec s).choose *
        T.E0 (T.sample (cell m)) ^ (hvalue.choose_spec s).choose *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
      mul_nonneg (mul_nonneg (hvalue.choose_spec s).choose_spec.1.le
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (Real.rpow_nonneg (hH m) _)
    exact n04SourceColumns_zeroJet_of_value (JD m hm i j q) (parameterGrading S) base
      (s + hvalue.choose) hcost hz v hv
  · have ht := hbound k (Nat.pos_of_ne_zero hk)
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz v m hm q i j hij
    have he := n04SourceColumns_positive_difference_jet hΩ (RF m hm) (h₀ m hm) i j q.property
      (JD m hm i j q) (Nat.pos_of_ne_zero hk) hz v
    exact (congrArg abs he).trans_le
      ((ht.choose_spec s).choose_spec.2 m hm q.val q.property i j hij z hz v)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.of_positive_towers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.of_positive_towers
