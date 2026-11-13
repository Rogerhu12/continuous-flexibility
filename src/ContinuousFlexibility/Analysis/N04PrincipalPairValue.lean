import ContinuousFlexibility.Analysis.N04PrincipalPairInverse
import ContinuousFlexibility.Analysis.N04PrincipalNegativeReciprocalNeighborhood

/-!
# A common value neighborhood for a paired family

Only the first parameter derivative is used to choose the low order and
the radius. This applies to any piece index, including a subtype of the
positive or negative pieces; no tower on the complementary pieces is
needed to establish the relative-error estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

namespace N04PrincipalPairBounds

theorem value_neighborhood
    {S : PhysicalSpacesData} {T : MaterialData} {ι : Type*} {cell : ι → ℕ}
    {base : ℕ} {ε : ℝ}
    {f : ι → Parameter S → PolarPoint → ℝ} {f₀ : ι → PolarPoint → ℝ}
    (hf : N04PrincipalPairBounds (parameterGrading S)
      (fun m => T.E0 (T.sample (cell m)))
      (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (U := sectorNeighborhood S base ε ε) (Ω := unitStrip) f f₀)
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hzero : ∀ m, EqOn (f m 0) (f₀ m) unitStrip) :
    ∃ b : ℕ, base ≤ b ∧ ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S b (min ε (1 / 2)) (min ε (1 / 2)),
        ∀ m q, q ∈ unitStrip →
          |f m z q - f₀ m q| ≤ B * T.E0 (T.sample (cell m)) ^ B *
            T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * parameterGrading S b z := by
  let t : ℕ := hf.choose
  let RD : ∀ m, MixedJetRegularity (sectorNeighborhood S base ε ε) unitStrip
      (fun z q => f m z q - f₀ m q) :=
    hf.choose_spec.choose_spec.choose_spec.choose
  have hD : N04PrincipalWeightedTowerBounds (parameterGrading S) t
      (fun m => T.E0 (T.sample (cell m)))
      (fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) RD :=
    hf.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  have hfirst := hD 1
  let b : ℕ := max base (max t hfirst.choose)
  have hbase : base ≤ b := le_max_left _ _
  have ht : t ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hloss : hfirst.choose ≤ b := (le_max_right _ _).trans (le_max_right _ _)
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hsub : sectorNeighborhood S b δ δ ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hbase (min_le_left _ _) (min_le_left _ _)
  have hU : IsOpen (sectorNeighborhood S b δ δ) := isOpen_sectorNeighborhood S b δ δ
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  have h0 : (0 : Parameter S) ∈ sectorNeighborhood S b δ δ := by
    constructor
    · change sectorGrading S b 0 < δ
      exact (sectorGrading S b).map_zero'.trans_lt hδ
    · change |(0 : ℝ)| < δ
      simpa only [abs_zero] using hδ
  let C : ℝ := (hfirst.choose_spec 0).choose
  have hC : 0 < C := (hfirst.choose_spec 0).choose_spec.1
  let B : ℝ := 4 * C + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB : C ≤ B := by dsimp only [B]; linarith
  have h3C : 3 * C ≤ B := by dsimp only [B]; linarith
  refine ⟨b, hbase, B, hB, ?_⟩
  intro z hz m q hq
  let J := ((RD m).parameter 0 0 q hq).restrict hU hsub
  let M : ℝ := C * T.E0 (T.sample (cell m)) ^ C *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hE0 := zero_le_one.trans (hE m)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hC.le (Real.rpow_nonneg hE0 _)) (Real.rpow_nonneg (hH m) _)
  have hsegment : ∀ s ∈ Icc (0 : ℝ) 1, (0 : Parameter S) + s • z ∈
      sectorNeighborhood S b δ δ := by
    intro s hs
    simpa only [smul_zero, zero_add] using
      (sectorNeighborhood_convex S b δ δ) h0 hz
        (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
  have hbound : ∀ y ∈ sectorNeighborhood S b δ δ, ∀ v : Fin 1 → Parameter S,
      |J.D 1 y v| ≤ M * oneHighVariationWeight (parameterGrading S) t b (y - 0) v := by
    intro y hy v
    have hylo : parameterGrading S t y ≤ 1 :=
      (hmono ht y).trans (n04Principal_parameter_low_le_one (min_le_right _ _) hy)
    have hh := (hfirst.choose_spec 0).choose_spec.2 m 0 0 (by omega) q hq y
      (hsub hy) hylo v
    have hw := oneHighVariationWeight_mono hmono (le_refl t)
      (show 0 + hfirst.choose ≤ b by simpa only [zero_add] using hloss) y v
    have hh' : |J.D 1 y v| ≤ M *
        oneHighVariationWeight (parameterGrading S) t (0 + hfirst.choose) y v :=
      (Real.norm_eq_abs _).symm.trans_le hh
    simpa only [sub_zero] using hh'.trans (mul_le_mul_of_nonneg_left hw hM)
  have hv := n04Realization_smoothDirections_difference_value_bound
    J (parameterGrading S) t b 0 z (hmono ht) hsegment
    ((hmono ht z).trans (n04Principal_parameter_low_le_one (min_le_right _ _) hz))
    hM hbound
  have hjetzero : mixedDerivative 0 0 (fun y => f m 0 y - f₀ m y) q = 0 := by
    rw [spaces_mixedDerivative_zero]
    exact sub_eq_zero.mpr (hzero m hq)
  simp only [zero_add, hjetzero, sub_zero, spaces_mixedDerivative_zero] at hv
  have hcoef : 3 * M ≤ B * T.E0 (T.sample (cell m)) ^ B *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) := by
    calc
      3 * M = (3 * C) * T.E0 (T.sample (cell m)) ^ C *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) := by dsimp only [M]; ring
      _ ≤ B * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h3C (Real.rpow_le_rpow_of_exponent_le (hE m) hCB)
            (Real.rpow_nonneg hE0 _) hB.le) (Real.rpow_nonneg (hH m) _)
  exact hv.trans (mul_le_mul_of_nonneg_right hcoef (apply_nonneg _ _))

end N04PrincipalPairBounds

end ContinuousFlexibility.Analysis
