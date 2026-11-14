module

public import ContinuousFlexibility.Analysis.N04PrincipalJetRegularity
public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue
public import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Recovering the vanishing value estimate from the first parameter jet

Products, reciprocals and differential expressions are first estimated as
genuine parameter towers. Their value difference is then estimated along
the reference segment. Only parameter order one is used, on the same
neighborhood, so this step makes no order-dependent neighborhood choice.
-/

@[expose] public section

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

/-- The sum grading is controlled by twice the sector-neighborhood radius. -/
theorem n04Principal_parameter_low_le_one {S : PhysicalSpacesData}
    {base : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 2)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε) :
    parameterGrading S base z ≤ 1 := by
  have he : parameterGrading S base z = sectorGrading S base z.1 + |z.2| :=
    pairGrading_apply (E := StateDirections S) (F := ℝ)
      (sectorGrading S) realGrading base z
  rw [he]
  have h₁ : sectorGrading S base z.1 < ε := hz.1
  have h₂ : |z.2| < ε := hz.2
  linarith

/-- A complete genuine difference tower plus its first-jet estimate gives
the entire current-data interface, including the displacement-only value
bound. All pieces use the same constants. -/
theorem n04Principal_currentData_of_tower
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hreg : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ContDiffOn ℝ ∞ (f z m) unitStrip ∧
        ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (hzero : ∀ m, P m → EqOn (f 0 m) (f₀ m) unitStrip)
    (J : ∀ m (i j : ℕ) (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (fun y => f z m y - f₀ m y) q.val))
    (htower : ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        ∀ m, P m → ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |(J m i j q).D k z v| ≤
            B * T.E0 (T.sample (cell m)) ^ B *
              T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
                oneHighVariationWeight (parameterGrading S) base (s + loss) z v) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  have h0 : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  have hfirst := htower 1
  refine ⟨hreg, fun m _ => J m, ⟨max base hfirst.choose, fun s => ?_⟩, htower⟩
  let B : ℝ := (hfirst.choose_spec s).choose
  have hB : 0 < B := (hfirst.choose_spec s).choose_spec.1
  let B' : ℝ := 4 * B + 1
  have hB' : 0 < B' := by dsimp only [B']; positivity
  have hBB' : B ≤ B' := by dsimp only [B']; linarith
  have h3B : 3 * B ≤ B' := by dsimp only [B']; linarith
  refine ⟨B', hB', ?_⟩
  intro z hz m hm q i j hij
  let high : ℕ := s + max base hfirst.choose
  let M : ℝ := B * T.E0 (T.sample (cell m)) ^ B *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hE0 := zero_le_one.trans (hE m)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hE0 _)) (Real.rpow_nonneg (hH m) _)
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (0 : Parameter S) + t • z ∈
      sectorNeighborhood S base ε ε := by
    intro t ht
    simpa only [smul_zero, zero_add] using
      (sectorNeighborhood_convex S base ε ε) h0 hz
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hbound : ∀ y ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin 1 → Parameter S,
        |(J m i j q).D 1 y v| ≤ M *
          oneHighVariationWeight (parameterGrading S) base high (y - 0) v := by
    intro y hy v
    have hb := (hfirst.choose_spec s).choose_spec.2 y hy v m hm q i j hij
    have hw := oneHighVariationWeight_mono hmono (le_refl base)
      (Nat.add_le_add_left (le_max_right base hfirst.choose) s) y v
    simpa only [sub_zero] using hb.trans (mul_le_mul_of_nonneg_left hw hM)
  have hv := n04Realization_smoothDirections_difference_value_bound
    (J m i j q) (parameterGrading S) base high 0 z
    (hmono (by dsimp only [high]; omega)) hsegment
    (n04Principal_parameter_low_le_one hεhalf hz) hM hbound
  have hjetzero : mixedDerivative i j (fun y => f 0 m y - f₀ m y) q.val = 0 := by
    have heq : EqOn (fun y => f 0 m y - f₀ m y) (fun _ => (0 : ℝ)) unitStrip :=
      fun y hy => sub_eq_zero.mpr (hzero m hm hy)
    exact (mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
      heq i j q.property).trans (mixedDerivative_fun_zero i j q.val)
  simp only [zero_add, hjetzero, sub_zero] at hv
  have hcoef : 3 * M ≤ B' * T.E0 (T.sample (cell m)) ^ B' *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) := by
    calc
      3 * M = (3 * B) * T.E0 (T.sample (cell m)) ^ B *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) := by dsimp only [M]; ring
      _ ≤ B' * T.E0 (T.sample (cell m)) ^ B' *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h3B (Real.rpow_le_rpow_of_exponent_le (hE m) hBB')
            (Real.rpow_nonneg hE0 _) hB'.le) (Real.rpow_nonneg (hH m) _)
  exact hv.trans (mul_le_mul_of_nonneg_right hcoef (apply_nonneg _ _))

end ContinuousFlexibility.Analysis
