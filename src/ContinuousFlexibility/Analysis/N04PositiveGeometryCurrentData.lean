module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue
public import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
public import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus

/-!
# Completing current data from genuine positive parameter jets

The constructors of the positive chart supply the current mixed-jet
towers and estimates of their positive parameter derivatives. The
reference difference is then an actual subtraction. Its value estimate
comes from the first derivative on the reference segment; in particular,
the required value bound vanishes at zero parameter. The zeroth tower
bound follows from that value bound, on the same neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem triple_material_cost {B E H : ℝ}
    (hB : 0 < B) (hE : 1 ≤ E) (hH : 0 ≤ H) :
    3 * (B * E ^ B * H ^ (3 / 4 : ℝ)) ≤
      (3 * B) * E ^ (3 * B) * H ^ (3 / 4 : ℝ) := by
  have hpow : E ^ B ≤ E ^ (3 * B) :=
    Real.rpow_le_rpow_of_exponent_le hE (by linarith only [hB])
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * B))
    (Real.rpow_nonneg hH (3 / 4 : ℝ))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

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

/-- Positive parameter derivatives of the actual current family imply
the complete difference certificate, including the value estimate with
no additive constant. The base, radius, samples and spatial family stay
unchanged. -/
theorem CurrentJetDataOn.of_positiveParameterJets
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hε : 0 < ε)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hlow : ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S base z ≤ 1)
    (hregular : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, P m →
      ContDiffOn ℝ ∞ (f z m) unitStrip ∧
        ∀ q ∈ unitStrip, f z m (q + (0, Real.pi)) = f z m q)
    (href : ∀ m, P m → f₀ m = f 0 m)
    (J : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q.val))
    (hbound : ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        ∀ m, ∀ hm : P m, ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
          |(J m hm i j q).D k z v| ≤
            B * T.E0 (T.sample (cell m)) ^ B *
              T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
                oneHighVariationWeight (parameterGrading S) base (s + loss) z v) :
    CurrentJetDataOn S T cell P base ε f f₀ := by
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hzero : (0 : Parameter S) ∈ U := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  have hmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have hsegment (z : Parameter S) (hz : z ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0 : Parameter S) + t • z ∈ U := by
    simpa only [smul_zero, zero_add] using
      (sectorNeighborhood_convex S base ε ε) hzero hz
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hreference (m : ℕ) (hm : P m) : ContDiffOn ℝ ∞ (f₀ m) unitStrip :=
    (href m hm).symm ▸ (hregular 0 hzero m hm).1
  let JD : ∀ m, P m → ∀ i j (q : unitStrip),
      SmoothDirections U
        (fun z => mixedDerivative i j (fun p => f z m p - f₀ m p) q.val) :=
    fun m hm i j q =>
      (smoothDirectionsAdd (J m hm i j q)
        (smoothDirections_constant hU (-mixedDerivative i j (f₀ m) q.val))).congr
        (fun z hz => (sub_eq_add_neg _ _).symm.trans
          (mixedDerivative_sub_of_contDiffOn hΩ (hregular z hz m hm).1
            (hreference m hm) i j q.property).symm)
  have hpositive (k : ℕ) (hk : 0 < k) (z : Parameter S) (hz : z ∈ U)
      (v : Fin k → Parameter S) (m : ℕ) (hm : P m) (q : unitStrip) (i j : ℕ) :
      (JD m hm i j q).D k z v = (J m hm i j q).D k z v := by
    let K := (JD m hm i j q).congr (fun x hx =>
      mixedDerivative_sub_of_contDiffOn hΩ (hregular x hx m hm).1
        (hreference m hm) i j q.property)
    exact smoothDirections_D_sub_constant (J m hm i j q) K hk hz v
  have hv : ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z ∈ U, ∀ m, P m → ∀ (q : unitStrip) (i j : ℕ), i + j ≤ s →
        |mixedDerivative i j (fun p => f z m p - f₀ m p) q.val| ≤
          B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            parameterGrading S (s + loss) z := by
    have hfirst := hbound 1 zero_lt_one
    let loss := max hfirst.choose base
    refine ⟨loss, fun s => ?_⟩
    have hs := hfirst.choose_spec s
    let B := hs.choose
    have hB : 0 < B := hs.choose_spec.1
    refine ⟨3 * B, mul_pos (by norm_num) hB, ?_⟩
    intro z hz m hm q i j hij
    let M := B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
    have hM : 0 ≤ M := mul_nonneg
      (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
      (Real.rpow_nonneg (hH m) _)
    have hj : ∀ y ∈ U, ∀ v : Fin 1 → Parameter S,
        |(J m hm i j q).D 1 y v| ≤ M *
          oneHighVariationWeight (parameterGrading S) base (s + loss) y v := by
      intro y hy v
      exact (hs.choose_spec.2 y hy v m hm q i j hij).trans
        (mul_le_mul_of_nonneg_left
          (oneHighVariationWeight_mono hmono le_rfl
            (Nat.add_le_add_left (le_max_left _ _) s) y v) hM)
    have horder : parameterGrading S base ≤ parameterGrading S (s + loss) :=
      hmono (by dsimp only [loss]; omega)
    have hv0 := n04Realization_smoothDirections_difference_value_bound
      (J m hm i j q) (parameterGrading S) base (s + loss) 0 z horder
      (hsegment z hz) (hlow z hz) hM
      (fun y hy v => by simpa only [sub_zero] using hj y hy v)
    have hv1 : |mixedDerivative i j (f z m) q.val -
        mixedDerivative i j (f 0 m) q.val| ≤ (3 * M) * parameterGrading S (s + loss) z := by
      simpa only [zero_add] using hv0
    have heq := mixedDerivative_sub_of_contDiffOn hΩ (hregular z hz m hm).1
      (hreference m hm) i j q.property
    have hrf : mixedDerivative i j (f₀ m) q.val = mixedDerivative i j (f 0 m) q.val :=
      congrArg (fun g => mixedDerivative i j g q.val) (href m hm)
    have hb := hv1.trans (mul_le_mul_of_nonneg_right
      (triple_material_cost hB (hE m) (hH m)) (apply_nonneg _ _))
    exact (congrArg abs (heq.trans (congrArg (fun c => mixedDerivative i j (f z m) q.val - c)
      hrf))).le.trans hb
  refine ⟨hregular, JD, hv, fun k => ?_⟩
  by_cases hk : k = 0
  · subst k
    refine ⟨hv.choose, fun s => ?_⟩
    have hs := hv.choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, ?_⟩
    intro z hz v m hm q i j hij
    have hvalue := hs.choose_spec.2 z hz m hm q i j hij
    have hcost : 0 ≤ hs.choose * T.E0 (T.sample (cell m)) ^ hs.choose *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
      mul_nonneg (mul_nonneg hs.choose_spec.1.le
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) (Real.rpow_nonneg (hH m) _)
    have hweight : parameterGrading S (s + hv.choose) z ≤
        oneHighVariationWeight (parameterGrading S) base (s + hv.choose) z v := by
      simp only [oneHighVariationWeight, Finset.univ_eq_empty, Finset.prod_empty,
        Finset.sum_empty, mul_one, add_zero]
      linarith
    exact (congrArg abs (smoothDirections_D_zero_apply (JD m hm i j q) hz v)).le.trans
      (hvalue.trans (mul_le_mul_of_nonneg_left hweight hcost))
  · have hpos := Nat.pos_of_ne_zero hk
    have hb := hbound k hpos
    refine ⟨hb.choose, fun s => ?_⟩
    have hs := hb.choose_spec s
    refine ⟨hs.choose, hs.choose_spec.1, ?_⟩
    intro z hz v m hm q i j hij
    exact (congrArg abs (hpositive k hpos z hz v m hm q i j)).le.trans
      (hs.choose_spec.2 z hz v m hm q i j hij)

end ContinuousFlexibility.Analysis
