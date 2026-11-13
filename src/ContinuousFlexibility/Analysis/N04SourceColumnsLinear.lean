import ContinuousFlexibility.Analysis.N04SourceColumnsData

/-!
# Linear operations on the scalar source interfaces

Equalities are required only on the actual open strip.  Fixed scalar
factors may depend on the piece and have a material coefficient envelope.
All operations retain the original parameter neighborhood.
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

theorem n04SourceColumns_cost_raise {B B' E H u v x : ℝ}
    (hB : 0 < B) (hBB : B ≤ B') (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hu : 0 ≤ u) (huv : u ≤ v) (hx : x ≤ B * E ^ B * H * u) :
    x ≤ B' * E ^ B' * H * v := by
  have he : 0 ≤ E := zero_le_one.trans hE
  have hc : B * E ^ B ≤ B' * E ^ B' :=
    mul_le_mul hBB (Real.rpow_le_rpow_of_exponent_le hE hBB)
      (Real.rpow_nonneg he _) (hB.le.trans hBB)
  exact hx.trans (mul_le_mul (mul_le_mul_of_nonneg_right hc hH) huv hu
    (mul_nonneg (mul_nonneg (hB.le.trans hBB) (Real.rpow_nonneg he _)) hH))

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

/-- Equality on the open strip identifies every genuine spatial and
parameter derivative of the same difference. -/
theorem CurrentJetDataOn.sourceColumns_congr
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (he : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m, EqOn (f z m) (g z m) unitStrip)
    (he₀ : ∀ m, EqOn (f₀ m) (g₀ m) unitStrip) :
    CurrentJetDataOn S T cell (fun _ => True) base ε g g₀ := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have heJ (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f z m y - f₀ m y) q.val =
        mixedDerivative i j (fun y => g z m y - g₀ m y) q.val :=
    n07a_mixedDerivative_eqOn hU
      (fun _ hy => congrArg₂ (· - ·) (he z hz m hy) (he₀ m hy)) i j q.property
  refine ⟨?_, fun m i j q => (hf.2.choose m i j q).congr (fun z hz => heJ z hz m i j q),
    ?_, ?_⟩
  · intro z hz m _
    refine ⟨(hf.1 z hz m trivial).1.congr (fun _ hq => (he z hz m hq).symm), ?_⟩
    intro q hq
    have hq' : q + (0, Real.pi) ∈ unitStrip := by
      exact ⟨by simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hq.1, mem_univ _⟩
    rw [← he z hz m hq', (hf.1 z hz m trivial).2 q hq, he z hz m hq]
  · have hv := hf.2.choose_spec.1
    refine ⟨hv.choose, fun s => ⟨(hv.choose_spec s).choose,
      (hv.choose_spec s).choose_spec.1, ?_⟩⟩
    intro z hz m _ q i j hij
    exact (congrArg abs (heJ z hz m i j q).symm).trans_le
      ((hv.choose_spec s).choose_spec.2 z hz m trivial q i j hij)
  · have ht := hf.2.choose_spec.2
    exact fun k => ⟨(ht k).choose, fun s => ⟨((ht k).choose_spec s).choose,
      ((ht k).choose_spec s).choose_spec.1,
      fun z hz v m _ q i j hij =>
        ((ht k).choose_spec s).choose_spec.2 z hz v m trivial q i j hij⟩⟩

/-- Reference data also depend only on the open-strip germ. -/
theorem N04SourceReferenceData.sourceColumns_congr
    (hf : N04SourceReferenceData T cell f₀) (he : ∀ m, EqOn (f₀ m) (g₀ m) unitStrip) :
    N04SourceReferenceData T cell g₀ := by
  refine ⟨fun m => ⟨(hf.1 m).1.congr (fun _ hq => (he m hq).symm), ?_⟩,
    fun s => ⟨(hf.2 s).choose, (hf.2 s).choose_spec.1, ?_⟩⟩
  · intro q hq
    have hq' : q + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.fst_add, Prod.fst_zero, add_zero] using hq.1, mem_univ _⟩
    rw [← he m hq', (hf.1 m).2 q hq, he m hq]
  · intro m q hq i j hij
    exact (congrArg abs
      (n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ) (he m) i j hq).symm).trans_le
        ((hf.2 s).choose_spec.2 m q hq i j hij)

/-- A fixed reference family has identically zero differences. -/
theorem N04SourceReferenceData.sourceColumns_static
    (hf : N04SourceReferenceData T cell f₀)
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell (fun _ => True) base ε (fun _ => f₀) f₀ := by
  have he (m i j : ℕ) (q : unitStrip) (z : Parameter S) :
      (0 : ℝ) = mixedDerivative i j (fun y => f₀ m y - f₀ m y) q.val := by
    simp only [sub_self, mixedDerivative_fun_zero]
  refine ⟨fun _ _ m _ => hf.1 m,
    fun m i j q => (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
      (0 : ℝ)).congr (fun z _ => he m i j q z), ⟨0, fun s => ⟨1, zero_lt_one, ?_⟩⟩,
    fun k => ⟨0, fun s => ⟨1, zero_lt_one, ?_⟩⟩⟩
  · intro z hz m _ q i j hij
    rw [← he m i j q z, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (hE m) _))
      (Real.rpow_nonneg (hH m) _)) (apply_nonneg _ _)
  · intro z hz v m _ q i j hij
    have hzero : (smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
        (0 : ℝ)).D k z v = 0 := by
      by_cases hk : k = 0
      · subst k
        exact smoothDirections_D_zero_apply _ hz v
      · exact smoothDirections_D_constant _ (Nat.pos_of_ne_zero hk) hz v
    change |(smoothDirections_constant (isOpen_sectorNeighborhood S base ε ε)
      (0 : ℝ)).D k z v| ≤ _
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (hE m) _))
      (Real.rpow_nonneg (hH m) _)) (oneHighVariationWeight_nonneg _ _ _ _ _)

/-- A scalar depending only on the piece costs one coefficient envelope. -/
theorem CurrentJetDataOn.sourceColumns_constMul
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (c : ℕ → ℝ) (hc : ∃ A : ℝ, 0 < A ∧ ∀ m,
      |c m| ≤ A * T.E0 (T.sample (cell m)) ^ A) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m q => c m * f z m q) (fun m q => c m * f₀ m q) := by
  have he (m i j : ℕ) (q : PolarPoint) (z : Parameter S) :
      c m * mixedDerivative i j (fun y => f z m y - f₀ m y) q =
        mixedDerivative i j (fun y => c m * f z m y - c m * f₀ m y) q := by
    rw [show (fun y => c m * f z m y - c m * f₀ m y) =
      (fun y => c m * (f z m y - f₀ m y)) from funext (fun _ => (mul_sub _ _ _).symm)]
    exact (mixedDerivative_const_mul _ _ _ _ _).symm
  let J : ∀ m i j (q : unitStrip), SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j (fun y => c m * f z m y - c m * f₀ m y) q.val) :=
    fun m i j q => (smoothDirections_postcompCLM (hf.2.choose m i j q)
      ((c m) • ContinuousLinearMap.id ℝ ℝ)).congr (fun z _ => he m i j q.val z)
  have hJ (m i j : ℕ) (q : unitStrip) (k : ℕ) (z : Parameter S)
      (v : Fin k → Parameter S) :
      (J m i j q).D k z v = c m * (hf.2.choose m i j q).D k z v := by
    simp only [J, SmoothDirections.congr, smoothDirections_postcompCLM_D_apply,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  let A : ℝ := hc.choose
  have hA : 0 < A := hc.choose_spec.1
  have hpack (B : ℝ) (hB : 0 < B) : ∃ R : ℝ, 0 < R ∧
      ∀ m u x, 0 ≤ u → |x| ≤ B * T.E0 (T.sample (cell m)) ^ B *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * u →
      |c m * x| ≤ R * T.E0 (T.sample (cell m)) ^ R *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * u := by
    have hp := coefficientEnvelope_pack (A * B) (A + B)
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro m u x hu hx
    have he0 : 0 < T.E0 (T.sample (cell m)) := zero_lt_one.trans_le (hE m)
    have hh : 0 ≤ T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg (hH m) _
    calc
      |c m * x| = |c m| * |x| := abs_mul _ _
      _ ≤ (A * T.E0 (T.sample (cell m)) ^ A) *
          (B * T.E0 (T.sample (cell m)) ^ B *
            T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * u) :=
        mul_le_mul (hc.choose_spec.2 m) hx (abs_nonneg _)
          (mul_nonneg hA.le (Real.rpow_nonneg he0.le _))
      _ = (A * B * T.E0 (T.sample (cell m)) ^ (A + B)) *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) * u := by
        rw [Real.rpow_add he0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hp.choose_spec.2 _ (hE m)) hh) hu
  refine ⟨fun z hz m _ => ⟨contDiffOn_const.mul (hf.1 z hz m trivial).1,
    fun q hq => congrArg (fun x => c m * x) ((hf.1 z hz m trivial).2 q hq)⟩, J, ?_, ?_⟩
  · have hv := hf.2.choose_spec.1
    refine ⟨hv.choose, fun s => ?_⟩
    have hs := hv.choose_spec s
    have hp := hpack hs.choose hs.choose_spec.1
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro z hz m _ q i j hij
    exact (congrArg abs (he m i j q.val z).symm).trans_le
      (hp.choose_spec.2 m _ _ (apply_nonneg _ _)
        (hs.choose_spec.2 z hz m trivial q i j hij))
  · intro k
    have ht := hf.2.choose_spec.2 k
    refine ⟨ht.choose, fun s => ?_⟩
    have hs := ht.choose_spec s
    have hp := hpack hs.choose hs.choose_spec.1
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro z hz v m _ q i j hij
    exact (congrArg abs (hJ m i j q k z v)).trans_le
      (hp.choose_spec.2 m _ _ (oneHighVariationWeight_nonneg _ _ _ _ _)
        (hs.choose_spec.2 z hz v m trivial q i j hij))

end ContinuousFlexibility.Analysis
