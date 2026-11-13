import ContinuousFlexibility.Analysis.N04SourceColumnsLinear

/-! Addition of actual current-minus-reference towers. -/

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

theorem n04SourceColumns_add_cost {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ E H u v w x y : ℝ,
      1 ≤ E → 0 ≤ H → 0 ≤ u → 0 ≤ v → u ≤ w → v ≤ w →
      |x| ≤ A * E ^ A * H * u → |y| ≤ B * E ^ B * H * v →
      |x + y| ≤ C * E ^ C * H * w := by
  let M : ℝ := max A B
  have hM : 0 < M := lt_max_of_lt_left hA
  have hp := coefficientEnvelope_pack (2 * M) M
  refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
  intro E H u v w x y hE hH hu hv huw hvw hx hy
  have hx' := n04SourceColumns_cost_raise hA (le_max_left _ _) hE hH hu huw hx
  have hy' := n04SourceColumns_cost_raise hB (le_max_right _ _) hE hH hv hvw hy
  calc
    |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ M * E ^ M * H * w + M * E ^ M * H * w := add_le_add hx' hy'
    _ = (2 * M * E ^ M) * H * w := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hp.choose_spec.2 E hE) hH) (hu.trans huw)

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

theorem N04SourceReferenceData.sourceColumns_add
    (hf : N04SourceReferenceData T cell f₀) (hg : N04SourceReferenceData T cell g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04SourceReferenceData T cell (fun m q => f₀ m q + g₀ m q) := by
  refine ⟨fun m => ⟨(hf.1 m).1.add (hg.1 m).1,
    fun q hq => congrArg₂ (· + ·) ((hf.1 m).2 q hq) ((hg.1 m).2 q hq)⟩, ?_⟩
  intro s
  have hfs := hf.2 s
  have hgs := hg.2 s
  have hp := n04SourceColumns_add_cost hfs.choose_spec.1 hgs.choose_spec.1
  refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
  intro m q hq i j hij
  rw [n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.1 m).1 (hg.1 m).1 i j hq]
  have hh := hp.choose_spec.2 (T.E0 (T.sample (cell m))) 1 1 1 1 _ _
    (hE m) zero_le_one zero_le_one zero_le_one le_rfl le_rfl
    (by simpa only [mul_one] using hfs.choose_spec.2 m q hq i j hij)
    (by simpa only [mul_one] using hgs.choose_spec.2 m q hq i j hij)
  simpa only [mul_one] using hh

/-- Addition selects its losses and constants before the piece and point. -/
theorem CurrentJetDataOn.sourceColumns_add
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hg : CurrentJetDataOn S T cell (fun _ => True) base ε g g₀)
    (hf₀ : N04SourceReferenceData T cell f₀) (hg₀ : N04SourceReferenceData T cell g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m q => f z m q + g z m q) (fun m q => f₀ m q + g₀ m q) := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hpmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  have he (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
      (m i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f z m y - f₀ m y) q.val +
          mixedDerivative i j (fun y => g z m y - g₀ m y) q.val =
        mixedDerivative i j (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val := by
    rw [← n07a_mixedDerivative_add_on hU
      ((hf.1 z hz m trivial).1.sub (hf₀.1 m).1)
      ((hg.1 z hz m trivial).1.sub (hg₀.1 m).1) i j q.property]
    congr 2
    funext y
    ring
  let J : ∀ m i j (q : unitStrip), SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => mixedDerivative i j
        (fun y => (f z m y + g z m y) - (f₀ m y + g₀ m y)) q.val) :=
    fun m i j q => (smoothDirectionsAdd (hf.2.choose m i j q)
      (hg.2.choose m i j q)).congr (fun z hz => he z hz m i j q)
  have hJ (m i j : ℕ) (q : unitStrip) (k : ℕ) (z : Parameter S)
      (v : Fin k → Parameter S) :
      (J m i j q).D k z v = (hf.2.choose m i j q).D k z v +
        (hg.2.choose m i j q).D k z v := rfl
  refine ⟨fun z hz m _ => ⟨(hf.1 z hz m trivial).1.add (hg.1 z hz m trivial).1,
    fun q hq => congrArg₂ (· + ·) ((hf.1 z hz m trivial).2 q hq)
      ((hg.1 z hz m trivial).2 q hq)⟩, J, ?_, ?_⟩
  · have hfv := hf.2.choose_spec.1
    have hgv := hg.2.choose_spec.1
    refine ⟨max hfv.choose hgv.choose, fun s => ?_⟩
    have hfs := hfv.choose_spec s
    have hgs := hgv.choose_spec s
    have hp := n04SourceColumns_add_cost hfs.choose_spec.1 hgs.choose_spec.1
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro z hz m _ q i j hij
    have hb := hp.choose_spec.2 _ _ _ _ _ _ _ (hE m) (Real.rpow_nonneg (hH m) _)
      (apply_nonneg _ _) (apply_nonneg _ _)
      (hpmono (Nat.add_le_add_left (le_max_left _ _) s) z)
      (hpmono (Nat.add_le_add_left (le_max_right _ _) s) z)
      (hfs.choose_spec.2 z hz m trivial q i j hij)
      (hgs.choose_spec.2 z hz m trivial q i j hij)
    exact (congrArg abs (he z hz m i j q).symm).trans_le hb
  · intro k
    have hft := hf.2.choose_spec.2 k
    have hgt := hg.2.choose_spec.2 k
    refine ⟨max hft.choose hgt.choose, fun s => ?_⟩
    have hfs := hft.choose_spec s
    have hgs := hgt.choose_spec s
    have hp := n04SourceColumns_add_cost hfs.choose_spec.1 hgs.choose_spec.1
    refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
    intro z hz v m _ q i j hij
    have hb := hp.choose_spec.2 _ _ _ _ _ _ _ (hE m) (Real.rpow_nonneg (hH m) _)
      (oneHighVariationWeight_nonneg _ _ _ _ _) (oneHighVariationWeight_nonneg _ _ _ _ _)
      (oneHighVariationWeight_mono hpmono le_rfl
        (Nat.add_le_add_left (le_max_left _ _) s) z v)
      (oneHighVariationWeight_mono hpmono le_rfl
        (Nat.add_le_add_left (le_max_right _ _) s) z v)
      (hfs.choose_spec.2 z hz v m trivial q i j hij)
      (hgs.choose_spec.2 z hz v m trivial q i j hij)
    exact (congrArg abs (hJ m i j q k z v)).trans_le hb

end ContinuousFlexibility.Analysis
