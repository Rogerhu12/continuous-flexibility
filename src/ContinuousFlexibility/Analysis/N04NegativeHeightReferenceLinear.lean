import ContinuousFlexibility.Analysis.N04NegativeHeightLinearSpatial

/-! Addition, angular differentiation and equality of fixed reference data. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {T : MaterialData} {cell : ℕ → ℕ} {P : ℕ → Prop}
  {f₀ g₀ : ℕ → PolarPoint → ℝ}

theorem N04HeightReferenceDataOn.height_add
    (hf : N04HeightReferenceDataOn T cell P f₀)
    (hg : N04HeightReferenceDataOn T cell P g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04HeightReferenceDataOn T cell P (fun m q => f₀ m q + g₀ m q) := by
  refine ⟨fun m hm => ⟨(hf.1 m hm).1.add (hg.1 m hm).1,
    fun q hq => congrArg₂ (fun x y : ℝ => x + y)
      ((hf.1 m hm).2 q hq) ((hg.1 m hm).2 q hq)⟩, fun s => ?_⟩
  have hfs := hf.2 s
  have hgs := hg.2 s
  refine ⟨hfs.choose + hgs.choose, add_pos hfs.choose_spec.1 hgs.choose_spec.1,
    fun m hm q hq i j hij => ?_⟩
  rw [n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.1 m hm).1 (hg.1 m hm).1 i j hq]
  simpa only [mul_one] using n04NegativeHeight_add_cost
    hfs.choose_spec.1.le hgs.choose_spec.1.le (hE m)
    (H := 1) (X := 1) (Y := 1) (W := 1)
    zero_le_one zero_le_one zero_le_one le_rfl le_rfl
    (by simpa only [mul_one] using hfs.choose_spec.2 m hm q hq i j hij)
    (by simpa only [mul_one] using hgs.choose_spec.2 m hm q hq i j hij)

theorem N04HeightReferenceDataOn.height_angularPartial
    (hf : N04HeightReferenceDataOn T cell P f₀) :
    N04HeightReferenceDataOn T cell P (fun m => angularPartial (f₀ m)) := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m hm => ⟨n04NegativeHeight_angularPartial_smooth (hf.1 m hm).1,
    n04NegativeHeight_angularPartial_periodic (hf.1 m hm).1
      (hf.1 m hm).2⟩, fun s => ?_⟩
  have h := hf.2 (s + 1)
  refine ⟨h.choose, h.choose_spec.1, fun m hm q hq i j hij => ?_⟩
  rw [mixedDerivative_angularPartial hU (hf.1 m hm).1 i j hq]
  exact h.choose_spec.2 m hm q hq i (j + 1) (by omega)

theorem N04HeightReferenceDataOn.height_congr
    (hf : N04HeightReferenceDataOn T cell P f₀)
    (hfg : ∀ m, P m → EqOn (f₀ m) (g₀ m) unitStrip) :
    N04HeightReferenceDataOn T cell P g₀ := by
  have hU : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  refine ⟨fun m hm => ⟨(hf.1 m hm).1.congr (fun q hq => (hfg m hm hq).symm), ?_⟩,
    fun s => ?_⟩
  · intro q hq
    have hs : q + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
    exact (hfg m hm hs).symm.trans (((hf.1 m hm).2 q hq).trans (hfg m hm hq))
  · have h := hf.2 s
    refine ⟨h.choose, h.choose_spec.1, fun m hm q hq i j hij => ?_⟩
    exact (congrArg abs (n07a_mixedDerivative_eqOn hU (hfg m hm) i j hq).symm).trans_le
      (h.choose_spec.2 m hm q hq i j hij)

/-- A piecewise constant reference scalar only needs its scalar
coefficient-envelope bound. -/
theorem n04HeightReferenceDataOn_pieceConstant (c : ℕ → ℝ)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hc : ∃ B : ℝ, 0 < B ∧ ∀ m, P m → |c m| ≤ B * T.E0 (T.sample (cell m)) ^ B) :
    N04HeightReferenceDataOn T cell P (fun m _ => c m) := by
  refine ⟨fun _ _ => ⟨contDiffOn_const, fun _ _ => rfl⟩,
    fun s => ⟨hc.choose, hc.choose_spec.1, fun m hm q hq i j hij => ?_⟩⟩
  have hconst : |mixedDerivative i j (fun _ : PolarPoint => c m) q| ≤ |c m| := by
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        simp only [spaces_mixedDerivative_zero, le_refl]
      · simp [mixedDerivative, iteratedDeriv_const, hj]
    · simp [mixedDerivative, iteratedDeriv_const, hi]
  exact hconst.trans (hc.choose_spec.2 m hm)

end ContinuousFlexibility.Analysis
