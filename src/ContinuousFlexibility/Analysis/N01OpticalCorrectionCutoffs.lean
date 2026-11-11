import ContinuousFlexibility.Analysis.OpticalCollarCutoff

/-!
# An actual uniformly controlled optical correction cutoff family

The family is selected from the actual reference optical collars. Its
transition lies strictly inside each actual negative component, the
reference speed has a fixed coefficient-power lower bound there, and
all cutoff derivatives have fixed coefficient-power upper bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.exists_opticalCorrectionCutoffs
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε) :
    ∃ K A B : ℝ, 0 < K ∧ 0 < A ∧ 0 < B ∧
      ∃ j : ℕ → ℕ, ∃ x δ : ℕ → ℝ, ∃ χ : ℕ → ℝ → ℝ,
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m) ∧
        0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
        (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A ∧
        ∀ r ∈ Icc (x m - δ m) (x m + δ m),
          radialE (D.cellIndex (j m)) ^ (-B) / (2 * (D.b - D.a)) ≤ opticalSpeed D.w r) ∧
      (∀ m, χ m = returnOpticalCutoff (x m) (δ m)) ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Icc (x m - δ m) (x m + δ m)) ∧
      ∀ n : ℕ, ∃ Kₙ : ℝ, 0 < Kₙ ∧ ∀ m r,
        |iteratedDeriv n (χ m) r| ≤
          Kₙ * radialE (D.cellIndex (j m)) ^ (A * n) := by
  classical
  obtain ⟨K₀, A₀, B, hK₀, hA₀, hB, hcollar⟩ := hN01.reference_opticalCollars
  choose j hj x hx using hcollar
  let δ : ℕ → ℝ := fun m =>
    (radialE (D.cellIndex (j m)) ^ (-B) / (C.right m - C.left m)) ^ 2 /
      (4 * (K₀ * radialE (D.cellIndex (j m)) ^ A₀ + 1))
  let χ : ℕ → ℝ → ℝ := fun m => returnOpticalCutoff (x m) (δ m)
  let A : ℝ := A₀ + 2 * B
  let K : ℝ := 4 * (K₀ + 1) * (D.b - D.a) ^ 2
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  obtain ⟨Q, hdata⟩ := hN01.1.1
  have hgeom : RadialProfileGeometry D := hdata.1
  have hR : 0 < D.b - D.a := sub_pos.mpr hgeom.2.1
  have hK : 0 < K := by
    dsimp only [K]
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (sq_pos_of_pos hR)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hE (m : ℕ) : 1 ≤ radialE (D.cellIndex (j m)) := by
    have hn : 0 ≤ (D.cellIndex (j m) : ℝ) := Nat.cast_nonneg _
    have he : 1 ≤ Real.exp 1 + (D.cellIndex (j m) : ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans
        (le_add_of_nonneg_right hn)
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (Real.rpow_nonneg hn _) (Real.log_nonneg he))
  have hδdata (m : ℕ) :
      0 < δ m ∧ C.left m < x m - δ m ∧ x m + δ m < C.right m ∧
      ∀ r ∈ Icc (x m - δ m) (x m + δ m),
        radialE (D.cellIndex (j m)) ^ (-B) / (2 * (C.right m - C.left m)) ≤
          opticalSpeed D.w r := hx m
  have hL (m : ℕ) : 0 < C.right m - C.left m := sub_pos.mpr (hC.1 m).2.1
  have hLR (m : ℕ) : C.right m - C.left m ≤ D.b - D.a := by
    linarith [(hC.1 m).1, (hC.1 m).2.2]
  have hwidth (m : ℕ) : (δ m)⁻¹ ≤ K * radialE (D.cellIndex (j m)) ^ A :=
    opticalCollar_width_inv_bound (hE m) hK₀ hA₀.le (hL m) (hLR m)
  refine ⟨K, A, B, hK, hA, hB, j, x, δ, χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨hj m, (hδdata m).1, (hδdata m).2.1, (hδdata m).2.2.1, hwidth m, ?_⟩
    intro r hr
    have hτ : 0 ≤ radialE (D.cellIndex (j m)) ^ (-B) :=
      Real.rpow_nonneg (zero_le_one.trans (hE m)) _
    exact (div_le_div_of_nonneg_left hτ
      (mul_pos (by norm_num) (hL m))
      (mul_le_mul_of_nonneg_left (hLR m) (by norm_num))).trans ((hδdata m).2.2.2 r hr)
  · intro m
    rfl
  · intro m
    exact ⟨returnOpticalCutoff_contDiff _ _, returnOpticalCutoff_mem_Icc _ _⟩
  · intro m
    refine ⟨returnOpticalCutoff_eventually_zero (hδdata m).1 (hδdata m).2.1,
      returnOpticalCutoff_eventually_one (hδdata m).1 (hδdata m).2.2.1, ?_⟩
    exact closure_minimal (returnOpticalCutoff_deriv_support_subset (x m) (hδdata m).1)
      isClosed_Icc
  · intro n
    obtain ⟨Kₙ, hKₙ, hjet⟩ := returnOpticalCutoff_iteratedDeriv_bound n
    refine ⟨Kₙ * K ^ n, mul_pos hKₙ (pow_pos hK n), fun m r => ?_⟩
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (hδdata m).1.le) (hwidth m) n
    calc
      _ ≤ Kₙ * ((δ m)⁻¹) ^ n := hjet (x m) (δ m) (hδdata m).1 r
      _ ≤ Kₙ * (K * radialE (D.cellIndex (j m)) ^ A) ^ n :=
        mul_le_mul_of_nonneg_left hpow hKₙ.le
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans (hE m))]
        ring

end ContinuousFlexibility.Statements
