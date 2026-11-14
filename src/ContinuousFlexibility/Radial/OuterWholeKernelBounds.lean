module

public import ContinuousFlexibility.Radial.OuterFundamentalKernel
public import ContinuousFlexibility.Radial.OuterKernelEnvelopeAlgebra

/-!
# Pointwise bounds for the actual whole Green kernel

The core blocks follow directly from the actual normalized homogeneous
pair. On the tail the proved Dirichlet-plus-rank-one identity gives one
common bound. It remains valid when the natural entrance value vanishes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set

variable {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}

theorem OuterFundamentalStatePair.kernel_core_abs_le
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam K x y : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hU : ∀ t ∈ Icc a c, |F.U t| ≤ K) (hV : ∀ t ∈ Icc a c, |F.V t| ≤ K)
    (hx : x ∈ Icc a c) (hy : y ∈ Icc a c) :
    |outerGreenKernel lam F.U F.V x y| ≤ lam⁻¹ * K ^ 2 := by
  have hmin : min x y ∈ Icc a c := ⟨le_min hx.1 hy.1, (min_le_left _ _).trans hx.2⟩
  have hmax : max x y ∈ Icc a c := ⟨hx.1.trans (le_max_left _ _), max_le hx.2 hy.2⟩
  rw [outerGreenKernel, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [pow_two] using mul_le_mul (hU _ hmin) (hV _ hmax) (abs_nonneg _) hK)
    (inv_nonneg.mpr hlam.le)

theorem OuterFundamentalStatePair.kernel_core_tail_abs_le
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam K x y : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1)
    (hU : ∀ t ∈ Icc a c, |F.U t| ≤ K) (hV : ∀ t ∈ Icc a c, |F.V t| ≤ K)
    (hx : x ∈ Icc a c) (hy : y ∈ Ico c b) :
    |outerGreenKernel lam F.U F.V x y| ≤ (lam⁻¹ * K ^ 2) * |P y| := by
  rw [outerGreenKernel_of_le (hx.2.trans hy.1), F.V_tail_factor hcb hPc y hy,
    abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
  calc
    _ = lam⁻¹ * ((|F.U x| * |F.V c|) * |P y|) := by ring
    _ ≤ lam⁻¹ * ((K * K) * |P y|) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (hU x hx) (hV c ⟨hac, le_rfl⟩) (abs_nonneg _) hK) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)
    _ = _ := by ring

/-- One bound covers core/core, both mixed blocks, and tail/tail.
The tail term is the actual unit-flux Dirichlet kernel. -/
theorem OuterFundamentalStatePair.kernel_blocks_abs_le
    (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam K x y ex ey d : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam)
    (hU : ∀ t ∈ Icc a c, |F.U t| ≤ K) (hV : ∀ t ∈ Icc a c, |F.V t| ≤ K)
    (hex : 0 ≤ ex) (hey : 0 ≤ ey) (hd : 0 ≤ d)
    (hx : (x ∈ Icc a c ∧ 1 ≤ ex) ∨ (x ∈ Ico c b ∧ |P x| ≤ ex))
    (hy : (y ∈ Icc a c ∧ 1 ≤ ey) ∨ (y ∈ Ico c b ∧ |P y| ≤ ey))
    (hdirichlet : x ∈ Ico c b → y ∈ Ico c b → |Q (min x y) * P (max x y)| ≤ d) :
    |outerGreenKernel lam F.U F.V x y| ≤ d + (lam⁻¹ * K ^ 2) * ex * ey := by
  let M := lam⁻¹ * K ^ 2
  have hM : 0 ≤ M := mul_nonneg (inv_nonneg.mpr hlam.le) (sq_nonneg K)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · calc
      _ ≤ M := F.kernel_core_abs_le hlam hK hU hV hx.1 hy.1
      _ ≤ M * (ex * ey) := le_mul_of_one_le_right hM
        (one_le_mul_of_one_le_of_one_le hx.2 hy.2)
      _ = M * ex * ey := by ring
      _ ≤ _ := le_add_of_nonneg_left hd
  · calc
      _ ≤ M * |P y| := F.kernel_core_tail_abs_le hlam hK hac hcb hPc hU hV hx.1 hy.1
      _ ≤ M * ey := mul_le_mul_of_nonneg_left hy.2 hM
      _ ≤ (M * ex) * ey := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hM hx.2) hey
      _ ≤ _ := le_add_of_nonneg_left hd
  · have hs : |outerGreenKernel lam F.U F.V x y| =
        |outerGreenKernel lam F.U F.V y x| := congrArg abs (outerGreenKernel_symm _ _ _ _ _)
    calc
      _ = |outerGreenKernel lam F.U F.V y x| := hs
      _ ≤ M * |P x| := F.kernel_core_tail_abs_le hlam hK hac hcb hPc hU hV hy.1 hx.1
      _ ≤ M * ex := mul_le_mul_of_nonneg_left hx.2 hM
      _ ≤ (M * ex) * ey := le_mul_of_one_le_right (mul_nonneg hM hex) hy.2
      _ ≤ _ := le_add_of_nonneg_left hd
  · rw [F.green_tail_decomposition_unit_flux hlam.ne' hac hcb hPc hQc hflux hx.1 hy.1]
    calc
      _ ≤ |Q (min x y) * P (max x y)| +
          |outerGreenKernel lam F.U F.V c c * (P x * P y)| := abs_add_le _ _
      _ ≤ d + M * (ex * ey) := add_le_add (hdirichlet hx.1 hy.1) (by
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (F.kernel_core_abs_le hlam hK hU hV ⟨hac, le_rfl⟩ ⟨hac, le_rfl⟩)
          (mul_le_mul hx.2 hy.2 (abs_nonneg _) hex)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM)
      _ = _ := by ring

end ContinuousFlexibility.Radial
