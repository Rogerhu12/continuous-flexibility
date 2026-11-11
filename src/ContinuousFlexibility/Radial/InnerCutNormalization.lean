import ContinuousFlexibility.Radial.InnerTwoCutError
import ContinuousFlexibility.Radial.InnerBufferLocalizedConstruction

/-!
# The physical cut normalization

The common height and Liouville factors cancel exactly from each
normalized radial error entry. Comparing the compression energies with
the positive inward reference energies then costs a fixed constant.
This also applies to the central reference energies with their retained
Liouville drift term.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements
open scoped BigOperators Matrix.Norms.L2Operator

theorem innerFluxHeight_normalization {height si sj ki kj e : ℝ}
    (hh : 0 < height) (hsi : 0 < si) (hsj : 0 < sj)
    (hki : 0 < ki) (hkj : 0 < kj) :
    (height * si * sj * e) /
      sqrt ((height * si ^ 2 * ki) * (height * sj ^ 2 * kj)) =
        e / sqrt (ki * kj) := by
  have hscale : 0 < height * si * sj := mul_pos (mul_pos hh hsi) hsj
  have hs : sqrt ((height * si ^ 2 * ki) * (height * sj ^ 2 * kj)) =
      (height * si * sj) * sqrt (ki * kj) := by
    rw [show (height * si ^ 2 * ki) * (height * sj ^ 2 * kj) =
      (height * si * sj) ^ 2 * (ki * kj) by ring,
      sqrt_mul (sq_nonneg _), sqrt_sq hscale.le]
  rw [hs]
  field_simp [hscale.ne', (sqrt_pos.mpr (mul_pos hki hkj)).ne'] <;> ring

theorem innerCutEnergy_normalized_entry_bound {di dj ki kj M η e : ℝ}
    (hdi : 0 < di) (hdj : 0 < dj) (hki : 0 < ki) (hkj : 0 < kj)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hi : di ≤ M * ki) (hj : dj ≤ M * kj)
    (he : |e / sqrt (di * dj)| ≤ η) :
    |e / sqrt (ki * kj)| ≤ M * η := by
  have hproduct : di * dj ≤ M ^ 2 * (ki * kj) := by
    calc
      di * dj ≤ (M * ki) * (M * kj) :=
        mul_le_mul hi hj hdj.le (mul_nonneg hM hki.le)
      _ = _ := by ring
  have hsD : 0 < sqrt (di * dj) := sqrt_pos.mpr (mul_pos hdi hdj)
  have hsK : 0 < sqrt (ki * kj) := sqrt_pos.mpr (mul_pos hki hkj)
  have hratio : sqrt (di * dj) / sqrt (ki * kj) ≤ M := by
    apply (div_le_iff₀ hsK).mpr
    have h := sqrt_le_sqrt hproduct
    simpa only [sqrt_mul (sq_nonneg M), sqrt_sq hM] using h
  have hratio0 : 0 ≤ sqrt (di * dj) / sqrt (ki * kj) := div_nonneg hsD.le hsK.le
  calc
    |e / sqrt (ki * kj)| =
        |(e / sqrt (di * dj)) * (sqrt (di * dj) / sqrt (ki * kj))| := by
      congr 1
      field_simp [hsD.ne', hsK.ne']
    _ = |e / sqrt (di * dj)| * (sqrt (di * dj) / sqrt (ki * kj)) := by
      rw [abs_mul, abs_of_nonneg hratio0]
    _ ≤ η * M := mul_le_mul he hratio hratio0 hη
    _ = M * η := mul_comm _ _

/-- R09's diagonal comparison transfers its entry estimate to the actual
inward reference energies before either weighted operator norm is taken. -/
theorem innerTwoCutWeightedError_norm_of_compression (D κ W : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) {M R η : ℝ}
    (hD : ∀ i, 0 < D i) (hκ : ∀ i, 0 < κ i) (hW : ∀ i, 0 < W i)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (henergy : ∀ i, D i ≤ M * κ i)
    (hratio : ∀ i k, W i / W k ≤ R)
    (hentry : ∀ i k, |E i k / sqrt (D i * D k)| ≤ η)
    (sign : Bool) :
    ‖innerTwoCutWeightedError κ W E sign‖ ≤ 4 * R * (M * η) :=
  innerTwoCutWeightedError_norm_le κ W E hW hR (mul_nonneg hM hη) hratio
    (fun i k => innerCutEnergy_normalized_entry_bound (hD i) (hD k) (hκ i) (hκ k)
      hM hη (henergy i) (henergy k) (hentry i k)) sign

/-- Large buffer masses leave only a fixed additional Dirichlet cost.
The same inverse constructed by compression is used here. -/
theorem InnerBufferLocalizedData.dirichlet_bound_largeMass
    {B : BufferData} {C K : ℝ} (M : InnerBufferLocalizedData B C K)
    (hC : 0 ≤ C) (hm : ∀ i, 1 ≤ B.mass i) :
    ‖M.dirichlet‖ ≤ B.B₀ + 2 * C := by
  have hmass (i : Fin 2) : (B.mass i)⁻¹ ^ 2 ≤ 1 := by
    have hnonneg : 0 ≤ (B.mass i)⁻¹ := inv_nonneg.mpr (zero_le_one.trans (hm i))
    have hInv : (B.mass i)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one (hm i)
    simpa only [one_pow] using (sq_le_sq₀ hnonneg zero_le_one).mpr hInv
  have hsum : (∑ i : Fin 2, (B.mass i)⁻¹ ^ 2) ≤ 2 := by
    rw [Fin.sum_univ_two]
    linarith only [hmass 0, hmass 1]
  calc
    ‖M.dirichlet‖ ≤ B.B₀ + C * ∑ i, (B.mass i)⁻¹ ^ 2 := M.dirichlet_bound
    _ ≤ B.B₀ + C * 2 := add_le_add (le_refl B.B₀) (mul_le_mul_of_nonneg_left hsum hC)
    _ = _ := by ring

end ContinuousFlexibility.Radial
