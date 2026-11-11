import ContinuousFlexibility.Analysis.SpacesSequenceRetraction
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Spectral bands in square-summable Banach families

The masks and regrouping result in this file do not depend on the circle.
They apply equally to Fourier coefficients in one or several variables and
to any partition of a spectral index set into countably many bands.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ENNReal

variable {ι : Type*} {B : Type*}
variable [NormedAddCommGroup B]

local instance spacesCircleSpectralDecidable : DecidableEq ι := Classical.decEq ι

private def lpSpectralMaskFun (s : Set ι) (u : lp (fun _ : ι => B) 2) : lp (fun _ : ι => B) 2 :=
  ⟨s.indicator u, (lp.memℓp u).mono' (by
    intro i
    by_cases hi : i ∈ s
    · simp only [Set.indicator_of_mem hi, le_refl]
    · simp only [Set.indicator_of_notMem hi, norm_zero, norm_nonneg])⟩

private theorem lpSpectralMaskFun_apply (s : Set ι) (u : lp (fun _ : ι => B) 2) (i : ι) :
    lpSpectralMaskFun s u i = s.indicator u i := rfl

private theorem lpSpectralMaskFun_norm_le (s : Set ι) (u : lp (fun _ : ι => B) 2) :
    ‖lpSpectralMaskFun s u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  change ‖s.indicator u i‖ ≤ ‖u i‖
  by_cases hi : i ∈ s
  · simp only [Set.indicator_of_mem hi, le_refl]
  · simp only [Set.indicator_of_notMem hi, norm_zero, norm_nonneg]

variable [NormedSpace ℝ B]

private def lpSpectralMaskLinear (s : Set ι) : lp (fun _ : ι => B) 2 →ₗ[ℝ] lp (fun _ : ι => B) 2 where
  toFun := lpSpectralMaskFun s
  map_add' := by
    intro u v
    apply lp.ext
    funext i
    change s.indicator (u + v) i = s.indicator u i + s.indicator v i
    by_cases hi : i ∈ s
    · simp only [Set.indicator_of_mem hi, lp.coeFn_add, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hi, add_zero]
  map_smul' := by
    intro c u
    apply lp.ext
    funext i
    change s.indicator (c • u) i = c • s.indicator u i
    by_cases hi : i ∈ s
    · simp only [Set.indicator_of_mem hi, lp.coeFn_smul, Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hi, smul_zero]

/-- A contractive projection onto an arbitrary set of spectral coordinates. -/
def lpSpectralMask (s : Set ι) : lp (fun _ : ι => B) 2 →L[ℝ] lp (fun _ : ι => B) 2 :=
  (lpSpectralMaskLinear s).mkContinuous 1 (fun u => by
    change ‖lpSpectralMaskFun s u‖ ≤ 1 * ‖u‖
    rw [one_mul]
    exact lpSpectralMaskFun_norm_le s u)

theorem lpSpectralMask_apply (s : Set ι) (u : lp (fun _ : ι => B) 2) (i : ι) :
    lpSpectralMask s u i = s.indicator u i := rfl

theorem lpSpectralMask_norm_le (s : Set ι) (u : lp (fun _ : ι => B) 2) :
    ‖lpSpectralMask s u‖ ≤ ‖u‖ := lpSpectralMaskFun_norm_le s u

theorem lpSpectralMask_idempotent (s : Set ι) (u : lp (fun _ : ι => B) 2) :
    lpSpectralMask s (lpSpectralMask s u) = lpSpectralMask s u := by
  apply lp.ext
  funext i
  by_cases hi : i ∈ s
  · simp only [lpSpectralMask_apply, Set.indicator_of_mem hi]
  · simp only [lpSpectralMask_apply, Set.indicator_of_notMem hi]

theorem lpSpectralMask_hasSum_single (s : Set ι) (u : lp (fun _ : ι => B) 2) :
    HasSum (fun i : s => lp.single 2 i.val (u i.val)) (lpSpectralMask s u) := by
  classical
  apply (hasSum_subtype_iff_indicator (s := s)
    (f := fun i : ι => lp.single 2 i (u i))).mpr
  convert lp.hasSum_single ENNReal.ofNat_ne_top (lpSpectralMask s u) using 1
  funext i
  by_cases hi : i ∈ s
  · simp only [Set.indicator_of_mem hi, lpSpectralMask_apply]
  · simp only [Set.indicator_of_notMem hi, lpSpectralMask_apply, lp.single_zero]

/-- Spectral band projection for any assignment of indices to natural-number bands. -/
def lpSpectralBand (band : ι → ℕ) (k : ℕ) : lp (fun _ : ι => B) 2 →L[ℝ] lp (fun _ : ι => B) 2 :=
  lpSpectralMask (band ⁻¹' {k})

theorem lpSpectralBand_apply (band : ι → ℕ) (k : ℕ) (u : lp (fun _ : ι => B) 2) (i : ι) :
    lpSpectralBand band k u i = if band i = k then u i else 0 := by
  classical
  by_cases hi : band i = k <;> simp [lpSpectralBand, lpSpectralMask_apply, hi]

theorem lpSpectralBand_norm_le (band : ι → ℕ) (k : ℕ) (u : lp (fun _ : ι => B) 2) :
    ‖lpSpectralBand band k u‖ ≤ ‖u‖ := lpSpectralMask_norm_le _ u

/-- All bands reconstruct the original vector, in the actual Banach norm.
No finiteness of the individual bands is required. -/
theorem hasSum_lpSpectralBand [CompleteSpace B]
    (band : ι → ℕ) (u : lp (fun _ : ι => B) 2) : HasSum (fun k => lpSpectralBand band k u) u := by
  have h := (lp.hasSum_single ENNReal.ofNat_ne_top u).tsum_fiberwise band
  have he (k : ℕ) :
      (∑' i : band ⁻¹' {k}, lp.single 2 i.val (u i.val)) = lpSpectralBand band k u :=
    (lpSpectralMask_hasSum_single (band ⁻¹' {k}) u).tsum_eq
  simpa only [he] using h

section Diagonal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A coordinatewise estimate gives the corresponding spectral-band norm
estimate, including when the comparison coefficients live in another Banach space. -/
theorem lpSpectralBand_norm_le_of_coordinate_bound
    (band : ι → ℕ) (k : ℕ) (u : lp (fun _ : ι => B) 2)
    (v : lp (fun _ : ι => F) 2) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, band i = k → ‖u i‖ ≤ C * ‖v i‖) :
    ‖lpSpectralBand band k u‖ ≤ C * ‖v‖ := by
  have hnorm : ‖lpSpectralBand band k u‖ ≤ ‖C • v‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    rw [lpSpectralBand_apply]
    by_cases hi : band i = k
    · simpa only [ite_eq_left hi, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hC] using h i hi
    · simp only [ite_eq_right hi, norm_zero, norm_nonneg]
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hnorm

private def lpSpectralDiagonalFun (L : ι → B →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖) (u : lp (fun _ : ι => B) 2) :
    lp (fun _ : ι => F) 2 :=
  ⟨fun i => L i (u i), (lp.memℓp (C • u)).mono' (by
    intro i
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hC] using hL i (u i))⟩

private theorem lpSpectralDiagonalFun_apply (L : ι → B →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖) (u : lp (fun _ : ι => B) 2) (i : ι) :
    lpSpectralDiagonalFun L hC hL u i = L i (u i) := rfl

private theorem lpSpectralDiagonalFun_norm_le (L : ι → B →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖)
    (u : lp (fun _ : ι => B) 2) :
    ‖lpSpectralDiagonalFun L hC hL u‖ ≤ C * ‖u‖ := by
  have hnorm : ‖lpSpectralDiagonalFun L hC hL u‖ ≤ ‖C • u‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    simpa only [lpSpectralDiagonalFun_apply, lp.coeFn_smul, Pi.smul_apply,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hL i (u i)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using hnorm

private def lpSpectralDiagonalLinear (L : ι → B →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖) :
    lp (fun _ : ι => B) 2 →ₗ[ℝ] lp (fun _ : ι => F) 2 where
  toFun := lpSpectralDiagonalFun L hC hL
  map_add' := by
    intro u v
    apply lp.ext
    funext i
    change L i (u i + v i) = L i (u i) + L i (v i)
    exact (L i).map_add (u i) (v i)
  map_smul' := by
    intro c u
    apply lp.ext
    funext i
    change L i (c • u i) = c • L i (u i)
    exact (L i).map_smul c (u i)

/-- Uniformly bounded coordinate operators act continuously on square-summable
families, with the same norm bound. This also packages Fourier jet multipliers. -/
def lpSpectralDiagonal (L : ι → B →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖) :
    lp (fun _ : ι => B) 2 →L[ℝ] lp (fun _ : ι => F) 2 :=
  (lpSpectralDiagonalLinear L hC hL).mkContinuous C (fun u => by
    change ‖lpSpectralDiagonalFun L hC hL u‖ ≤ C * ‖u‖
    exact lpSpectralDiagonalFun_norm_le L hC hL u)

theorem lpSpectralDiagonal_apply (L : ι → B →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖)
    (u : lp (fun _ : ι => B) 2) (i : ι) :
    lpSpectralDiagonal L hC hL u i = L i (u i) := rfl

theorem lpSpectralDiagonal_norm_le (L : ι → B →L[ℝ] F)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ i x, ‖L i x‖ ≤ C * ‖x‖)
    (u : lp (fun _ : ι => B) 2) :
    ‖lpSpectralDiagonal L hC hL u‖ ≤ C * ‖u‖ :=
  lpSpectralDiagonalFun_norm_le L hC hL u

end Diagonal

section LogBands

/-- Exponential bands for a spectral size at least one. -/
def spectralLogBand (weight : ι → ℝ) (i : ι) : ℕ := ⌊Real.log (weight i)⌋₊

theorem spectralLogBand_lower (weight : ι → ℝ) (hweight : ∀ i, 1 ≤ weight i) (i : ι) :
    Real.exp (spectralLogBand weight i : ℝ) ≤ weight i := by
  calc
    Real.exp (spectralLogBand weight i : ℝ) ≤ Real.exp (Real.log (weight i)) :=
      Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg (hweight i)))
    _ = weight i := Real.exp_log (zero_lt_one.trans_le (hweight i))

theorem spectralLogBand_upper (weight : ι → ℝ) (hweight : ∀ i, 1 ≤ weight i) (i : ι) :
    weight i < Real.exp ((spectralLogBand weight i : ℝ) + 1) := by
  calc
    weight i = Real.exp (Real.log (weight i)) := (Real.exp_log (zero_lt_one.trans_le (hweight i))).symm
    _ < Real.exp ((spectralLogBand weight i : ℝ) + 1) :=
      Real.exp_lt_exp.mpr (Nat.lt_floor_add_one (Real.log (weight i)))

theorem spectralLogBand_exp_mul_le_pow (weight : ι → ℝ) (hweight : ∀ i, 1 ≤ weight i)
    (s : ℕ) (i : ι) :
    Real.exp ((s : ℝ) * (spectralLogBand weight i : ℝ)) ≤ weight i ^ s := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (spectralLogBand_lower weight hweight i) s

theorem spectralLogBand_pow_le (weight : ι → ℝ) (hweight : ∀ i, 1 ≤ weight i)
    (s : ℕ) (i : ι) :
    weight i ^ s ≤ Real.exp (s : ℝ) * Real.exp ((s : ℝ) * (spectralLogBand weight i : ℝ)) := by
  calc
    weight i ^ s ≤ Real.exp ((spectralLogBand weight i : ℝ) + 1) ^ s :=
      pow_le_pow_left₀ (zero_le_one.trans (hweight i)) (spectralLogBand_upper weight hweight i).le s
    _ = Real.exp ((s : ℝ) * ((spectralLogBand weight i : ℝ) + 1)) :=
      (Real.exp_nat_mul _ s).symm
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

end LogBands

end ContinuousFlexibility.Analysis
