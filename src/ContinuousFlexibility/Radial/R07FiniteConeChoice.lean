import ContinuousFlexibility.Radial.R07ConeTransfer
import ContinuousFlexibility.Radial.R07ConeMiddle

/-!
# Simultaneous finite cone heights and short-join tolerance

The two cone heights are chosen in disjoint thirds of the available
middle-height interval. A single positive angle margin and a single join
length work for every member of the finite frequency family.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_r07_finite_cone_choice {ι : Type*} [Fintype ι]
    (frequency : ι → ℕ) (hfrequency : ∀ i, 2 ≤ frequency i)
    (B : Bool → ι → ℝ × ℝ) (hB : ∀ side i, B side i ≠ (0, 0))
    {a b : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a < b)
    (hf : ContDiff ℝ ∞ f) (hfp : ∀ x, 0 < f x)
    (hfd : ∀ x ∈ Icc a b, 0 < deriv f x) :
    ∃ (WL WR δ eta : ℝ) (H : R07ConeMiddleData),
      f a < WL ∧ WL < WR ∧ WR < f b ∧
      0 < δ ∧ δ ≤ 1 / 48 ∧ 0 < eta ∧
      R07ConeMiddleSpecification a b WL WR eta f H ∧
      (∀ side i, 2 * δ ≤ radialAngleSine (1, r07ConeSlope side (frequency i))
        ((B side i).1, (if side then f b else f a) /
          (if side then WR else WL) * (B side i).2)) ∧
      ∀ i rmin, a ≤ rmin →
        2 * (frequency i : ℝ) ^ 2 * (f b / f a) / rmin * eta ≤ δ / 12 := by
  classical
  have hmono : StrictMonoOn f (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hf.continuous.continuousOn
      (fun x hx => hfd x (interior_subset hx))
  have hfab : f a < f b := hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  obtain ⟨WL, hWL, hAL⟩ := r07_exists_finite_cone_height (Finset.univ : Finset ι)
    (fun i => r07ConeSlope false (frequency i)) (B false)
    (fun i _ => r07ConeSlope_ne_zero false (hfrequency i)) (fun i _ => hB false i)
    (H := f a) (l := f a) (h := (2 * f a + f b) / 3)
    (hfp a) (hfp a) (by linarith only [hfab])
  obtain ⟨WR, hWR, hAR⟩ := r07_exists_finite_cone_height (Finset.univ : Finset ι)
    (fun i => r07ConeSlope true (frequency i)) (B true)
    (fun i _ => r07ConeSlope_ne_zero true (hfrequency i)) (fun i _ => hB true i)
    (H := f b) (l := (f a + 2 * f b) / 3) (h := f b)
    (hfp b) (by have := hfp a; linarith only [this, hfab])
    (by linarith only [hfab])
  have hW : WL < WR := by linarith only [hWL.2, hWR.1, hfab]
  let angle : Bool × ι → ℝ := fun q =>
    radialAngleSine (1, r07ConeSlope q.1 (frequency q.2))
      ((B q.1 q.2).1, (if q.1 then f b else f a) /
        (if q.1 then WR else WL) * (B q.1 q.2).2)
  have hangle : ∀ q, 0 < angle q := by
    rintro ⟨side, i⟩
    cases side
    · exact hAL i (Finset.mem_univ i)
    · exact hAR i (Finset.mem_univ i)
  obtain ⟨δ, hδ, hδ48, hδangle⟩ :=
    r07_exists_finite_angle_tolerance (Finset.univ : Finset (Bool × ι)) angle
      (fun q _ => hangle q)
  let N : ℕ := max 2 (Finset.univ.sup frequency)
  have hN : (0 : ℝ) < N := by
    have hNnat : 2 ≤ N := le_max_left _ _
    exact_mod_cast (by omega : 0 < N)
  have hfreq (i : ι) : frequency i ≤ N :=
    (Finset.le_sup (f := frequency) (Finset.mem_univ i)).trans (le_max_right _ _)
  let contrast : ℝ := f b / f a
  have hcontrast : 0 < contrast := div_pos (hfp b) (hfp a)
  let eta : ℝ := δ * a / (24 * (N : ℝ) ^ 2 * contrast)
  have heta : 0 < eta := div_pos (mul_pos hδ ha) (by positivity)
  obtain ⟨H, hH⟩ := exists_r07_cone_middle ha hab hf hfp hfd hWL.1 hW hWR.2 heta
  refine ⟨WL, WR, δ, eta, H, hWL.1, hW, hWR.2, hδ, hδ48, heta, hH, ?_, ?_⟩
  · intro side i
    exact hδangle (side, i) (Finset.mem_univ _)
  · intro i rmin hmin
    have hrmin : 0 < rmin := ha.trans_le hmin
    have hfreqr : (frequency i : ℝ) ≤ N := by exact_mod_cast hfreq i
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (frequency i)) hfreqr 2
    have hnum : 2 * (frequency i : ℝ) ^ 2 * contrast ≤ 2 * (N : ℝ) ^ 2 * contrast :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) hcontrast.le
    calc
      _ ≤ (2 * (N : ℝ) ^ 2 * contrast / a) * eta :=
        mul_le_mul_of_nonneg_right
          ((div_le_div_of_nonneg_right hnum hrmin.le).trans
            (div_le_div_of_nonneg_left (by positivity) ha hmin)) heta.le
      _ = δ / 12 := by
        dsimp only [eta]
        field_simp [ha.ne', hN.ne', hcontrast.ne'] <;> ring

end ContinuousFlexibility.Radial
