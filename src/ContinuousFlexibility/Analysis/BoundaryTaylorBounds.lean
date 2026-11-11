import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear mixed-jet bounds for boundary Taylor extensions

The radial basis is fixed before choosing an interval. After scaling by
its actual width `w`, its derivative of order `a` carries precisely the
factor `w^j * (w⁻¹)^a`. Angular derivatives act only on the prescribed
boundary coefficient functions. Thus the estimate is linear in the data,
has no lower-width hypothesis, and introduces no growing derivative loss
in the boundary data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The fixed normalized radial basis for the finite boundary extension. -/
def boundaryTaylorBasis (j : ℕ) (x : ℝ) : ℝ :=
  boundaryTaylorCutoff x * (x ^ j / (j.factorial : ℝ))

theorem contDiff_boundaryTaylorBasis (j : ℕ) :
    ContDiff ℝ ∞ (boundaryTaylorBasis j) :=
  boundaryTaylorCutoff.contDiff.mul ((contDiff_id.pow j).div_const _)

theorem hasCompactSupport_boundaryTaylorBasis (j : ℕ) :
    HasCompactSupport (boundaryTaylorBasis j) := by
  have heq : boundaryTaylorBasis j =
      (boundaryTaylorCutoff : ℝ → ℝ) * (fun x : ℝ => x ^ j / (j.factorial : ℝ)) := by
    funext x
    simp only [boundaryTaylorBasis, Pi.mul_apply]
  rw [heq]
  exact boundaryTaylorCutoff.hasCompactSupport.mul_right

/-- One constant bounds a fixed radial derivative of all the finitely many
normalized basis functions, globally on the real line. -/
theorem exists_boundaryTaylorBasis_jet_bound (n a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ n, ∀ x : ℝ,
      |iteratedDeriv a (boundaryTaylorBasis j) x| ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |iteratedDeriv a (boundaryTaylorBasis j) x| ≤ C := by
    have hs : HasCompactSupport (iteratedDeriv a (boundaryTaylorBasis j)) := by
      induction a with
      | zero =>
          simpa only [iteratedDeriv_zero] using hasCompactSupport_boundaryTaylorBasis j
      | succ a ih =>
          rw [iteratedDeriv_succ]
          exact ih.deriv
    have hc := ContDiff.continuous_iteratedDeriv a
      (contDiff_boundaryTaylorBasis j) (by simp)
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
    exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by
      simpa only [Real.norm_eq_abs] using hC x⟩
  choose B hB0 hB using hb
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), B j :=
    Finset.sum_nonneg (fun j _ => hB0 j)
  refine ⟨1 + ∑ j ∈ Finset.range (n + 1), B j, by linarith, ?_⟩
  intro j hj x
  refine (hB j x).trans ?_
  have hjmem : j ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsingle := Finset.single_le_sum (fun i _ => hB0 i) hjmem
  linarith

private theorem mixedDerivative_separated_sum {ι : Type*}
    (s : Finset ι) {u v : ι → ℝ → ℝ}
    (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hv : ∀ i ∈ s, ContDiff ℝ ∞ (v i)) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => ∑ i ∈ s, u i q.1 * v i q.2) p =
      ∑ i ∈ s, iteratedDeriv a (u i) p.1 * iteratedDeriv b (v i) p.2 := by
  have hθ (i : ι) (hi : i ∈ s) (r : ℝ) :
      ContDiff ℝ ∞ (fun θ : ℝ => u i r * v i θ) :=
    contDiff_const.mul (hv i hi)
  have hr (i : ι) (hi : i ∈ s) :
      ContDiff ℝ ∞ (fun r : ℝ => u i r * iteratedDeriv b (v i) p.2) :=
    (hu i hi).mul contDiff_const
  have hb (r : ℝ) :
      iteratedDeriv b (fun θ => ∑ i ∈ s, u i r * v i θ) p.2 =
        ∑ i ∈ s, u i r * iteratedDeriv b (v i) p.2 := by
    rw [iteratedDeriv_fun_sum (fun i hi =>
      ((hθ i hi r).of_le (show (b : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
    simp only [iteratedDeriv_const_mul_field]
  unfold mixedDerivative
  simp_rw [hb]
  rw [iteratedDeriv_fun_sum (fun i hi =>
    ((hr i hi).of_le (show (a : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
  simp only [iteratedDeriv_mul_const_field]

private theorem mixedDerivative_add_smooth {F G : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => F q + G q) p =
      mixedDerivative a b F p + mixedDerivative a b G p := by
  have hθ {H : PolarPoint → ℝ} (hH : ContDiff ℝ ∞ H) (r : ℝ) :
      ContDiff ℝ ∞ (fun θ : ℝ => H (r, θ)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hb (r : ℝ) :
      iteratedDeriv b (fun θ => F (r, θ) + G (r, θ)) p.2 =
        iteratedDeriv b (fun θ => F (r, θ)) p.2 +
          iteratedDeriv b (fun θ => G (r, θ)) p.2 :=
    iteratedDeriv_fun_add
      (((hθ hF r).of_le (show (b : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
      (((hθ hG r).of_le (show (b : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
  have hs {H : PolarPoint → ℝ} (hH : ContDiff ℝ ∞ H) :
      ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => H (r, θ)) p.2) := by
    have hjet : ContDiff ℝ ∞ (mixedDerivative 0 b H) :=
      contDiffOn_univ.mp (contDiffOn_mixedDerivative isOpen_univ hH.contDiffOn 0 b)
    have hcomp : ContDiff ℝ ∞ (fun r : ℝ => mixedDerivative 0 b H (r, p.2)) :=
      hjet.comp (contDiff_id.prodMk contDiff_const)
    simpa only [mixedDerivative, iteratedDeriv_zero] using hcomp
  unfold mixedDerivative
  simp_rw [hb]
  exact iteratedDeriv_fun_add
    (((hs hF).of_le (show (a : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
    (((hs hG).of_le (show (a : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)

private theorem boundaryTaylor_cutoff_eq_sum_scaled (n : ℕ) (c w : ℝ)
    (hw : w ≠ 0) (A : ℕ → ℝ → ℝ) (p : PolarPoint) :
    boundaryTaylorCutoff ((p.1 - c) / w) * boundaryTaylorPolynomial n c A p =
      ∑ j ∈ Finset.range (n + 1),
        w ^ j * boundaryTaylorBasis j ((p.1 - c) / w) * A j p.2 := by
  unfold boundaryTaylorPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hpow : w ^ j * ((p.1 - c) / w) ^ j = (p.1 - c) ^ j := by
    rw [div_pow, mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hw)]
  unfold boundaryTaylorBasis
  calc
    _ = boundaryTaylorCutoff ((p.1 - c) / w) *
        (A j p.2 / (j.factorial : ℝ) * (w ^ j * ((p.1 - c) / w) ^ j)) := by
      rw [hpow]
    _ = _ := by ring

private theorem iteratedDeriv_scaled_boundaryTaylorBasis
    (j a : ℕ) (c w x : ℝ) :
    iteratedDeriv a
      (fun r => w ^ j * boundaryTaylorBasis j ((r - c) / w)) x =
      w ^ j * (w⁻¹) ^ a * iteratedDeriv a (boundaryTaylorBasis j) ((x - c) / w) := by
  simp_rw [div_eq_inv_mul]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_sub_const a (fun r : ℝ => boundaryTaylorBasis j (w⁻¹ * r)) c,
    iteratedDeriv_comp_const_mul ((contDiff_boundaryTaylorBasis j).of_le
      (show (a : ℕ∞ω) ≤ ∞ by simp)) w⁻¹]
  ring

/-- Exact finite mixed-jet formula. The angular order acts only on the
boundary data, while all radial-order dependence is explicit. -/
theorem mixedDerivative_boundaryTaylorExtension {n : ℕ} {A B : ℕ → ℝ → ℝ}
    (hA : ∀ j ≤ n, ContDiff ℝ ∞ (A j))
    (hB : ∀ j ≤ n, ContDiff ℝ ∞ (B j))
    {c d : ℝ} (hcd : c ≠ d) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (boundaryTaylorExtension n c d A B) p =
      (∑ j ∈ Finset.range (n + 1),
        |d - c| ^ j * (|d - c|⁻¹) ^ a *
          iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - c) / |d - c|) *
          iteratedDeriv b (A j) p.2) +
      ∑ j ∈ Finset.range (n + 1),
        |d - c| ^ j * (|d - c|⁻¹) ^ a *
          iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - d) / |d - c|) *
          iteratedDeriv b (B j) p.2 := by
  let w : ℝ := |d - c|
  have hw : w ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hcd.symm)
  have hpatch (e : ℝ) (V : ℕ → ℝ → ℝ)
      (hV : ∀ j ≤ n, ContDiff ℝ ∞ (V j)) :
      mixedDerivative a b
        (fun q => boundaryTaylorCutoff ((q.1 - e) / w) *
          boundaryTaylorPolynomial n e V q) p =
        ∑ j ∈ Finset.range (n + 1),
          w ^ j * (w⁻¹) ^ a *
            iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - e) / w) *
            iteratedDeriv b (V j) p.2 := by
    have hR (j : ℕ) : ContDiff ℝ ∞
        (fun r : ℝ => w ^ j * boundaryTaylorBasis j ((r - e) / w)) :=
      contDiff_const.mul ((contDiff_boundaryTaylorBasis j).comp
        ((contDiff_id.sub contDiff_const).div_const w))
    have heq := funext (boundaryTaylor_cutoff_eq_sum_scaled n e w hw V)
    rw [heq, mixedDerivative_separated_sum (Finset.range (n + 1))
      (fun j _ => hR j)
      (fun j hj => hV j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_scaled_boundaryTaylorBasis]
  have hs (e : ℝ) (V : ℕ → ℝ → ℝ)
      (hV : ∀ j ≤ n, ContDiff ℝ ∞ (V j)) :
      ContDiff ℝ ∞ (fun q : PolarPoint =>
        boundaryTaylorCutoff ((q.1 - e) / w) * boundaryTaylorPolynomial n e V q) :=
    (boundaryTaylorCutoff.contDiff.comp
      ((contDiff_fst.sub contDiff_const).div_const w)).mul
      (contDiff_boundaryTaylorPolynomial hV e)
  change mixedDerivative a b
    (fun q => boundaryTaylorCutoff ((q.1 - c) / w) * boundaryTaylorPolynomial n c A q +
      boundaryTaylorCutoff ((q.1 - d) / w) * boundaryTaylorPolynomial n d B q) p = _
  rw [mixedDerivative_add_smooth (hs c A hA) (hs d B hB)]
  exact congrArg₂ (· + ·) (hpatch c A hA) (hpatch d B hB)

/-- A coefficient-linear estimate with all width factors displayed.
The constant depends only on the finite Taylor degree and the radial
derivative order. In particular it is independent of the interval, the
angular order, and the boundary data. -/
theorem exists_boundaryTaylorExtension_mixed_bound (n a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d : ℝ), c ≠ d →
      ∀ (A B : ℕ → ℝ → ℝ),
      (∀ j ≤ n, ContDiff ℝ ∞ (A j)) →
      (∀ j ≤ n, ContDiff ℝ ∞ (B j)) →
      ∀ (b : ℕ) (p : PolarPoint),
        |mixedDerivative a b (boundaryTaylorExtension n c d A B) p| ≤
          C * (|d - c|⁻¹) ^ a *
            ∑ j ∈ Finset.range (n + 1),
              |d - c| ^ j * (|iteratedDeriv b (A j) p.2| +
                |iteratedDeriv b (B j) p.2|) := by
  obtain ⟨C, hC0, hC⟩ := exists_boundaryTaylorBasis_jet_bound n a
  refine ⟨C, hC0, ?_⟩
  intro c d hcd A B hA hB b p
  let w : ℝ := |d - c|
  have hw0 : 0 ≤ w := abs_nonneg _
  have hi0 : 0 ≤ (w⁻¹) ^ a := pow_nonneg (inv_nonneg.mpr hw0) _
  have hsum (e : ℝ) (V : ℕ → ℝ → ℝ) :
      |∑ j ∈ Finset.range (n + 1),
        w ^ j * (w⁻¹) ^ a *
          iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - e) / w) *
          iteratedDeriv b (V j) p.2| ≤
        C * (w⁻¹) ^ a *
          ∑ j ∈ Finset.range (n + 1), w ^ j * |iteratedDeriv b (V j) p.2| := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          |w ^ j * (w⁻¹) ^ a *
            iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - e) / w) *
            iteratedDeriv b (V j) p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          C * (w⁻¹) ^ a * (w ^ j * |iteratedDeriv b (V j) p.2|) := by
        apply Finset.sum_le_sum
        intro j hj
        have hpre : 0 ≤ w ^ j * (w⁻¹) ^ a :=
          mul_nonneg (pow_nonneg hw0 _) hi0
        calc
          _ = (w ^ j * (w⁻¹) ^ a) *
              |iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - e) / w)| *
              |iteratedDeriv b (V j) p.2| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hpre]
          _ ≤ (w ^ j * (w⁻¹) ^ a) * C * |iteratedDeriv b (V j) p.2| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (hC j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) _) hpre)
              (abs_nonneg _)
          _ = _ := by ring
      _ = _ := (Finset.mul_sum ..).symm
  rw [mixedDerivative_boundaryTaylorExtension hA hB hcd a b p]
  calc
    _ ≤ |∑ j ∈ Finset.range (n + 1),
          w ^ j * (w⁻¹) ^ a *
            iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - c) / w) *
            iteratedDeriv b (A j) p.2| +
        |∑ j ∈ Finset.range (n + 1),
          w ^ j * (w⁻¹) ^ a *
            iteratedDeriv a (boundaryTaylorBasis j) ((p.1 - d) / w) *
            iteratedDeriv b (B j) p.2| := abs_add_le _ _
    _ ≤ C * (w⁻¹) ^ a *
          (∑ j ∈ Finset.range (n + 1), w ^ j * |iteratedDeriv b (A j) p.2|) +
        C * (w⁻¹) ^ a *
          ∑ j ∈ Finset.range (n + 1), w ^ j * |iteratedDeriv b (B j) p.2| :=
      add_le_add (hsum c A) (hsum d B)
    _ = _ := by
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

end ContinuousFlexibility.Analysis
