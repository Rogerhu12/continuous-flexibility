import ContinuousFlexibility.Analysis.N01cStateHeightBounds
import ContinuousFlexibility.Analysis.FlatExtension

/-!
# Weighted jets of the actual polar height inputs

The radial factor in the normalized angular derivative is differentiated
by a finite Leibniz formula. Its ordinary derivatives are uniformly bounded
on the closed physical radial interval, which is separated from zero.
The two further polar partials are the actual coordinate derivatives.
Consequently all five height inputs share one coefficient-envelope power,
retain the original height exponent, and require four additional input
grading orders.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

/-- Exact Leibniz expansion for a radial scalar multiplier of a smooth
cylinder function. Smoothness of the multiplier is needed only at the
actual evaluation radius. -/
theorem mixedDerivative_radial_mul
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) {g : ℝ → ℝ}
    (a b : ℕ) (p : PolarPoint) (hg : ContDiffAt ℝ ∞ g p.1) :
    mixedDerivative a b (fun q => g q.1 * f q) p =
      ∑ i : Fin (a + 1), (a.choose i.val : ℝ) * iteratedDeriv i.val g p.1 *
        mixedDerivative (a - i.val) b f p := by
  let F : ℝ → ℝ := fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2
  have hF : ContDiff ℝ ∞ F := by
    simpa only [F, Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
      (contDiff_mixedDerivative hf 0 b).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p.2)))
  let term (i : ℕ) : ℝ :=
    (a.choose i : ℝ) * iteratedDeriv i g p.1 * iteratedDeriv (a - i) F p.1
  have hformula :
      iteratedDeriv a (fun r => g r * F r) p.1 =
        ∑ i : Fin (a + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul (hg.of_le (by simp)) (hF.contDiffAt.of_le (by simp))
  change iteratedDeriv a
    (fun r => iteratedDeriv b (fun θ => g r * f (r, θ)) p.2) p.1 = _
  simp_rw [iteratedDeriv_const_mul_field]
  exact hformula

private theorem reciprocal_iteratedDeriv_bound
    {a b : ℝ} (ha : 0 < a) (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc a b,
      |iteratedDeriv i (fun t : ℝ => t⁻¹) r| ≤ B := by
  have hs : ContDiffOn ℝ ∞ (fun t : ℝ => t⁻¹) (Ioi (0 : ℝ)) :=
    contDiffOn_id.inv (fun t ht => ne_of_gt ht)
  have hc : ContinuousOn (fun r => |iteratedDeriv i (fun t : ℝ => t⁻¹) r|)
      (Ioi (0 : ℝ)) :=
    (differentiableOn_iteratedDeriv_Ioi hs i).continuousOn.abs
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun r hr => ha.trans_le hr.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.mono hsub)
  refine ⟨max 0 B, le_max_left _ _, fun r hr => ?_⟩
  exact (hB ⟨r, hr, rfl⟩).trans (le_max_right _ _)

/-- Multiplication by the actual reciprocal radius has a spatially
uniform finite-jet bound. The constant depends only on the radial interval
and the requested order, and is independent of the function and weight. -/
theorem reciprocal_radius_mul_mixedJets_bound
    {D : ReferenceData} (hD : 0 < D.a) (s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : PolarPoint → ℝ, ContDiff ℝ ∞ f →
      ∀ W : PolarPoint → ℝ, (∀ p ∈ annularOpen D, 0 ≤ W p) →
      (∀ a b : ℕ, a + b ≤ s → ∀ p ∈ annularOpen D,
        |mixedDerivative a b f p| ≤ W p) →
      ∀ a b : ℕ, a + b ≤ s → ∀ p ∈ annularOpen D,
        |mixedDerivative a b (fun q => q.1⁻¹ * f q) p| ≤ K * W p := by
  have hb (i : ℕ) := reciprocal_iteratedDeriv_bound (b := D.b) hD i
  choose B hB hbound using hb
  let A : ℕ → ℝ := fun a =>
    ∑ i : Fin (a + 1), (a.choose i.val : ℝ) * B i.val
  have hA (a : ℕ) : 0 ≤ A a :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hB i.val))
  let K : ℝ := ∑ j : Fin (s + 1), A j.val
  have hK : 0 ≤ K := Finset.sum_nonneg (fun j _ => hA j.val)
  refine ⟨K, hK, fun f hf W hW hjet a b hab p hp => ?_⟩
  have hr : 0 < p.1 := hD.trans hp.1.1
  have hg : ContDiffAt ℝ ∞ (fun r : ℝ => r⁻¹) p.1 :=
    contDiffAt_id.inv hr.ne'
  let j : Fin (s + 1) := ⟨a, by omega⟩
  have hAK : A a ≤ K :=
    Finset.single_le_sum (fun k _ => hA k.val) (Finset.mem_univ j)
  rw [mixedDerivative_radial_mul hf a b p hg]
  calc
    _ ≤ ∑ i : Fin (a + 1),
        |(a.choose i.val : ℝ) * iteratedDeriv i.val (fun r : ℝ => r⁻¹) p.1 *
          mixedDerivative (a - i.val) b f p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (a + 1), ((a.choose i.val : ℝ) * B i.val) * W p := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (a.choose i.val))]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (hbound i.val p.1 ⟨hp.1.1.le, hp.1.2.le⟩) (Nat.cast_nonneg _))
        (hjet (a - i.val) b (by omega) p hp)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB i.val))
    _ = A a * W p := by simp only [A, Finset.sum_mul]
    _ ≤ K * W p := mul_le_mul_of_nonneg_right hAK (hW p hp)

set_option backward.isDefEq.respectTransparency true in
/-- All five genuine polar height inputs have one ordinary mixed-jet
bound on the physical annulus. The two derivatives inside the inputs and
the two Sobolev evaluation derivatives give a fixed loss of four. -/
theorem stateU_polarMixedJets_le_E0_stateGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : 0 < D.a) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : AnnularState S, ∀ a b : ℕ,
      a + b ≤ s → ∀ p ∈ annularOpen D,
        let B := C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          stateGrading S (s + 4) x
        |mixedDerivative a b (heightRadial (stateU S x)) p| ≤ B ∧
        |mixedDerivative a b (heightAngular (stateU S x)) p| ≤ B ∧
        |mixedDerivative a b (radialPartial (heightRadial (stateU S x))) p| ≤ B ∧
        |mixedDerivative a b (radialPartial (heightAngular (stateU S x))) p| ≤ B ∧
        |mixedDerivative a b (angularPartial (heightAngular (stateU S x))) p| ≤ B := by
  obtain ⟨C₀, A, hC₀, hA, hbase⟩ :=
    stateU_positiveMixedJets_le_E0_stateGrading hT hS (s + 2)
  obtain ⟨K, hK, hmul⟩ := reciprocal_radius_mul_mixedJets_bound hD (s + 1)
  refine ⟨(1 + K) * C₀, A, mul_nonneg (by linarith) hC₀, hA,
    fun x a b hab p hp => ?_⟩
  let W : PolarPoint → ℝ := fun q =>
    C₀ * T.E0 q.1 ^ A * T.H q.1 ^ (3 / 4 : ℝ) * stateGrading S (s + 4) x
  have hW (q : PolarPoint) (hq : q ∈ annularOpen D) : 0 ≤ W q :=
    mul_nonneg (mul_nonneg
      (mul_nonneg hC₀ (Real.rpow_nonneg (hT.2.1 _ hq.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 _ hq.1).2.1.le _)) (apply_nonneg _ _)
  have hraw (c d : ℕ) (hcd : 0 < c + d) (horder : c + d ≤ s + 2)
      (q : PolarPoint) (hq : q ∈ annularOpen D) :
      |mixedDerivative c d (stateU S x) q| ≤ W q := by
    simpa only [W, Nat.add_assoc] using hbase x c d hcd horder q hq
  have hf : ContDiff ℝ ∞ (stateU S x) :=
    physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1.1 x.1.2
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hzero : mixedDerivative 0 0 (stateU S x) = stateU S x := by
    funext q
    simp only [mixedDerivative, iteratedDeriv_zero]
  have hθeq : angularPartial (stateU S x) = mixedDerivative 0 1 (stateU S x) := by
    simpa only [hzero, Nat.zero_add] using angularPartial_mixedDerivative hf 0 0
  have hθ : ContDiff ℝ ∞ (angularPartial (stateU S x)) := by
    rw [hθeq]
    exact contDiff_mixedDerivative hf 0 1
  have hk : ContDiff ℝ ∞ (heightRadial (stateU S x)) := by
    have he : heightRadial (stateU S x) = mixedDerivative 1 0 (stateU S x) :=
      funext (heightRadial_eq_firstMixedJet hf)
    rw [he]
    exact contDiff_mixedDerivative hf 1 0
  have hangular : ContDiffOn ℝ ∞ (heightAngular (stateU S x)) (annularOpen D) :=
    hθ.contDiffOn.div contDiffOn_fst (fun q hq => (hD.trans hq.1.1).ne')
  have hθjet : ∀ c d : ℕ, c + d ≤ s + 1 → ∀ q ∈ annularOpen D,
      |mixedDerivative c d (angularPartial (stateU S x)) q| ≤ W q := by
    intro c d hcd q hq
    rw [mixedDerivative_angularPartial hU hf.contDiffOn c d hq]
    exact hraw c (d + 1) (by omega) (by omega) q hq
  have hnormalized : ∀ c d : ℕ, c + d ≤ s + 1 → ∀ q ∈ annularOpen D,
      |mixedDerivative c d (heightAngular (stateU S x)) q| ≤ K * W q := by
    have he : heightAngular (stateU S x) =
        (fun q => q.1⁻¹ * angularPartial (stateU S x) q) := by
      funext q
      simp only [heightAngular, div_eq_mul_inv, mul_comm]
    rw [he]
    exact hmul (angularPartial (stateU S x)) hθ W hW hθjet
  have hradial :
      |mixedDerivative a b (heightRadial (stateU S x)) p| ≤ W p := by
    change |mixedDerivative a b (radialPartial (stateU S x)) p| ≤ W p
    rw [mixedDerivative_radialPartial hU hf.contDiffOn a b hp]
    exact hraw (a + 1) b (by omega) (by omega) p hp
  have hradialRadial :
      |mixedDerivative a b (radialPartial (heightRadial (stateU S x))) p| ≤ W p := by
    rw [mixedDerivative_radialPartial hU hk.contDiffOn a b hp]
    change |mixedDerivative (a + 1) b (radialPartial (stateU S x)) p| ≤ W p
    rw [mixedDerivative_radialPartial hU hf.contDiffOn (a + 1) b hp]
    exact hraw (a + 1 + 1) b (by omega) (by omega) p hp
  have hradialAngular :
      |mixedDerivative a b (radialPartial (heightAngular (stateU S x))) p| ≤ K * W p := by
    rw [mixedDerivative_radialPartial hU hangular a b hp]
    exact hnormalized (a + 1) b (by omega) p hp
  have hangularAngular :
      |mixedDerivative a b (angularPartial (heightAngular (stateU S x))) p| ≤ K * W p := by
    rw [mixedDerivative_angularPartial hU hangular a b hp]
    exact hnormalized a (b + 1) (by omega) p hp
  let P : ℝ := ((1 + K) * C₀) * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
    stateGrading S (s + 4) x
  have hscale : (1 + K) * W p = P := by dsimp only [W, P]; ring
  have hWP : W p ≤ P := by
    rw [← hscale]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + K by linarith) (hW p hp)
  have hKWP : K * W p ≤ P := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_right (by linarith) (hW p hp)
  exact ⟨hradial.trans hWP, (hnormalized a b (by omega) p hp).trans hKWP,
    hradialRadial.trans hWP, hradialAngular.trans hKWP, hangularAngular.trans hKWP⟩

end ContinuousFlexibility.Statements
