import ContinuousFlexibility.Analysis.N04RealizationEnvelopeComposition
import ContinuousFlexibility.Analysis.FiniteInversePolynomialEnvelope
import ContinuousFlexibility.Analysis.PlanarInverseDerivativeBound

/-!
# Finite inverse and positive composition envelopes at boundary points

All constants precede the evaluation index. Positive composition uses
only positive jets of both maps, so no angular lift value is bounded.
The inverse step reuses the existing universal finite polynomial.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {X D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04Realization_envelope_comp_positive_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f : X → E → F) (g : X → D → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) {n : ℕ} (hn : 0 < n)
    (hfj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (g x (p x))‖))
    (hgj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (f x ∘ g x) (p x)‖) := by
  classical
  have hsum := hasPositiveEnvelope_finsetSum hW
    (Finset.univ : Finset (OrderedFinpartition n))
    (fun c x => ‖iteratedFDeriv ℝ c.length (f x) (g x (p x))‖ *
      ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖) (by
      intro c _
      have hprod := hasPositiveEnvelope_finsetProd hW
        (Finset.univ : Finset (Fin c.length))
        (fun j x => ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖)
        (fun _ _ _ => norm_nonneg _)
        (fun j _ => hgj _ (c.partSize_pos j) (c.partSize_le j))
      exact (hfj c.length (c.length_pos hn) c.length_le).mul hW hprod
        (fun x => Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact hsum.mono (fun x =>
    norm_iteratedFDeriv_comp_le_partition_sum (hf x) (hg x) n)

/-- The actual inverse derivative is bounded using the actual forward
derivative and determinant, with no chosen inverse representation. -/
theorem n04Realization_inverse_first_norm_le
    {f g : PolarPoint → PolarPoint} {p : PolarPoint}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g (f p))
    (hgf : g ∘ f =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hJ : planeJacobian f p ≠ 0) :
    ‖fderiv ℝ g (f p)‖ ≤
      2 * ‖fderiv ℝ f p‖ * |planeJacobian f p|⁻¹ := by
  let A : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ f p
  have hentry (v : PolarPoint) (hv : ‖v‖ ≤ 1) :
      |(A v).1| ≤ ‖A‖ ∧ |(A v).2| ≤ ‖A‖ := by
    have hAv : ‖A v‖ ≤ ‖A‖ :=
      (A.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg A) hv)
    have hfst : |(A v).1| ≤ ‖A v‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (A v)
    have hsnd : |(A v).2| ≤ ‖A v‖ := by
      simpa only [Real.norm_eq_abs] using norm_snd_le (A v)
    exact ⟨hfst.trans hAv, hsnd.trans hAv⟩
  have h₁ := hentry (1, 0) (by norm_num [Prod.norm_def])
  have h₂ := hentry (0, 1) (by norm_num [Prod.norm_def])
  simpa only [div_eq_mul_inv] using
    fderiv_inverse_norm_le_of_germ hf hg hgf (abs_pos.mpr hJ) le_rfl
      h₁.1 h₂.1 h₁.2 h₂.2

/-- A finite prefix of forward envelopes and the actual first inverse
derivative give every positive inverse jet in that prefix. -/
theorem n04Realization_envelope_inverse_positive_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → F)
    (f : X → E → F) (g : X → F → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x))
    (hfg : ∀ x, f x ∘ g x =ᶠ[𝓝 (p x)] (id : F → F))
    (hleft : ∀ x, (fderiv ℝ (g x) (p x)).comp
      (fderiv ℝ (f x) (g x (p x))) = ContinuousLinearMap.id ℝ E)
    (hfirst : HasPositiveEnvelope W (fun x => ‖fderiv ℝ (g x) (p x)‖))
    {n : ℕ} (hn : 0 < n)
    (hfj : ∀ j, 2 ≤ j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (g x (p x))‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (g x) (p x)‖) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
      let V : Fin n → X → ℝ := fun j x =>
        ‖iteratedFDeriv ℝ (j.val + 2) (f x) (g x (p x))‖
      let R : X → ℝ := fun x =>
        1 + ‖fderiv ℝ (g x) (p x)‖ + ∑ j : Fin n, V j x
      have hV₀ (j : Fin n) (x : X) : 0 ≤ V j x := norm_nonneg _
      have hsum₀ (x : X) : 0 ≤ ∑ j : Fin n, V j x :=
        Finset.sum_nonneg (fun j _ => hV₀ j x)
      have hR₁ (x : X) : 1 ≤ R x := by
        dsimp only [R]
        linarith only [norm_nonneg (fderiv ℝ (g x) (p x)), hsum₀ x]
      have hL (x : X) : ‖fderiv ℝ (g x) (p x)‖ ≤ R x := by
        dsimp only [R]
        linarith only [hsum₀ x]
      have hV (x : X) (j : Fin n) : V j x ≤ R x := by
        have ht : V j x ≤ ∑ i : Fin n, V i x :=
          Finset.single_le_sum (f := fun i : Fin n => V i x)
            (fun i _ => hV₀ i x) (Finset.mem_univ j)
        dsimp only [R]
        linarith only [ht, norm_nonneg (fderiv ℝ (g x) (p x))]
      have hRE : HasPositiveEnvelope W R :=
        ((hasPositiveEnvelope_const W hW 1).add hW hfirst).add hW
          (hasPositiveEnvelope_finsetSum hW (Finset.univ : Finset (Fin n)) V
            (fun j _ => hfj (j.val + 2) (by omega) (by omega)))
      obtain ⟨C, hC, d, hpoly⟩ :=
        exists_nonlinearInverse_finiteJet_polynomial_envelope (E := E) (F := F) n
      have htotal := (hasPositiveEnvelope_const W hW C).mul hW
        (hRE.pow hW (fun x => zero_le_one.trans (hR₁ x)) d)
        (fun x => pow_nonneg (zero_le_one.trans (hR₁ x)) d)
      apply htotal.mono
      intro x
      apply hpoly (hR₁ x) (f x) (g x) (p x) (hf x) (hg x) (hfg x)
        (fderiv ℝ (g x) (p x)) (hleft x) (hL x)
      intro k hk hkn
      let j : Fin n := ⟨k - 1, by omega⟩
      have hj : j.val + 2 = k + 1 := by dsimp only [j]; omega
      have hv := hV x j
      simpa only [V, hj] using hv

end ContinuousFlexibility.Analysis
