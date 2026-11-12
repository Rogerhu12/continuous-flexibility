import ContinuousFlexibility.Analysis.N04RealizationEnvelopeAlgebra
import ContinuousFlexibility.Analysis.OneHighCompositionJets
import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets

/-!
# Finite jet envelopes for actual products and compositions

The point and functions may vary with an arbitrary index. Composition
uses outer jets through the requested order and only positive inner
jets. In particular, it never estimates an unwrapped angular value.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators

variable {X D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Localize the public bilinear jet estimate at one actual point. -/
theorem n04Realization_norm_iteratedFDeriv_bilinear_le_at
    (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  obtain ⟨V, hV, hxV, hgV⟩ := hg.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hf' : ContDiffOn ℝ n f U := by simpa using hfU
  have hg' : ContDiffOn ℝ n g V := by simpa using hgV
  have hUV : IsOpen (U ∩ V) := hU.inter hV
  have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩
  have hfjet (j : ℕ) : iteratedFDerivWithin ℝ j f (U ∩ V) x =
      iteratedFDeriv ℝ j f x := iteratedFDerivWithin_of_isOpen j hUV hxUV
  have hgjet (j : ℕ) : iteratedFDerivWithin ℝ j g (U ∩ V) x =
      iteratedFDeriv ℝ j g x := iteratedFDerivWithin_of_isOpen j hUV hxUV
  have hBjet : iteratedFDerivWithin ℝ n (fun y => B (f y) (g y)) (U ∩ V) x =
      iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x :=
    iteratedFDerivWithin_of_isOpen n hUV hxUV
  simpa only [hfjet, hgjet, hBjet] using
    B.norm_iteratedFDerivWithin_le_of_bilinear (hf'.mono inter_subset_left)
      (hg'.mono inter_subset_right) hUV.uniqueDiffOn hxUV le_rfl

theorem n04Realization_envelope_bilinear_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (B : E →L[ℝ] F →L[ℝ] G) (f : X → D → E) (g : X → D → F)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) (n : ℕ)
    (hfj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (p x)‖))
    (hgj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => B (f x y) (g x y)) (p x)‖) := by
  have hsum := hasPositiveEnvelope_finsetSum hW (Finset.range (n + 1))
    (fun i x => (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (f x) (p x)‖ *
      ‖iteratedFDeriv ℝ (n - i) (g x) (p x)‖) (by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact ((hasPositiveEnvelope_const W hW (n.choose i : ℝ)).mul hW
        (hfj i hin) (fun _ => norm_nonneg _)).mul hW
          (hgj (n - i) (Nat.sub_le n i)) (fun _ => norm_nonneg _))
  have htotal := (hasPositiveEnvelope_const W hW ‖B‖).mul hW hsum
    (fun x => Finset.sum_nonneg (fun i _ => by positivity))
  exact htotal.mono (fun x => n04Realization_norm_iteratedFDeriv_bilinear_le_at
    B (hf x) (hg x) n)

theorem n04Realization_envelope_clm_apply_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f : X → D → E →L[ℝ] F) (g : X → D → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) (n : ℕ)
    (hfj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (p x)‖))
    (hgj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => f x y (g x y)) (p x)‖) := by
  have h := n04Realization_envelope_bilinear_jets hW p
    (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ F)) f g hf hg n hfj hgj
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply] using h

theorem n04Realization_envelope_mul_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f g : X → D → ℝ)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (p x))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) (n : ℕ)
    (hfj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (p x)‖))
    (hgj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => f x y * g x y) (p x)‖) := by
  have h := n04Realization_envelope_bilinear_jets hW p
    (ContinuousLinearMap.mul ℝ ℝ) f g hf hg n hfj hgj
  simpa only [ContinuousLinearMap.mul_apply'] using h

/-- The inner zeroth jet is deliberately absent. -/
theorem n04Realization_envelope_comp_jets
    {W : X → ℝ} (hW : ∀ x, 1 ≤ W x) (p : X → D)
    (f : X → E → F) (g : X → D → E)
    (hf : ∀ x, ContDiffAt ℝ ∞ (f x) (g x (p x)))
    (hg : ∀ x, ContDiffAt ℝ ∞ (g x) (p x)) (n : ℕ)
    (hfj : ∀ j, j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (f x) (g x (p x))‖))
    (hgj : ∀ j, 0 < j → j ≤ n → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (g x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (f x ∘ g x) (p x)‖) := by
  classical
  have hsum := hasPositiveEnvelope_finsetSum hW (Finset.univ : Finset (OrderedFinpartition n))
    (fun c x => ‖iteratedFDeriv ℝ c.length (f x) (g x (p x))‖ *
      ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖) (by
      intro c _
      have hprod := hasPositiveEnvelope_finsetProd hW (Finset.univ : Finset (Fin c.length))
        (fun j x => ‖iteratedFDeriv ℝ (c.partSize j) (g x) (p x)‖)
        (fun _ _ _ => norm_nonneg _)
        (fun j _ => hgj _ (c.partSize_pos j) (c.partSize_le j))
      exact (hfj c.length c.length_le).mul hW hprod
        (fun x => Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact hsum.mono (fun x => norm_iteratedFDeriv_comp_le_partition_sum (hf x) (hg x) n)

end ContinuousFlexibility.Analysis
