import ContinuousFlexibility.Analysis.SmoothDirectionsUnitIntegral
import ContinuousFlexibility.Analysis.TameJetLocalBounds
import Mathlib.Tactic.Abel

/-!
# Fixed-loss tameness of compactly averaged linear pullbacks

A family of linear maps that contracts the grading on the unit interval
preserves each homogeneous jet estimate. Compactness selects finitely
many neighborhoods along the image of the reference point. Their finite
maximum loss and finite minimum radius are chosen before the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem tameJetSize_linear_contraction
    (p : ℕ → Seminorm ℝ E) (L : E →ₗ[ℝ] E)
    (hL : ∀ s x, p s (L x) ≤ p s x)
    (k s loss base : ℕ) (x : E) (v : Fin k → E) :
    tameJetSize p k s loss base (L x) (fun i => L (v i)) ≤
      tameJetSize p k s loss base x v := by
  unfold tameJetSize
  apply add_le_add
  · exact mul_le_mul (add_le_add le_rfl (hL _ _))
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hL _ _))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (by positivity)
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul (hL _ _)
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun _ _ => hL _ _))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
  {bond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ E} {f : E → ProjectiveLimit F bond}

theorem smoothTameOn_unitIntegralLinearFamily
    (hp : Monotone p) (ht : WithSeminorms p)
    (J : SmoothDirections univ f)
    (hJ : J.TameBounds p (gradedSeminorm F bond))
    (L : ℝ → E →L[ℝ] E)
    (hL : Continuous (fun z : ℝ × E => L z.1 z.2))
    (hcontract : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s x, p s (L a x) ≤ p s x) :
    SmoothTameOn p (gradedSeminorm F bond) univ
      (fun x => projectiveUnitIntegral (fun a => f (L a x))
        ((continuous_smoothDirections_univ J).comp
          (hL.comp (continuous_id.prodMk continuous_const)))) := by
  classical
  refine ⟨smoothDirectionsUnitIntegralLinearFamily J L hL, ?_⟩
  intro k x₀ hx₀
  choose loss base ε hε hb using fun a (ha : a ∈ Icc (0 : ℝ) 1) =>
    hJ k (L a x₀) (mem_univ _)
  let O (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : Set ℝ :=
    {t | p (base a ha) (L t x₀ - L a x₀) < ε a ha / 2}
  have hO (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : O a ha ∈ 𝓝 a := by
    have hc : Continuous (fun t : ℝ => p (base a ha) (L t x₀ - L a x₀)) :=
      (ht.continuous_seminorm (base a ha)).comp
        ((hL.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
    apply hc.continuousAt.preimage_mem_nhds
    apply Iio_mem_nhds
    simpa only [sub_self, map_zero] using half_pos (hε a ha)
  obtain ⟨K, hcover⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).elim_nhds_subcover' O hO
  have hcover' (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      ∃ w ∈ K, a ∈ O w w.property := by
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (hcover ha)
    obtain ⟨hwK, haw⟩ := Set.mem_iUnion.mp hw
    exact ⟨w, hwK, haw⟩
  have hK : K.Nonempty := by
    obtain ⟨w, hw, _⟩ := hcover' 0 ⟨le_rfl, zero_le_one⟩
    exact ⟨w, hw⟩
  let l := K.sup (fun a => loss a a.property)
  let b := K.sup (fun a => base a a.property)
  let δ : ℝ := K.inf' hK (fun a => ε a a.property / 2)
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr
    (fun a ha => half_pos (hε a a.property))
  refine ⟨l, b, δ, hδ, ?_⟩
  intro s hs
  have hconstants (a : ↥K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (univ : Set E),
      p (base a.val a.val.property) (x - L a.val x₀) < ε a.val a.val.property →
      ∀ v : Fin k → E,
        gradedSeminorm F bond s (J.D k x v) ≤
          C * tameJetSize p k s (loss a.val a.val.property) (base a.val a.val.property) x v := by
    exact hb a.val a.val.property s ((Finset.le_sup a.property).trans hs)
  choose C hC hbound using hconstants
  let A : ℝ := ∑ a : ↥K, C a
  have hA : 0 ≤ A := Finset.sum_nonneg (fun a _ => hC a)
  refine ⟨A, hA, ?_⟩
  intro x hx hnear v
  change gradedSeminorm F bond s
    ((smoothDirectionsUnitIntegralLinearFamily J L hL).D k x v) ≤
      A * tameJetSize p k s l b x v
  rw [smoothDirectionsUnitIntegralLinearFamily_jet]
  apply projectiveUnitIntegral_grading_le _ s
    (mul_nonneg hA (tameJetSize_nonneg _ _ _ _ _ _ _))
  intro a ha
  obtain ⟨w, hwK, haw⟩ := hcover' a ha
  let w' : ↥K := ⟨w, hwK⟩
  have hwb : base w w.property ≤ b := Finset.le_sup hwK
  have hwl : loss w w.property ≤ l := Finset.le_sup hwK
  have hδε : δ ≤ ε w w.property / 2 := Finset.inf'_le _ hwK
  have hperturb : p (base w w.property) (L a (x - x₀)) < ε w w.property / 2 :=
    ((hcontract a ha _ _).trans (hp hwb (x - x₀))).trans_lt (hnear.trans_le hδε)
  have hmem : p (base w w.property) (L a x - L w x₀) < ε w w.property := by
    have heq : L a x - L w x₀ = L a (x - x₀) + (L a x₀ - L w x₀) := by
      rw [map_sub]
      abel
    rw [heq]
    have hs' := (map_add_le_add (p (base w w.property))
      (L a (x - x₀)) (L a x₀ - L w x₀)).trans_lt (add_lt_add hperturb haw)
    linarith only [hs']
  have hwA : C w' ≤ A := Finset.single_le_sum (fun a _ => hC a) (Finset.mem_univ w')
  have hsize := (tameJetSize_linear_contraction p (L a).toLinearMap
    (hcontract a ha) k s (loss w w.property) (base w w.property) x v).trans
      (tameJetSize_mono hp hwl hwb k s x v)
  exact (hbound w' (L a x) (mem_univ _) hmem (fun i => L a (v i))).trans
    (mul_le_mul hwA hsize (tameJetSize_nonneg _ _ _ _ _ _ _) hA)

end ContinuousFlexibility.Analysis
