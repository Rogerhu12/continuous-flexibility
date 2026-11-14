module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryInverseStep

/-!
# A common polynomial for actual finite boundary inverse jets

The constants are chosen before the domain, maps, point and material
sample. Induction is on the finite ordinary inverse order. It neither
assumes parameter regularity of a chosen extension nor introduces an
estimate on the unwrapped zeroth angular coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04PositiveGeometry_boundaryInverse_prefix_bound (N m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
      ∀ {U : Set X}, IsOpen U →
      ∀ (f : X × ℝ → E → F) (g : X × ℝ → F → E)
        (q : X × ℝ → F) (L : X × ℝ → F →L[ℝ] E),
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f z) (g z (q z))) →
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g z) (q z)) →
      (∀ z ∈ U ×ˢ univ, f z ∘ g z =ᶠ[𝓝 (q z)] (id : F → F)) →
      (∀ z ∈ U ×ˢ univ,
        (L z).comp (fderiv ℝ (f z) (g z (q z))) = ContinuousLinearMap.id ℝ E) →
      ∀ JL : SmoothDirections (U ×ˢ univ) L,
      ∀ JF : ∀ j, 2 ≤ j → j ≤ m →
        SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (f z) (g z (q z))),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds JL K s d x θ P M H t shift →
      (∀ j hj hjm, N04BoundaryWordBounds (JF j hj hjm) K s d x θ P M H t shift) →
      ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ v : Fin j → F, (∀ i, ‖v i‖ ≤ 1) →
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (g z) (q z) v),
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  classical
  induction m with
  | zero =>
      refine ⟨1, le_rfl, 1, le_rfl, ?_⟩
      intro U hU f g q L hf hg hfg hL JL JF K s d hN x hx θ P
        M H t hM hH hHM ht shift hJL hJF j hj hjm
      omega
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        refine ⟨1, le_rfl, 1, le_rfl, ?_⟩
        intro U hU f g q L hf hg hfg hL JL JF K s d hN x hx θ P
          M H t hM hH hHM ht shift hJL hJF j hj hjm v hv Q
        have he : j = 1 := by omega
        subst j
        simpa only [one_mul, pow_one] using
          n04PositiveGeometry_boundaryInverse_first_bound hf hg hfg hL JL hx hJL v hv Q
      · obtain ⟨A, hA, degree, hd, hprefix⟩ := ih
        obtain ⟨B, hB, exponent, he, hstep⟩ :=
          n04PositiveGeometry_boundaryInverse_step_bound (X := X) (E := E) (F := F)
            N (m + 1) (by omega)
        have hC : 1 ≤ A + B * A ^ exponent := hA.trans
          (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hB)
            (pow_nonneg (zero_le_one.trans hA) _)))
        refine ⟨A + B * A ^ exponent, hC, degree + degree * exponent, by omega, ?_⟩
        intro U hU f g q L hf hg hfg hL JL JF K s d hN x hx θ P
          M H t hM hH hHM ht shift hJL hJF j hj hjm v hv Q
        let R := A * M ^ degree
        have hMR : M ≤ R := by
          calc
            M = M ^ 1 := (pow_one M).symm
            _ ≤ M ^ degree := pow_le_pow_right₀ hM hd
            _ ≤ A * M ^ degree :=
              le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hA
        have hold (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (v : Fin j → F)
            (hv : ∀ i, ‖v i‖ ≤ 1)
            (Q : SmoothDirections (U ×ˢ univ)
              (fun z => iteratedFDeriv ℝ j (g z) (q z) v)) :
            N04BoundaryWordBounds Q K s d x θ P R H t shift :=
          hprefix hU f g q L hf hg hfg hL JL
            (fun j hj hjm => JF j hj (Nat.le_succ_of_le hjm)) K s d hN x hx θ P
            M H t hM hH hHM ht shift hJL
            (fun j hj hjm => hJF j hj (Nat.le_succ_of_le hjm)) j hj hjm v hv Q
        by_cases hjold : j ≤ m
        · apply (hold j hj hjold v hv Q).enlarge hH (zero_le_one.trans ht)
          exact mul_le_mul (le_add_of_nonneg_right
            (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (zero_le_one.trans hA) _)))
            (pow_le_pow_right₀ hM (Nat.le_add_right _ _))
            (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
        · have hej : j = m + 1 := by omega
          subst j
          let JG : ∀ j, 1 ≤ j → j < m + 1 → ∀ v : Fin j → F,
              SmoothDirections (U ×ˢ univ)
                (fun z => iteratedFDeriv ℝ j (g z) (q z) v) :=
            fun j hj hjm v => n04Realization_inverse_finiteJet_directions
              (hU.prod isOpen_univ) hf hg hfg hL JL (m + 1) JF
              j hj hjm.le v
          have hnew := hstep hU f g q L hf hg hfg hL JL JF JG K s d hN x hx θ P
            R H t (hM.trans hMR) hH (hHM.trans hMR) ht shift
            (hJL.enlarge hH (zero_le_one.trans ht) hMR)
            (fun j hj hjm => (hJF j hj hjm).enlarge hH (zero_le_one.trans ht) hMR)
            (fun j hj hjm v hv => hold j hj (by omega) v hv (JG j hj hjm v)) v hv Q
          apply hnew.enlarge hH (zero_le_one.trans ht)
          calc
            B * R ^ exponent = (B * A ^ exponent) * M ^ (degree * exponent) := by
              simp only [R, mul_pow, ← pow_mul, mul_assoc]
            _ ≤ _ := mul_le_mul (le_add_of_nonneg_left (zero_le_one.trans hA))
              (pow_le_pow_right₀ hM (Nat.le_add_left _ _))
              (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)

end ContinuousFlexibility.Analysis
