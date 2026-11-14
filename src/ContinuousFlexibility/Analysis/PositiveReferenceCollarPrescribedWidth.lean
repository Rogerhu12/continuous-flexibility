module

public import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory

/-!
# The actual positive collar at a prescribed admissible width

This is the same integral primitive as the existing collar factory.
The width is supplied with its explicit finite-jet and mass margins;
its displayed derivative lower bound is retained for later estimates.
This file is a new reconstruction after the workspace reset.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def prescribedPositiveCollarLower (l r δ m κ Lref : ℝ) : ℝ :=
  m * min (min (κ / 2) Lref / m) ((1 / 2) / positiveReferenceMiddleMass l r δ)

/-- The same factory handles a left root or a right root. Only the given
finite root data and the actual reference slope are bounded as inputs. -/
theorem positiveReferenceCollar_family_of_width
    {ι : Type*} {n : ℕ} {A : ι → ℕ → ℝ → ℝ} {Ref : PolarPoint → ℝ}
    {l r δ ρ κ M Lref Mref v m : ℝ} (root : Bool)
    (hlr : l < r) (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hLref : 0 < Lref) (hMref : 0 ≤ Mref) (hm : 0 < m)
    (hδ : 0 < δ) (hδρ : δ < ρ) (hδone : δ ≤ 1) (hgap : 2 * δ < r - l)
    (hsmall : ((n + 1 : ℕ) : ℝ) * M * δ ≤ κ / 2)
    (hmass : 2 * (max (M + ((n + 1 : ℕ) : ℝ) * M) Mref) * δ ≤ m / 2)
    (hA : ∀ i j, j ≤ n + 1 → ContDiff ℝ ∞ (A i j))
    (hAvalue : ∀ i θ, A i 0 θ = if root then v + m else v)
    (hAlow : ∀ i θ, κ ≤ A i 1 θ)
    (hAbound : ∀ i j, 1 ≤ j → j ≤ n + 1 → ∀ θ, |A i j θ| ≤ M)
    (hRef : ContDiff ℝ ∞ Ref)
    (hRefValue : ∀ side, side ≠ root → ∀ θ,
      Ref (if side then r else l, θ) = if side then v + m else v)
    (hRefLow : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        Lref ≤ radialPartial Ref (x, θ))
    (hRefBound : ∀ side, side ≠ root → ∀ x,
      x ∈ Metric.ball (if side then r else l) ρ → ∀ θ,
        |radialPartial Ref (x, θ)| ≤ Mref) :
    let B := prescribedPositiveCollarLower l r δ m κ Lref
    0 < B ∧
      ∀ i : ι,
        let Y := positiveReferenceCollarCoordinate n l r δ v m root (A i) Ref;
        ContDiff ℝ ∞ Y ∧
        (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) ∧
        (∀ (side : Bool) θ, Y (if side then r else l, θ) = if side then v + m else v) ∧
        (∀ k ≤ n + 1, ∀ θ,
          radialBoundaryJet Y (if root then r else l) k θ = A i k θ) ∧
        (∀ side, side ≠ root → ∀ θ, Y =ᶠ[𝓝 (if side then r else l, θ)] Ref) := by
  let Mroot : ℝ := M + ((n + 1 : ℕ) : ℝ) * M
  let Mslope : ℝ := max Mroot Mref
  let L : ℝ := min (κ / 2) Lref
  have hMroot : 0 ≤ Mroot :=
    add_nonneg hM (mul_nonneg (Nat.cast_nonneg _) hM)
  have hMslope : 0 ≤ Mslope := hMroot.trans (le_max_left _ _)
  have hL : 0 < L := lt_min (half_pos hκ) hLref
  let P : ι → Bool → PolarPoint → ℝ := fun i =>
    positiveReferenceCollarField n l r root (A i) Ref
  have hP (i : ι) (side : Bool) : ContDiff ℝ ∞ (P i side) := by
    by_cases hs : side = root
    · simp only [P, positiveReferenceCollarField, if_pos hs]
      exact contDiff_boundaryTaylorPolynomial (hA i) _
    · simpa only [P, positiveReferenceCollarField, if_neg hs] using hRef
  have hPvalue (i : ι) (side : Bool) (θ : ℝ) :
      P i side (if side then r else l, θ) = if side then v + m else v := by
    by_cases hs : side = root
    · subst side
      have he := iteratedDeriv_boundaryTaylorPolynomial (n + 1)
        (if root then r else l) (A i) (k := 0) (Nat.zero_le _) θ
      have he' : boundaryTaylorPolynomial (n + 1) (if root then r else l) (A i)
          (if root then r else l, θ) = A i 0 θ := by
        simpa only [iteratedDeriv_zero] using he
      simpa only [P, positiveReferenceCollarField, if_pos rfl, ite_true] using
        he'.trans (hAvalue i θ)
    · simpa only [P, positiveReferenceCollarField, if_neg hs] using hRefValue side hs θ
  have hPbounds (i : ι) (side : Bool) (x : ℝ)
      (hx : x ∈ Metric.ball (if side then r else l) δ) (θ : ℝ) :
      L ≤ radialPartial (P i side) (x, θ) ∧
        |radialPartial (P i side) (x, θ)| ≤ Mslope := by
    by_cases hs : side = root
    · subst side
      have hdist : |x - (if root then r else l)| ≤ δ := by
        have hd : |x - (if root then r else l)| < δ := by
          simpa only [Metric.mem_ball, Real.dist_eq] using hx
        exact hd.le
      have hb := boundaryTaylorPolynomial_radial_slope_bounds
        hδ.le hδone hM hdist (hAlow i θ) (fun j hj hjn => hAbound i j hj hjn θ) hsmall
      have he : P i root =
          boundaryTaylorPolynomial (n + 1) (if root then r else l) (A i) := by
        simp only [P, positiveReferenceCollarField, if_pos rfl, ite_true]
      rw [he, ← deriv_cylinder_radial_slice
        ((contDiff_boundaryTaylorPolynomial (hA i) _).differentiable (by simp)) x θ]
      exact ⟨(min_le_left _ _).trans hb.1, hb.2.trans (le_max_left _ _)⟩
    · have hxr : x ∈ Metric.ball (if side then r else l) ρ :=
        Metric.ball_subset_ball hδρ.le hx
      have he : P i side = Ref := by
        simp only [P, positiveReferenceCollarField, if_neg hs]
      rw [he]
      exact ⟨(min_le_right _ _).trans (hRefLow side hs x hxr θ),
        (hRefBound side hs x hxr θ).trans (le_max_right _ _)⟩
  have hAP (i : ι) (side : Bool) :
      ContDiff ℝ ∞ (radialPartial (P i side)) :=
    contDiff_cylinder_radialPartial (hP i side)
  let B : ℝ := m * min (L / m) ((1 / 2) / positiveReferenceMiddleMass l r δ)
  have hMiddle : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hgap
  have hB : 0 < B :=
    mul_pos hm (lt_min (div_pos hL hm) (div_pos (by norm_num) hMiddle))
  refine ⟨hB, ?_⟩
  intro i
  let Y := positiveReferenceCollarCoordinate n l r δ v m root (A i) Ref
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_parameterizedPositiveReferenceCoordinate (hAP i) l r δ v m
  have hYlow : ∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x :=
    (parameterizedPositiveReferenceCoordinate_uniform_lower
      (hAP i) hδ hgap hm hL hMslope
      (fun side x hx θ => (hPbounds i side x hx θ).1)
      (fun side x hx θ => (hPbounds i side x hx θ).2) hmass v).2
  have hYgerm (side : Bool) (θ : ℝ) :
      Y =ᶠ[𝓝 (if side then r else l, θ)] P i side :=
    parameterizedPositiveReferenceCoordinate_endpoint_germ
      (hP i) hδ hgap hm.ne' (hPvalue i) side θ
  refine ⟨hY, hYlow, ?_, ?_, ?_⟩
  · intro side θ
    exact (hYgerm side θ).eq_of_nhds.trans (hPvalue i side θ)
  · intro k hk θ
    have he := iteratedDeriv_parameterizedPositiveReferenceCoordinate_endpoint
      (hP i) hδ hgap hm.ne' (hPvalue i) root θ k
    have hroot : P i root =
        boundaryTaylorPolynomial (n + 1) (if root then r else l) (A i) := by
      simp only [P, positiveReferenceCollarField, if_pos rfl, ite_true]
    rw [hroot] at he
    exact he.trans (iteratedDeriv_boundaryTaylorPolynomial (n + 1)
      (if root then r else l) (A i) hk θ)
  · intro side hs θ
    have he : P i side = Ref := by
      simp only [P, positiveReferenceCollarField, if_neg hs]
    exact (hYgerm side θ).trans (Filter.Eventually.of_forall fun p => congrFun he p)

end ContinuousFlexibility.Analysis
