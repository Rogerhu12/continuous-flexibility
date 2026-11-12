import ContinuousFlexibility.Radial.InnerPieceProjection
import ContinuousFlexibility.Radial.InnerBorderTransport
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual source pieces with one central scalar

The scalar belongs only to the distinguished central piece. The source
projections act on the Hilbert product used for adjoints and interface
estimates, and retain the Bessel constant one of the physical L²
restriction. They also cover the unbordered subspace where the scalar is
zero.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  (μ : Measure α) (sets : ι → Set α) (center : ι)

/-- The actual physical restriction and its single central scalar. -/
def innerBorderPieceProjection (i : ι) : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ :=
  ((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ) ∘L
    ((innerL2PieceProjection μ (sets i)).prodMap
      (if i = center then ContinuousLinearMap.id ℝ ℝ else 0)) ∘L
    (innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))

theorem innerBorderPieceProjection_apply (i : ι) (F : InnerBorderL2 μ) :
    innerBorderPieceProjection μ sets center i F =
      WithLp.toLp 2 (innerL2PieceProjection μ (sets i) F.fst,
        if i = center then F.snd else 0) := by
  by_cases hi : i = center <;>
    simp only [innerBorderPieceProjection, hi, ite_true, ite_false,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      innerBorderMaxEquiv_apply, innerBorderMaxEquiv_symm_apply,
      ContinuousLinearMap.coe_prodMap', Prod.map_apply', WithLp.ofLp_fst,
      WithLp.ofLp_snd, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]

theorem innerBorderPieceProjection_norm_sq (i : ι) (F : InnerBorderL2 μ) :
    ‖innerBorderPieceProjection μ sets center i F‖ ^ 2 =
      ‖innerL2PieceProjection μ (sets i) F.fst‖ ^ 2 +
        (if i = center then F.snd else 0) ^ 2 := by
  rw [innerBorderPieceProjection_apply, innerBorderL2_norm_sq]

theorem innerBorderPieceProjection_scalar_sum (F : InnerBorderL2 μ) :
    (∑ i, (if i = center then F.snd else 0) ^ 2) = F.snd ^ 2 := by
  rw [Finset.sum_eq_single center]
  · simp only [eq_self_iff_true, ite_true]
  · intro i _ hi
    simp only [if_neg hi, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · intro hc
    exact (hc (Finset.mem_univ center)).elim

/-- A source is counted once on its physical pieces and once in its
central scalar coordinate. -/
theorem innerBorderPieceProjections_bessel
    (hmeas : ∀ i, MeasurableSet (sets i))
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (F : InnerBorderL2 μ) :
    (∑ i, ‖innerBorderPieceProjection μ sets center i F‖ ^ 2) ≤ ‖F‖ ^ 2 := by
  simp_rw [innerBorderPieceProjection_norm_sq]
  rw [Finset.sum_add_distrib, innerBorderPieceProjection_scalar_sum]
  have hF : ‖F‖ ^ 2 = ‖F.fst‖ ^ 2 + F.snd ^ 2 := by
    exact innerBorderL2_norm_sq (WithLp.ofLp F).1 (WithLp.ofLp F).2
  rw [hF]
  exact add_le_add (innerL2PieceProjections_bessel μ sets hmeas hdis F.fst) (le_refl _)

/-- Different pieces are orthogonal even when they are applied to
different sources. In particular the central scalar never cross-couples
two local blocks. -/
theorem innerBorderPieceProjections_orthogonal
    (hmeas : ∀ i, MeasurableSet (sets i))
    (hdis : Pairwise (fun i k => Disjoint (sets i) (sets k)))
    (F H : InnerBorderL2 μ) {i k : ι} (hik : i ≠ k) :
    ⟪innerBorderPieceProjection μ sets center i F,
      innerBorderPieceProjection μ sets center k H⟫_ℝ = 0 := by
  rw [innerBorderPieceProjection_apply, innerBorderPieceProjection_apply, innerBorderL2_inner,
    innerL2_disjoint_inner_zero (hdis hik) _ _
      (innerL2PieceProjection_supported μ (sets i) (hmeas i) F.fst)
      (innerL2PieceProjection_supported μ (sets k) (hmeas k) H.fst), zero_add]
  by_cases hi : i = center
  · have hk : k ≠ center := fun h => hik (hi.trans h.symm)
    rw [if_pos hi, if_neg hk, mul_zero]
  · rw [if_neg hi, zero_mul]

end ContinuousFlexibility.Radial
