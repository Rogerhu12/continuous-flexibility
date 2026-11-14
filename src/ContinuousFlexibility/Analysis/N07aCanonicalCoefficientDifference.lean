module

public import ContinuousFlexibility.Analysis.N07aCanonicalOpenLp

/-!
# Differences of the actual open coefficient multipliers

The value functions and their L² actions are retained exactly. A sharper
geometric bound may be used for a difference even when the record was
constructed using a coarser finite bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficient

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def sub (χ ψ : N07aCanonicalOpenCoefficient S K m) :
    N07aCanonicalOpenCoefficient S K m where
  value := fun p => χ.value p - ψ.value p
  smooth := χ.smooth.sub ψ.smooth
  periodic := by
    intro p hp
    rw [χ.periodic p hp, ψ.periodic p hp]
  bounded := by
    intro a b
    obtain ⟨C, hC, hχ⟩ := χ.bounded a b
    obtain ⟨D, hD, hψ⟩ := ψ.bounded a b
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    filter_upwards [hχ, hψ, n07a_canonicalOpen_ae (S := S) (K := K) (m := m)]
      with p hp hq hU
    have he : (fun p => χ.value p - ψ.value p) =
        fun p => χ.value p + (-1 : ℝ) * ψ.value p := by funext p; ring
    rw [he, n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
      χ.smooth (contDiffOn_const.mul ψ.smooth) a b hU,
      spaces_mixedDerivative_const_mul]
    simp only [neg_one_mul, ← sub_eq_add_neg]
    exact (abs_sub _ _).trans (add_le_add hp hq)

theorem sub_value (χ ψ : N07aCanonicalOpenCoefficient S K m) :
    (χ.sub ψ).value = fun p => χ.value p - ψ.value p := rfl

theorem sub_mul (χ ψ : N07aCanonicalOpenCoefficient S K m) (u : CanonicalL2 S K m) :
    (χ.sub ψ).mul u = χ.mul u - ψ.mul u := by
  apply Lp.ext
  filter_upwards [(χ.sub ψ).mul_ae u, χ.mul_ae u, ψ.mul_ae u,
    Lp.coeFn_sub (χ.mul u) (ψ.mul u)] with p hd hχ hψ hs
  rw [hd, hs, Pi.sub_apply, hχ, hψ, sub_value]
  exact _root_.sub_mul _ _ _

theorem sub_toLp (χ ψ : N07aCanonicalOpenCoefficient S K m) :
    (χ.sub ψ).toLp = χ.toLp - ψ.toLp := by
  apply Lp.ext
  filter_upwards [(χ.sub ψ).toLp_ae, χ.toLp_ae, ψ.toLp_ae,
    Lp.coeFn_sub χ.toLp ψ.toLp] with p hd hχ hψ hs
  rw [hd, hs, Pi.sub_apply, hχ, hψ]
  rfl

theorem mul_norm_le_of_bound (χ : N07aCanonicalOpenCoefficient S K m)
    (M : ℝ) (hM : ∀ᵐ p ∂canonicalMeasure S K m, |χ.value p| ≤ M)
    (u : CanonicalL2 S K m) : ‖χ.mul u‖ ≤ M * ‖u‖ := by
  let hm := n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn
  have he : χ.mul u = n07aCanonicalMultiplier χ.value hm M hM u :=
    Lp.ext ((χ.mul_ae u).trans (n07aCanonicalMultiplier_ae χ.value hm M hM u).symm)
  rw [he]
  exact n07aCanonicalMultiplier_norm_le χ.value hm M hM u

end ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficient
