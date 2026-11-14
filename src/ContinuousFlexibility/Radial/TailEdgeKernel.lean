module

public import ContinuousFlexibility.Radial.TailEdgeEnergy

/-!
# Dirichlet Green and Poisson kernel comparisons

The three-point comparison is the pointwise bound used at each insertion
of the potential in the Green series. The linear endpoint heights satisfy
the corresponding two comparisons.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

theorem tailEdgeGreen_comm (a b s t : ℝ) :
    tailEdgeGreen a b s t = tailEdgeGreen a b t s := by
  unfold tailEdgeGreen
  rw [min_comm s t, max_comm s t]

theorem tailEdgeGreen_nonneg {a b s t : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : 0 ≤ tailEdgeGreen a b s t :=
  div_nonneg (mul_nonneg (sub_nonneg.mpr (le_min hs.1 ht.1))
    (sub_nonneg.mpr (max_le hs.2 ht.2))) (sub_nonneg.mpr hab.le)

private theorem tailEdgeGreen_threePoint_of_le {a b s z t : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (hz : z ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    tailEdgeGreen a b s z * tailEdgeGreen a b z t ≤
      tailEdgeGreen a b s t * tailEdgeGreen a b z z := by
  by_cases hzs : z ≤ s
  · have hzt := hzs.trans hst
    have hprod : (z - a) * (b - s) ≤ (s - a) * (b - z) :=
      mul_le_mul (sub_le_sub_right hzs a) (sub_le_sub_left hzs b)
        (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hs.1)
    have hC : 0 ≤ (z - a) * (b - t) * ((b - a)⁻¹) ^ 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr ht.2))
        (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab.le)) 2)
    simp only [tailEdgeGreen, min_eq_right hzs, max_eq_left hzs, min_eq_left hzt,
      max_eq_right hzt, min_eq_left hst, max_eq_right hst, min_self, max_self]
    calc
      _ = ((z - a) * (b - s)) * ((z - a) * (b - t) * ((b - a)⁻¹) ^ 2) := by ring
      _ ≤ ((s - a) * (b - z)) * ((z - a) * (b - t) * ((b - a)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right hprod hC
      _ = _ := by ring
  · have hsz : s ≤ z := le_of_lt (lt_of_not_ge hzs)
    by_cases hzt : z ≤ t
    · simp only [tailEdgeGreen, min_eq_left hsz, max_eq_right hsz, min_eq_left hzt,
        max_eq_right hzt, min_eq_left hst, max_eq_right hst, min_self, max_self]
      apply le_of_eq
      ring
    · have htz : t ≤ z := le_of_lt (lt_of_not_ge hzt)
      have hprod : (t - a) * (b - z) ≤ (z - a) * (b - t) :=
        mul_le_mul (sub_le_sub_right htz a) (sub_le_sub_left htz b)
          (sub_nonneg.mpr hz.2) (sub_nonneg.mpr hz.1)
      have hC : 0 ≤ (s - a) * (b - z) * ((b - a)⁻¹) ^ 2 :=
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hz.2))
          (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab.le)) 2)
      simp only [tailEdgeGreen, min_eq_left hsz, max_eq_right hsz, min_eq_right htz,
        max_eq_left htz, min_eq_left hst, max_eq_right hst, min_self, max_self]
      calc
        _ = ((t - a) * (b - z)) * ((s - a) * (b - z) * ((b - a)⁻¹) ^ 2) := by ring
        _ ≤ ((z - a) * (b - t)) * ((s - a) * (b - z) * ((b - a)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_right hprod hC
        _ = _ := by ring

/-- A Green insertion is bounded by the original kernel times the diagonal. -/
theorem tailEdgeGreen_threePoint {a b s z t : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (hz : z ∈ Icc a b) (ht : t ∈ Icc a b) :
    tailEdgeGreen a b s z * tailEdgeGreen a b z t ≤
      tailEdgeGreen a b s t * tailEdgeGreen a b z z := by
  rcases le_total s t with hst | hts
  · exact tailEdgeGreen_threePoint_of_le hab hs hz ht hst
  · rw [tailEdgeGreen_comm a b s z, tailEdgeGreen_comm a b z t,
      tailEdgeGreen_comm a b s t, mul_comm (tailEdgeGreen a b z s)]
    exact tailEdgeGreen_threePoint_of_le hab ht hz hs hts

def tailEdgeLeftHeight (a b s : ℝ) : ℝ := (b - s) / (b - a)

def tailEdgeRightHeight (a b s : ℝ) : ℝ := (s - a) / (b - a)

theorem tailEdgeGreen_leftHeight {a b s z : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (hz : z ∈ Icc a b) :
    tailEdgeGreen a b s z * tailEdgeLeftHeight a b z ≤
      tailEdgeLeftHeight a b s * tailEdgeGreen a b z z := by
  rcases le_total z s with hzs | hsz
  · simp only [tailEdgeGreen, tailEdgeLeftHeight, min_eq_right hzs, max_eq_left hzs,
      min_self, max_self]
    apply le_of_eq
    ring
  · have hprod : (s - a) * (b - z) ≤ (z - a) * (b - s) :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hsz b) (sub_nonneg.mpr hs.1)).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hsz a) (sub_nonneg.mpr hs.2))
    have hC : 0 ≤ (b - z) * ((b - a)⁻¹) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hz.2) (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab.le)) 2)
    simp only [tailEdgeGreen, tailEdgeLeftHeight, min_eq_left hsz, max_eq_right hsz,
      min_self, max_self]
    calc
      _ = ((s - a) * (b - z)) * ((b - z) * ((b - a)⁻¹) ^ 2) := by ring
      _ ≤ ((z - a) * (b - s)) * ((b - z) * ((b - a)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right hprod hC
      _ = _ := by ring

theorem tailEdgeGreen_rightHeight {a b s z : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (hz : z ∈ Icc a b) :
    tailEdgeGreen a b s z * tailEdgeRightHeight a b z ≤
      tailEdgeRightHeight a b s * tailEdgeGreen a b z z := by
  rcases le_total s z with hsz | hzs
  · simp only [tailEdgeGreen, tailEdgeRightHeight, min_eq_left hsz, max_eq_right hsz,
      min_self, max_self]
    apply le_of_eq
    ring
  · have hprod : (z - a) * (b - s) ≤ (s - a) * (b - z) :=
      mul_le_mul (sub_le_sub_right hzs a) (sub_le_sub_left hzs b)
        (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hs.1)
    have hC : 0 ≤ (z - a) * ((b - a)⁻¹) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hz.1) (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab.le)) 2)
    simp only [tailEdgeGreen, tailEdgeRightHeight, min_eq_right hzs, max_eq_left hzs,
      min_self, max_self]
    calc
      _ = ((z - a) * (b - s)) * ((z - a) * ((b - a)⁻¹) ^ 2) := by ring
      _ ≤ ((s - a) * (b - z)) * ((z - a) * ((b - a)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right hprod hC
      _ = _ := by ring

end ContinuousFlexibility.Radial
