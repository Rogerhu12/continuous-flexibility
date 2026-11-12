import ContinuousFlexibility.Analysis.N07aCanonicalOpenCoefficients
import ContinuousFlexibility.Statements.N07aCanonicalGeometry
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Actual coefficients from unit-piece geometric jets

Affine radial rescaling has an exact derivative formula. Thus the actual
unit-strip bounds in the primitive geometry supply the bounded interior
jet algebra on the original canonical interval. No extension through a
piece endpoint is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem n07a_iteratedDeriv_comp_mul (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x => f (c * x)) =
      fun x => c ^ n * iteratedDeriv n f (c * x) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    funext x
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left,
      smul_eq_mul, iteratedDeriv_succ, pow_succ]
    ring

theorem n07a_iteratedDeriv_comp_affine (f : ℝ → ℝ) (d c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => f (d + c * y)) x =
      c ^ n * iteratedDeriv n f (d + c * x) := by
  rw [n07a_iteratedDeriv_comp_mul (fun y => f (d + y)) c n]
  rw [iteratedDeriv_comp_const_add]

theorem n07a_mixedDerivative_radialAffine (f : PolarPoint → ℝ)
    (d c : ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (d + c * q.1, q.2)) p =
      c ^ a * mixedDerivative a b f (d + c * p.1, p.2) :=
  n07a_iteratedDeriv_comp_affine
    (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) d c a p.1

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def n07aCanonicalUnitInversePoint (K : CanonicalData S) (m : ℕ)
    (p : PolarPoint) : PolarPoint :=
  ((p.1 - K.left m) / (K.right m - K.left m), p.2)

theorem n07aCanonicalUnitInversePoint_maps (hm : K.left m < K.right m) :
    MapsTo (n07aCanonicalUnitInversePoint K m) (canonicalOpen S K m)
      CanonicalGeometry.unitStrip := by
  intro p hp
  have hL : 0 < K.right m - K.left m := sub_pos.mpr hm
  refine ⟨⟨div_pos (sub_pos.mpr hp.1.1) hL, ?_⟩, mem_univ _⟩
  exact (div_lt_one hL).mpr (sub_lt_sub_right hp.1.2 _)

theorem n07aCanonicalUnitInversePoint_contDiff :
    ContDiff ℝ ∞ (n07aCanonicalUnitInversePoint K m) :=
  ((contDiff_fst.sub contDiff_const).div_const _).prodMk contDiff_snd

theorem n07aCanonicalUnitPoint_inverse (hm : K.left m < K.right m) (p : PolarPoint) :
    CanonicalGeometry.canonicalUnitPoint K m (n07aCanonicalUnitInversePoint K m p) = p := by
  have hL : K.right m - K.left m ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  apply Prod.ext
  · change K.left m + (K.right m - K.left m) *
      ((p.1 - K.left m) / (K.right m - K.left m)) = p.1
    field_simp [hL]
    ring
  · rfl

/-- Interior smoothness and bounded jets of the actual rescaling construct
the original open-piece coefficient, retaining its original value function. -/
def n07aCanonicalOpenCoefficientOfUnit (hm : K.left m < K.right m)
    (f : PolarPoint → ℝ)
    (hf : ContDiffOn ℝ ∞ (f ∘ CanonicalGeometry.canonicalUnitPoint K m)
      CanonicalGeometry.unitStrip)
    (hperiod : ∀ p ∈ CanonicalGeometry.unitStrip,
      f (CanonicalGeometry.canonicalUnitPoint K m (p + (0, Real.pi))) =
        f (CanonicalGeometry.canonicalUnitPoint K m p))
    (hbound : ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ CanonicalGeometry.unitStrip,
      |mixedDerivative a b (f ∘ CanonicalGeometry.canonicalUnitPoint K m) p| ≤ B) :
    N07aCanonicalOpenCoefficient S K m := by
  let g := f ∘ CanonicalGeometry.canonicalUnitPoint K m
  let c := (K.right m - K.left m)⁻¹
  let d := -(K.left m) * c
  have haffine (p : PolarPoint) : n07aCanonicalUnitInversePoint K m p =
      (d + c * p.1, p.2) := by
    apply Prod.ext
    · change (p.1 - K.left m) / (K.right m - K.left m) =
        -(K.left m) * (K.right m - K.left m)⁻¹ + (K.right m - K.left m)⁻¹ * p.1
      rw [div_eq_mul_inv]
      ring
    · rfl
  have he (p : PolarPoint) : g (n07aCanonicalUnitInversePoint K m p) = f p :=
    congrArg f (n07aCanonicalUnitPoint_inverse hm p)
  have hfun : f = fun p => g (d + c * p.1, p.2) := by
    funext p
    exact (he p).symm.trans (congrArg g (haffine p))
  refine ⟨f, ?_, ?_, ?_⟩
  · have hs := hf.comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
      (n07aCanonicalUnitInversePoint_maps hm)
    exact hs.congr (fun p _ => (he p).symm)
  · intro p hp
    have hq := n07aCanonicalUnitInversePoint_maps hm hp
    have h := hperiod (n07aCanonicalUnitInversePoint K m p) hq
    have hshift : n07aCanonicalUnitInversePoint K m (p + (0, Real.pi)) =
        n07aCanonicalUnitInversePoint K m p + (0, Real.pi) := by
      ext <;> simp [n07aCanonicalUnitInversePoint]
    calc
      f (p + (0, Real.pi)) = g (n07aCanonicalUnitInversePoint K m (p + (0, Real.pi))) :=
        (he _).symm
      _ = g (n07aCanonicalUnitInversePoint K m p + (0, Real.pi)) := congrArg g hshift
      _ = g (n07aCanonicalUnitInversePoint K m p) := h
      _ = f p := he p
  · intro a b
    obtain ⟨B, hB, hBb⟩ := hbound a b
    refine ⟨|c| ^ a * B, mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, ?_⟩
    filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
    rw [hfun, n07a_mixedDerivative_radialAffine, abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
    rw [← haffine]
    exact hBb _ (n07aCanonicalUnitInversePoint_maps hm hp)

end ContinuousFlexibility.Analysis
