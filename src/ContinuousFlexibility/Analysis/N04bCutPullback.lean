import ContinuousFlexibility.Scalar.Coordinates
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual first derivative of two gauged travel pullbacks

One signed coordinate formula treats the two sides of a cut. At the common
travel value the coordinate derivatives are opposite. The common scalar
gauge supplies the lower-left entry of the transmission matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Signed travel coordinate centered at the common travel value. -/
def n04bSignedTravel (T s : ℝ) (τ : ℝ → ℝ) (p : PolarPoint) : PolarPoint :=
  (T / 2 + s * (τ p.1 - T / 2), p.2)

/-- The actual pullback, multiplied by its radial gauge. -/
def n04bGaugedTravel (T s : ℝ) (τ β : ℝ → ℝ)
    (G : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  β p.1 * G (n04bSignedTravel T s τ p)

/-- A single chain-rule calculation gives both normal derivatives. -/
theorem n04b_radialPartial_gaugedTravel
    (T s r θ τ' β' : ℝ) (τ β : ℝ → ℝ) (G : PolarPoint → ℝ)
    (hτ : HasDerivAt τ τ' r) (hβ : HasDerivAt β β' r)
    (hcut : τ r = T / 2) (hG : DifferentiableAt ℝ G (T / 2, θ)) :
    radialPartial (n04bGaugedTravel T s τ β G) (r, θ) =
      β' * G (T / 2, θ) +
        β r * s * τ' * radialPartial G (T / 2, θ) := by
  let fstL : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let sndL : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have ht : HasFDerivAt (fun p : PolarPoint => τ p.1)
      (τ' • fstL) (r, θ) := by
    simpa only [Function.comp_def, fstL] using
      hτ.comp_hasFDerivAt (r, θ) hasFDerivAt_fst
  have hb : HasFDerivAt (fun p : PolarPoint => β p.1)
      (β' • fstL) (r, θ) := by
    simpa only [Function.comp_def, fstL] using
      hβ.comp_hasFDerivAt (r, θ) hasFDerivAt_fst
  have hs : HasFDerivAt (n04bSignedTravel T s τ)
      ((s • (τ' • fstL)).prod sndL) (r, θ) := by
    exact (((ht.sub_const (T / 2)).const_mul s).const_add (T / 2)).prodMk
      hasFDerivAt_snd
  have he : n04bSignedTravel T s τ (r, θ) = (T / 2, θ) := by
    simp only [n04bSignedTravel, hcut, sub_self, mul_zero, add_zero]
  have hG' : DifferentiableAt ℝ G (n04bSignedTravel T s τ (r, θ)) := by
    rw [he]
    exact hG
  have hc := hG'.hasFDerivAt.comp (r, θ) hs
  have hw := hb.fun_mul hc
  change fderiv ℝ (fun p : PolarPoint => β p.1 * G (n04bSignedTravel T s τ p))
    (r, θ) (1, 0) = _
  rw [hw.fderiv]
  simp only [he, fstL, sndL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one]
  rw [show (s * τ', (0 : ℝ)) = (s * τ') • ((1 : ℝ), (0 : ℝ)) by simp,
    map_smul]
  simp only [smul_eq_mul, radialPartial]
  ring

/-- The reciprocal fourth-root gauge gives the fixed transmission matrix.
The derivative of the travel coordinate is arbitrary and cancels exactly. -/
theorem n04b_gauged_cut_transmission
    (T r θ τ' : ℝ) (τ β : ℝ → ℝ) (G : PolarPoint → ℝ)
    (hr : r ≠ 0) (hτ : HasDerivAt τ τ' r)
    (hβ : HasDerivAt β (-β r / (4 * r)) r)
    (hcut : τ r = T / 2) (hG : DifferentiableAt ℝ G (T / 2, θ)) :
    n04bGaugedTravel T (-1) τ β G (r, θ) =
        n04bGaugedTravel T 1 τ β G (r, θ) ∧
      radialPartial (n04bGaugedTravel T (-1) τ β G) (r, θ) =
        -radialPartial (n04bGaugedTravel T 1 τ β G) (r, θ) -
          n04bGaugedTravel T 1 τ β G (r, θ) / (2 * r) := by
  have hvalue (s : ℝ) :
      n04bGaugedTravel T s τ β G (r, θ) = β r * G (T / 2, θ) := by
    simp only [n04bGaugedTravel, n04bSignedTravel, hcut,
      sub_self, mul_zero, add_zero]
  refine ⟨(hvalue (-1)).trans (hvalue 1).symm, ?_⟩
  rw [n04b_radialPartial_gaugedTravel T (-1) r θ τ' _ τ β G hτ hβ hcut hG,
    n04b_radialPartial_gaugedTravel T 1 r θ τ' _ τ β G hτ hβ hcut hG,
    hvalue 1]
  field_simp [hr]
  <;> ring

end ContinuousFlexibility.Analysis
