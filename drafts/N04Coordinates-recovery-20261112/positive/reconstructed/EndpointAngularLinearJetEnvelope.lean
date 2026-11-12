import ContinuousFlexibility.Analysis.EndpointTaylorLinearJetEnvelope
import ContinuousFlexibility.Analysis.RawEndpointAngularInterpolation
import ContinuousFlexibility.Analysis.TaylorReferenceIdentity
import Mathlib.Algebra.Field.Periodic

/-!
# Actual angular displacement jets at a fixed endpoint width

Monotonicity and the normalized periodic lift give a uniform zeroth
displacement bound. The positive-order input is the ordinary jet of the
actual one-sided endpoint field. The Taylor width remains unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

/-- A normalized monotone lift has displacement bounded by its period,
independently of the particular lift. -/
theorem abs_monotone_periodicLift_displacement_le
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hmono : Monotone f)
    (hperiod : ∀ θ, f (θ + T) = f θ + T) (hzero : f 0 = 0) (θ : ℝ) :
    |f θ - θ| ≤ T := by
  have hD : Function.Periodic (fun t : ℝ => f t - t) T := by
    intro t
    change f (t + T) - (t + T) = f t - t
    rw [hperiod]
    ring
  obtain ⟨t, ht, he⟩ := hD.exists_mem_Ico₀ hT θ
  change f θ - θ = f t - t at he
  have hTvalue : f T = T := by simpa only [zero_add, hzero] using hperiod 0
  have hlow : 0 ≤ f t := by simpa only [hzero] using hmono ht.1
  have hhigh : f t ≤ T := by simpa only [hTvalue] using hmono ht.2.le
  rw [he, abs_le]
  constructor <;> linarith only [ht.1, ht.2, hlow, hhigh]

/-- The actual angular interpolation minus the angular projection is
exactly the same endpoint correction applied to displacement traces. -/
theorem positiveAngularTaylorInterpolation_sub_snd_eq_correction
    (n : ℕ) (l r δ : ℝ) (A : Bool → ℕ → ℝ → ℝ) :
    (fun p : PolarPoint => positiveAngularTaylorInterpolation n l r δ A p - p.2) =
      endpointTaylorCorrection n l r δ (fun side j θ => A side j θ -
        radialBoundaryJet (Prod.snd : PolarPoint → ℝ) (if side then r else l) j θ) := by
  have hpoly (c : ℝ) (side : Bool) (p : PolarPoint) :
      boundaryTaylorPolynomial n c (fun j θ => A side j θ -
        radialBoundaryJet (Prod.snd : PolarPoint → ℝ) c j θ) p =
      boundaryTaylorPolynomial n c (A side) p - p.2 := by
    calc
      _ = boundaryTaylorPolynomial n c (A side) p -
          boundaryTaylorPolynomial n c (radialBoundaryJet (Prod.snd : PolarPoint → ℝ) c) p := by
        simp only [boundaryTaylorPolynomial, sub_div, sub_mul, Finset.sum_sub_distrib]
      _ = _ := by rw [boundaryTaylorPolynomial_snd]
  funext p
  simp only [endpointTaylorCorrection, Bool.false_eq_true, ite_false, ite_true,
    hpoly, positiveAngularTaylorInterpolation, positiveAngularTaylorPatch]
  ring

/-- Only positive ordinary endpoint jets enter the high-data bound.
The zero angular lift is removed exactly; its displacement is controlled
by the actual positive derivative, period, and odd symmetry. -/
theorem exists_rawEndpointAngular_displacement_linear_jet_envelope (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U B δ l r : ℝ},
      1 ≤ U → 1 ≤ B → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ U →
      ∀ (ψ : Bool → PolarPoint → ℝ) (a b : Bool → ℝ),
      (∀ side, a side < b side) →
      (∀ side, (if side then r else l) ∈ Icc (a side) (b side)) →
      (∀ side, ContDiffOn ℝ ∞ (ψ side) (Ioo (a side) (b side) ×ˢ (univ : Set ℝ))) →
      (∀ side θ, ContDiffAt ℝ ∞ (ψ side) (if side then r else l, θ)) →
      (∀ side θ, 0 < angularPartial (ψ side) (if side then r else l, θ)) →
      (∀ side θ, ψ side (if side then r else l, θ + Real.pi) =
        ψ side (if side then r else l, θ) + Real.pi) →
      (∀ side θ, ψ side (if side then r else l, -θ) =
        -ψ side (if side then r else l, θ)) →
      (∀ side k, 1 ≤ k → k ≤ n + N → ∀ θ,
        ‖iteratedFDeriv ℝ k (ψ side) (if side then r else l, θ)‖ ≤ B) →
      ∀ k, k ≤ N → ∀ p : PolarPoint,
        ‖iteratedFDeriv ℝ k (fun q => positiveAngularTaylorInterpolation n l r δ
          (rawEndpointAngularData l r ψ) q - q.2) p‖ ≤ C * U ^ (N + 1) * B := by
  obtain ⟨C, hC, hlinear⟩ := exists_endpointTaylorCorrection_linear_jet_envelope n N
  refine ⟨C * (Real.pi + 2), ?_, ?_⟩
  · have hp : 1 ≤ Real.pi + 2 := by linarith only [Real.pi_pos]
    exact (by norm_num : (1 : ℝ) = 1 * 1).trans_le
      (mul_le_mul hC hp zero_le_one (zero_le_one.trans hC))
  intro U B δ l r hU hB hδ hδone hδinv ψ a b hab hend hψ hroot hangle hperiod hodd hjets k hk p
  let e : Bool → ℝ := fun side => if side then r else l
  let A : Bool → ℕ → ℝ → ℝ := fun side j θ =>
    radialBoundaryJet (ψ side) (e side) j θ -
      radialBoundaryJet (Prod.snd : PolarPoint → ℝ) (e side) j θ
  have hA (side : Bool) (j : ℕ) (_ : j ≤ n) : ContDiff ℝ ∞ (A side j) :=
    (contDiff_radialBoundaryJet_of_contDiffAt (e side) (hroot side) j).sub
      (contDiff_radialBoundaryJet contDiff_snd (e side) j)
  have htrace (side : Bool) (j q : ℕ) (hj : j ≤ n) (hq : q ≤ N)
      (hpos : 1 ≤ j + q) (θ : ℝ) :
      |iteratedDeriv q (radialBoundaryJet (ψ side) (e side) j) θ| ≤ B := by
    rw [iteratedDeriv_radialBoundaryJet_eq_mixedDerivative_on_closedStrip
      (hab side) (hψ side) (hend side) (hroot side)]
    exact (abs_mixedDerivative_le_norm_iteratedFDeriv_on_closedStrip
      (hab side) (hψ side) (hend side) (hroot side θ) j q).trans
      (hjets side (j + q) hpos (by omega) θ)
  have hzero (side : Bool) : A side 0 = fun θ => ψ side (e side, θ) - θ := by
    funext θ
    simp only [A, radialBoundaryJet, iteratedDeriv_zero]
  have hdisp (side : Bool) (θ : ℝ) : |A side 0 θ| ≤ Real.pi := by
    have hder (t : ℝ) : 0 < deriv (fun η => ψ side (e side, η)) t := by
      have he : deriv (fun η => ψ side (e side, η)) t =
          angularPartial (ψ side) (e side, t) :=
        (((hroot side t).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_const t (e side)).prodMk (hasDerivAt_id t))).deriv
      rw [he]
      exact hangle side t
    have h0 : ψ side (e side, 0) = 0 := by
      have he := hodd side 0
      simp only [neg_zero] at he
      linarith only [he]
    rw [hzero]
    exact abs_monotone_periodicLift_displacement_le Real.pi_pos
      (strictMono_of_deriv_pos hder).monotone (hperiod side) h0 θ
  have hcoeff (side : Bool) (j : ℕ) (hj : j ≤ n) (q : ℕ) (hq : q ≤ N) (θ : ℝ) :
      |iteratedDeriv q (A side j) θ| ≤ B + 1 + Real.pi := by
    by_cases hj0 : j = 0
    · subst j
      by_cases hq0 : q = 0
      · subst q
        simpa only [iteratedDeriv_zero] using
          (hdisp side θ).trans (by linarith only [hB] : Real.pi ≤ B + 1 + Real.pi)
      · have hid : |iteratedDeriv q (fun t : ℝ => t) θ| ≤ 1 := by
          rw [iteratedDeriv_fun_id, if_neg hq0]
          split <;> norm_num
        have hraw : |iteratedDeriv q (fun t => ψ side (e side, t)) θ| ≤ B := by
          simpa only [radialBoundaryJet, iteratedDeriv_zero] using
            htrace side 0 q (Nat.zero_le n) hq (by omega) θ
        have hs : ContDiff ℝ ∞ (fun t => ψ side (e side, t)) := by
          simpa only [radialBoundaryJet, iteratedDeriv_zero] using
            contDiff_radialBoundaryJet_of_contDiffAt (e side) (hroot side) 0
        rw [hzero, iteratedDeriv_fun_sub
          ((hs.of_le (show (q : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
          ((contDiff_id.of_le (show (q : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)]
        exact (abs_sub _ _).trans ((add_le_add hraw hid).trans
          (le_add_of_nonneg_right Real.pi_pos.le))
    · have he : A side j = radialBoundaryJet (ψ side) (e side) j := by
        funext t
        simp only [A, radialBoundaryJet, iteratedDeriv_const, if_neg hj0, sub_zero]
      rw [he]
      exact (htrace side j q hj hq (by omega) θ).trans
        (by linarith only [Real.pi_pos])
  have hBbig : 0 < B + 1 + Real.pi := by linarith only [hB, Real.pi_pos]
  have hBlinear : B + 1 + Real.pi ≤ (Real.pi + 2) * B := by
    nlinarith only [hB, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hB)]
  rw [positiveAngularTaylorInterpolation_sub_snd_eq_correction]
  change ‖iteratedFDeriv ℝ k (endpointTaylorCorrection n l r δ A) p‖ ≤ _
  have he := hlinear hU hBbig hδ hδone hδinv l r A hA hcoeff k hk p
  exact he.trans ((mul_le_mul_of_nonneg_left hBlinear
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hU) _))).trans_eq
      (by ring))

end ContinuousFlexibility.Analysis
