module

public import ContinuousFlexibility.Analysis.BoundaryTaylorExtension
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Actual mixed jets on a boundary circle

Finite matching of radial jets is an equality of smooth functions of the
angle. Differentiating this equality preserves every angular order. The
identification with the actual mixed derivatives is proved on an open
neighborhood of the boundary circle, using the symmetry of the second
Fréchet derivative of the successive partial derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem deriv_radialSlice_at {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    deriv (fun r : ℝ => F (r, p.2)) p.1 = radialPartial F p := by
  have hline : HasDerivAt (fun r : ℝ => (r, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h := hF.hasFDerivAt.comp_hasDerivAt p.1 hline
  simpa only [Function.comp_def, radialPartial] using h.deriv

private theorem deriv_angularSlice_at {F : PolarPoint → ℝ} {p : PolarPoint}
    (hF : DifferentiableAt ℝ F p) :
    deriv (fun θ : ℝ => F (p.1, θ)) p.2 = angularPartial F p := by
  have hline : HasDerivAt (fun θ : ℝ => (p.1, θ)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  have h := hF.hasFDerivAt.comp_hasDerivAt p.2 hline
  simpa only [Function.comp_def, angularPartial] using h.deriv

/-- Radial differentiation adds one to the radial index on the original
open set; no regularity away from that set is required. -/
theorem radialPartial_mixedDerivative_on_open
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    radialPartial (mixedDerivative a b F) p = mixedDerivative (a + 1) b F p := by
  have hg := contDiffOn_mixedDerivative hU hF a b
  have hd : DifferentiableAt ℝ (mixedDerivative a b F) p :=
    (hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [← deriv_radialSlice_at hd]
  simp only [mixedDerivative, iteratedDeriv_succ]

private theorem partial_eq_of_eqOn {U : Set PolarPoint} (hU : IsOpen U)
    {F G : PolarPoint → ℝ} (h : EqOn F G U)
    {p : PolarPoint} (hp : p ∈ U) (v : PolarPoint) :
    fderiv ℝ F p v = fderiv ℝ G p v := by
  have he : F =ᶠ[𝓝 p] G := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact h hq
  exact congrArg (fun T : PolarPoint →L[ℝ] ℝ => T v) (he.fderiv_eq (𝕜 := ℝ))

/-- Angular differentiation adds one to the angular index on an open
set. The proof uses actual symmetry of the second derivative. -/
theorem angularPartial_mixedDerivative_on_open
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    angularPartial (mixedDerivative a b F) p = mixedDerivative a (b + 1) F p := by
  induction a generalizing p with
  | zero =>
      have hg := contDiffOn_mixedDerivative hU hF 0 b
      have hd : DifferentiableAt ℝ (mixedDerivative 0 b F) p :=
        (hg.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      rw [← deriv_angularSlice_at hd]
      simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ]
  | succ a ih =>
      have hrad : EqOn (radialPartial (mixedDerivative a b F))
          (mixedDerivative (a + 1) b F) U :=
        fun q hq => radialPartial_mixedDerivative_on_open hU hF a b hq
      have hang : EqOn (angularPartial (mixedDerivative a b F))
          (mixedDerivative a (b + 1) F) U :=
        fun q hq => ih hq
      have hg : ContDiffAt ℝ 2 (mixedDerivative a b F) p :=
        ((contDiffOn_mixedDerivative hU hF a b).contDiffAt
          (hU.mem_nhds hp)).of_le (by simp)
      calc
        _ = angularPartial (radialPartial (mixedDerivative a b F)) p :=
          (partial_eq_of_eqOn hU hrad hp (0, 1)).symm
        _ = radialPartial (angularPartial (mixedDerivative a b F)) p :=
          (radial_angular_commute hg).symm
        _ = radialPartial (mixedDerivative a (b + 1) F) p :=
          partial_eq_of_eqOn hU hang hp (1, 0)
        _ = _ := radialPartial_mixedDerivative_on_open hU hF a (b + 1) hp

/-- The angular derivatives of the actual radial boundary trace are the
actual mixed jets at the boundary. -/
theorem iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) (a b : ℕ) (θ : ℝ) :
    iteratedDeriv b (radialBoundaryJet F c a) θ =
      mixedDerivative a b F (c, θ) := by
  induction b generalizing θ with
  | zero =>
      simp only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero]
  | succ b ih =>
      have he : iteratedDeriv b (radialBoundaryJet F c a) =
          fun t : ℝ => mixedDerivative a b F (c, t) := funext ih
      have hd : DifferentiableAt ℝ (mixedDerivative a b F) (c, θ) :=
        ((contDiffOn_mixedDerivative hU hF a b).contDiffAt
          (hU.mem_nhds (hc θ))).differentiableAt (by simp)
      rw [iteratedDeriv_succ, he, deriv_angularSlice_at hd]
      exact angularPartial_mixedDerivative_on_open hU hF a b (hc θ)

/-- Matching the radial jets as functions of the angle matches all
mixed jets with those radial orders. No extra radial loss is introduced. -/
theorem mixedDerivative_boundary_eq_of_radialBoundaryJet_eq
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {F G : PolarPoint → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    (hG : ContDiffOn ℝ ∞ G V) (c : ℝ)
    (hcU : ∀ θ : ℝ, (c, θ) ∈ U) (hcV : ∀ θ : ℝ, (c, θ) ∈ V)
    {n a : ℕ}
    (hjet : ∀ j ≤ n, ∀ θ : ℝ, radialBoundaryJet F c j θ = radialBoundaryJet G c j θ)
    (ha : a ≤ n) (b : ℕ) (θ : ℝ) :
    mixedDerivative a b F (c, θ) = mixedDerivative a b G (c, θ) := by
  rw [← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hU hF c hcU,
    ← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hV hG c hcV,
    funext (hjet a ha)]

/-- Zero radial boundary traces force the whole Fréchet jet to vanish.
This includes all mixed directions, so it can be transported by a chart. -/
theorem iteratedFDeriv_eq_zero_of_radialBoundaryJets_zero
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) {n k : ℕ}
    (hzero : ∀ j ≤ n, ∀ θ : ℝ, radialBoundaryJet F c j θ = 0)
    (hk : k ≤ n) (θ : ℝ) :
    iteratedFDeriv ℝ k F (c, θ) = 0 := by
  have hmix (a b : ℕ) (hab : a + b = k) :
      mixedDerivative a b F (c, θ) = 0 := by
    have ha : a ≤ n := by
      calc
        a ≤ a + b := Nat.le_add_right a b
        _ = k := hab
        _ ≤ n := hk
    have he : radialBoundaryJet F c a = fun _ => 0 := funext (hzero a ha)
    rw [← iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hU hF c hc, he,
      iteratedDeriv_fun_const_zero]
  have hnorm := norm_iteratedFDeriv_le_of_mixedDerivative hU hF k (hc θ)
    (M := 0) le_rfl (fun a b hab => by simp only [hmix a b hab, norm_zero, le_refl])
  exact norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using hnorm) (norm_nonneg _))

/-- A smooth change of variables preserves the finite order of boundary
vanishing. In particular the radial curve of a smooth inverse chart
transports physical boundary vanishing to canonical radial vanishing. -/
theorem iteratedDeriv_comp_eq_zero_of_radialBoundaryJets_zero
    {U : Set PolarPoint} (hU : IsOpen U) {F : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (c : ℝ)
    (hc : ∀ θ : ℝ, (c, θ) ∈ U) {n k : ℕ}
    (hzero : ∀ j ≤ n, ∀ θ : ℝ, radialBoundaryJet F c j θ = 0)
    {γ : ℝ → PolarPoint} {x θ : ℝ} (hγ : ContDiffAt ℝ ∞ γ x)
    (hγx : γ x = (c, θ)) (hk : k ≤ n) :
    iteratedDeriv k (F ∘ γ) x = 0 := by
  have hFat : ContDiffAt ℝ ∞ F (γ x) := by
    rw [hγx]
    exact hF.contDiffAt (hU.mem_nhds (hc θ))
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (i := k) hFat hγ (by simp)]
  apply Finset.sum_eq_zero
  intro π _
  rw [hγx, iteratedFDeriv_eq_zero_of_radialBoundaryJets_zero hU hF c hc hzero
    (π.length_le.trans hk) θ]
  simp only [ContinuousMultilinearMap.zero_apply]

end ContinuousFlexibility.Analysis
