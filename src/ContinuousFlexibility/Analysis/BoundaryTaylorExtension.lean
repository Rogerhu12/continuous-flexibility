import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp

/-!
# Boundary Taylor extensions on a cylinder

A single fixed smooth cutoff extends prescribed angular boundary data by
radial Taylor polynomials. The two endpoint constructions use the same
formula and are exchanged by swapping the endpoint data. Their supports
are separated after scaling by the actual interval width; no positive
lower bound for that width is assumed.

Degree four gives the coordinate correction in the positive-component
construction, and degree three gives its height correction. Subtracting
the extension of an actual smooth field kills its radial boundary jets
through the selected degree. This module asserts exact interpolation and
smoothness, not a width-independent bound for derivatives of the cutoff.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The fixed cutoff used at either endpoint. -/
def boundaryTaylorCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The radial polynomial with prescribed angular coefficient functions.
The coefficients are the actual radial derivatives, hence the factorials. -/
def boundaryTaylorPolynomial (n : ℕ) (c : ℝ) (a : ℕ → ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    a j p.2 / (j.factorial : ℝ) * (p.1 - c) ^ j

/-- Smooth boundary coefficients give a jointly smooth polynomial. -/
theorem contDiff_boundaryTaylorPolynomial {n : ℕ} {a : ℕ → ℝ → ℝ}
    (ha : ∀ j ≤ n, ContDiff ℝ ∞ (a j)) (c : ℝ) :
    ContDiff ℝ ∞ (boundaryTaylorPolynomial n c a) := by
  unfold boundaryTaylorPolynomial
  apply ContDiff.sum
  intro j hj
  exact (((ha j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).comp
    contDiff_snd).div_const _).mul ((contDiff_fst.sub contDiff_const).pow j)

/-- The radial derivatives at the center are exactly the prescribed data.
This algebraic identity does not require regularity in the angular variable. -/
theorem iteratedDeriv_boundaryTaylorPolynomial (n : ℕ) (c : ℝ)
    (a : ℕ → ℝ → ℝ) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => boundaryTaylorPolynomial n c a (x, θ)) c =
      a k θ := by
  unfold boundaryTaylorPolynomial
  have hmono (j : ℕ) : ContDiff ℝ (k : ℕ∞ω)
      (fun x : ℝ => a j θ / (j.factorial : ℝ) * (x - c) ^ j) := by
    fun_prop
  rw [iteratedDeriv_fun_sum (fun j _ => (hmono j).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field]
  have hshift (j : ℕ) :
      iteratedDeriv k (fun x : ℝ => (x - c) ^ j) c =
        if k = j then (j.factorial : ℝ) else 0 := by
    simpa only [sub_self, iteratedDeriv_fun_pow_zero] using
      congrFun (iteratedDeriv_comp_sub_const k (fun x : ℝ => x ^ j) c) c
  simp_rw [hshift]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
  · intro j _ hj
    rw [if_neg (Ne.symm hj), mul_zero]
  · intro hk'
    exact (hk' (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim

private theorem boundaryTaylorCutoff_one_germ (c w : ℝ) :
    (fun x : ℝ => boundaryTaylorCutoff ((x - c) / w)) =ᶠ[𝓝 c] 1 := by
  have hcont : Continuous (fun x : ℝ => (x - c) / w) :=
    (continuous_id.sub continuous_const).div_const w
  have hlim : Tendsto (fun x : ℝ => (x - c) / w) (𝓝 c) (𝓝 0) := by
    simpa only [sub_self, zero_div] using hcont.tendsto c
  exact boundaryTaylorCutoff.eventuallyEq_one.comp_tendsto hlim

private theorem boundaryTaylorCutoff_zero_germ {t : ℝ} (ht : 1 / 3 < |t|) :
    (boundaryTaylorCutoff : ℝ → ℝ) =ᶠ[𝓝 t] 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  rw [boundaryTaylorCutoff.tsupport_eq]
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero,
    boundaryTaylorCutoff, not_le] using ht

/-- The two endpoint Taylor polynomials, multiplied by copies of one fixed
cutoff at scale `|d-c|`. The middle third of the interval is unchanged. -/
def boundaryTaylorExtension (n : ℕ) (c d : ℝ)
    (a b : ℕ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  boundaryTaylorCutoff ((p.1 - c) / |d - c|) *
      boundaryTaylorPolynomial n c a p +
    boundaryTaylorCutoff ((p.1 - d) / |d - c|) *
      boundaryTaylorPolynomial n d b p

/-- The same construction handles both endpoints. -/
theorem boundaryTaylorExtension_swap (n : ℕ) (c d : ℝ)
    (a b : ℕ → ℝ → ℝ) :
    boundaryTaylorExtension n c d a b = boundaryTaylorExtension n d c b a := by
  funext p
  unfold boundaryTaylorExtension
  rw [abs_sub_comm d c]
  exact add_comm _ _

/-- The extension is globally smooth whenever its finite boundary data are. -/
theorem contDiff_boundaryTaylorExtension {n : ℕ} {a b : ℕ → ℝ → ℝ}
    (ha : ∀ j ≤ n, ContDiff ℝ ∞ (a j))
    (hb : ∀ j ≤ n, ContDiff ℝ ∞ (b j)) (c d : ℝ) :
    ContDiff ℝ ∞ (boundaryTaylorExtension n c d a b) :=
  ((boundaryTaylorCutoff.contDiff.comp
      ((contDiff_fst.sub contDiff_const).div_const |d - c|)).mul
      (contDiff_boundaryTaylorPolynomial ha c)).add
    ((boundaryTaylorCutoff.contDiff.comp
      ((contDiff_fst.sub contDiff_const).div_const |d - c|)).mul
      (contDiff_boundaryTaylorPolynomial hb d))

private theorem iteratedDeriv_boundaryTaylorExtension_first
    (n : ℕ) {c d : ℝ} (hcd : c ≠ d) (a b : ℕ → ℝ → ℝ)
    {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => boundaryTaylorExtension n c d a b (x, θ)) c =
      a k θ := by
  have hratio : |(c - d) / (|d - c|)| = 1 := by
    rw [abs_div, abs_abs, abs_sub_comm c d,
      div_self (abs_ne_zero.mpr (sub_ne_zero.mpr hcd.symm))]
  have hcont : Continuous (fun x : ℝ => (x - d) / |d - c|) :=
    (continuous_id.sub continuous_const).div_const |d - c|
  have hother : (fun x : ℝ => boundaryTaylorCutoff ((x - d) / |d - c|)) =ᶠ[𝓝 c] 0 :=
    (boundaryTaylorCutoff_zero_germ (t := (c - d) / |d - c|)
      (by rw [hratio]; norm_num)).comp_tendsto (hcont.tendsto c)
  have hgerm :
      (fun x => boundaryTaylorExtension n c d a b (x, θ)) =ᶠ[𝓝 c]
        (fun x => boundaryTaylorPolynomial n c a (x, θ)) := by
    filter_upwards [boundaryTaylorCutoff_one_germ c |d - c|, hother] with x hx hy
    simp only [boundaryTaylorExtension, hx, hy, one_mul, zero_mul, add_zero]
  exact (hgerm.iteratedDeriv k).eq_of_nhds.trans
    (iteratedDeriv_boundaryTaylorPolynomial n c a hk θ)

/-- Every prescribed radial jet is matched at either endpoint. Setting
`side = false` selects `c,a`; setting it to `true` selects `d,b`. -/
theorem iteratedDeriv_boundaryTaylorExtension (n : ℕ) {c d : ℝ}
    (hcd : c ≠ d) (a b : ℕ → ℝ → ℝ) (side : Bool)
    {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => boundaryTaylorExtension n c d a b (x, θ))
      (if side then d else c) = (if side then b else a) k θ := by
  cases side with
  | false => exact iteratedDeriv_boundaryTaylorExtension_first n hcd a b hk θ
  | true =>
      rw [boundaryTaylorExtension_swap]
      exact iteratedDeriv_boundaryTaylorExtension_first n hcd.symm b a hk θ

/-- Away from both scaled endpoint neighborhoods, the correction vanishes. -/
theorem boundaryTaylorExtension_eq_zero (n : ℕ) (c d : ℝ)
    (a b : ℕ → ℝ → ℝ) {p : ℝ × ℝ}
    (hc : 1 / 3 ≤ |(p.1 - c) / (|d - c|)|)
    (hd : 1 / 3 ≤ |(p.1 - d) / (|d - c|)|) :
    boundaryTaylorExtension n c d a b p = 0 := by
  have hcut {t : ℝ} (ht : 1 / 3 ≤ |t|) : boundaryTaylorCutoff t = 0 :=
    boundaryTaylorCutoff.zero_of_le_dist (by
      simpa only [Real.dist_eq, sub_zero, boundaryTaylorCutoff] using ht)
  simp only [boundaryTaylorExtension, hcut hc, hcut hd, zero_mul, add_zero]

/-- Actual radial boundary jets, viewed as functions of the angle. -/
def radialBoundaryJet (F : ℝ × ℝ → ℝ) (c : ℝ) (j : ℕ) (θ : ℝ) : ℝ :=
  iteratedDeriv j (fun x => F (x, θ)) c

/-- Boundary restriction preserves smoothness of each actual radial jet. -/
theorem contDiff_radialBoundaryJet {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (c : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (radialBoundaryJet F c j) := by
  have hjet : ContDiff ℝ ∞ (mixedDerivative j 0 F) :=
    contDiffOn_univ.mp (contDiffOn_mixedDerivative isOpen_univ hF.contDiffOn j 0)
  have heq : radialBoundaryJet F c j = fun θ => mixedDerivative j 0 F (c, θ) := by
    funext θ
    simp only [radialBoundaryJet, mixedDerivative, iteratedDeriv_zero]
  rw [heq]
  exact hjet.comp (contDiff_const.prodMk contDiff_id)

/-- The extension of the actual boundary jets of a smooth field is smooth. -/
theorem contDiff_boundaryTaylorExtension_of_field {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (c d : ℝ) :
    ContDiff ℝ ∞ (boundaryTaylorExtension n c d
      (radialBoundaryJet F c) (radialBoundaryJet F d)) :=
  contDiff_boundaryTaylorExtension
    (fun j _ => contDiff_radialBoundaryJet hF c j)
    (fun j _ => contDiff_radialBoundaryJet hF d j) c d

/-- Subtracting the constructed extension kills the actual radial boundary
jets through degree `n`, at both ends with one statement. In particular,
degrees three and four both supply the triple vanishing used in cubic division. -/
theorem iteratedDeriv_sub_boundaryTaylorExtension_eq_zero
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) {c d : ℝ}
    (hcd : c ≠ d) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k
      (fun x => F (x, θ) - boundaryTaylorExtension n c d
        (radialBoundaryJet F c) (radialBoundaryJet F d) (x, θ))
      (if side then d else c) = 0 := by
  have hslice : ContDiff ℝ ∞ (fun x : ℝ => F (x, θ)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hext : ContDiff ℝ ∞ (fun x : ℝ => boundaryTaylorExtension n c d
      (radialBoundaryJet F c) (radialBoundaryJet F d) (x, θ)) :=
    (contDiff_boundaryTaylorExtension_of_field hF n c d).comp
      (contDiff_id.prodMk contDiff_const)
  rw [iteratedDeriv_fun_sub
    (hslice.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    (hext.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    iteratedDeriv_boundaryTaylorExtension n hcd _ _ side hk θ]
  cases side <;> exact sub_self _

end ContinuousFlexibility.Analysis
