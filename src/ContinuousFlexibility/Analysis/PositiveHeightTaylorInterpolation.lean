module

public import ContinuousFlexibility.Analysis.PositiveFiberInterpolationSymmetry
public import ContinuousFlexibility.Analysis.PointwiseCylinderJets
public import ContinuousFlexibility.Analysis.BoundaryTaylorHeight
public import ContinuousFlexibility.Analysis.PositiveEndpointCutoff

/-!
# Positive finite height matching on freely chosen endpoint collars

The two logarithmic Taylor polynomials use the chosen small collar radius,
so the reference height remains exact outside those collars. Positivity is
automatic. Pointwise infinite smoothness of the two raw boundary circles
is sufficient for the angular Taylor data; no common infinite-order
neighborhood is extracted from a pointwise hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def endpointTaylorCorrection (n : ℕ) (l r δ : ℝ)
    (A : Bool → ℕ → ℝ → ℝ) (p : PolarPoint) : ℝ :=
  positiveEndpointCutoff l δ p.1 * boundaryTaylorPolynomial n l (A false) p +
    positiveEndpointCutoff r δ p.1 * boundaryTaylorPolynomial n r (A true) p

theorem contDiff_endpointTaylorCorrection
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ}
    (hA : ∀ side j, j ≤ n → ContDiff ℝ ∞ (A side j)) (l r δ : ℝ) :
    ContDiff ℝ ∞ (endpointTaylorCorrection n l r δ A) :=
  (((contDiff_positiveEndpointCutoff l δ).comp contDiff_fst).mul
    (contDiff_boundaryTaylorPolynomial (hA false) l)).add
    (((contDiff_positiveEndpointCutoff r δ).comp contDiff_fst).mul
      (contDiff_boundaryTaylorPolynomial (hA true) r))

theorem endpointTaylorCorrection_radial_germ
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) (θ : ℝ) :
    (fun x => endpointTaylorCorrection n l r δ A (x, θ)) =ᶠ[
      𝓝 (if side then r else l)]
      (fun x => boundaryTaylorPolynomial n (if side then r else l) (A side) (x, θ)) := by
  let c : ℝ := if side then r else l
  let d : ℝ := if side then l else r
  have hsep : 0 ≤ r - l := by linarith
  have hcd : δ ≤ |c - d| := by
    cases side with
    | false =>
        change δ ≤ |l - r|
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith
    | true =>
        change δ ≤ |r - l|
        rw [abs_of_nonneg hsep]
        linarith
  have hother := positiveEndpointCutoff_zero_germ_of_separation hδ hcd
  filter_upwards [positiveEndpointCutoff_one_germ c δ, hother] with x hx hy
  cases side <;> simp only [c, d, Bool.false_eq_true, ite_false, ite_true] at hx hy ⊢
  <;> simp only [endpointTaylorCorrection, hx, hy, Pi.one_apply, Pi.zero_apply,
    one_mul, zero_mul, add_zero, zero_add]

theorem iteratedDeriv_endpointTaylorCorrection
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (A : Bool → ℕ → ℝ → ℝ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => endpointTaylorCorrection n l r δ A (x, θ))
      (if side then r else l) = A side k θ :=
  ((endpointTaylorCorrection_radial_germ n hδ hgap A side θ).iteratedDeriv k).eq_of_nhds.trans
    (iteratedDeriv_boundaryTaylorPolynomial n (if side then r else l) (A side) hk θ)

theorem endpointTaylorCorrection_angleInvariant
    {n : ℕ} {A : Bool → ℕ → ℝ → ℝ} (τ : ℝ → ℝ)
    (hA : ∀ side j, j ≤ n → ∀ θ, A side j (τ θ) = A side j θ)
    (l r δ x θ : ℝ) :
    endpointTaylorCorrection n l r δ A (x, τ θ) =
      endpointTaylorCorrection n l r δ A (x, θ) := by
  simp only [endpointTaylorCorrection,
    boundaryTaylorPolynomial_angleInvariant τ (hA false),
    boundaryTaylorPolynomial_angleInvariant τ (hA true)]

def positiveHeightTaylorData (l r : ℝ) (href : PolarPoint → ℝ)
    (h : Bool → PolarPoint → ℝ) (side : Bool) : ℕ → ℝ → ℝ :=
  radialBoundaryJet (boundaryHeightLogRatio href (h side)) (if side then r else l)

def positiveHeightTaylorInterpolation (n : ℕ) (l r δ : ℝ)
    (href : PolarPoint → ℝ) (h : Bool → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  href p * Real.exp (endpointTaylorCorrection n l r δ
    (positiveHeightTaylorData l r href h) p)

private theorem positiveHeightTaylor_log_contDiffAt
    {l r : ℝ} {href : PolarPoint → ℝ} {h : Bool → PolarPoint → ℝ}
    (hRef : ContDiff ℝ ∞ href) (hRefPos : ∀ p, 0 < href p)
    (hRaw : ∀ side θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hRawPos : ∀ side θ, 0 < h side (if side then r else l, θ))
    (side : Bool) (θ : ℝ) :
    ContDiffAt ℝ ∞ (boundaryHeightLogRatio href (h side))
      (if side then r else l, θ) := by
  have hquot : ContDiffAt ℝ ∞ (fun p => h side p / href p)
      (if side then r else l, θ) :=
    (hRaw side θ).fun_div hRef.contDiffAt (hRefPos _).ne'
  exact hquot.log (div_pos (hRawPos side θ) (hRefPos _)).ne'

theorem contDiff_positiveHeightTaylorData
    {l r : ℝ} {href : PolarPoint → ℝ} {h : Bool → PolarPoint → ℝ}
    (hRef : ContDiff ℝ ∞ href) (hRefPos : ∀ p, 0 < href p)
    (hRaw : ∀ side θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hRawPos : ∀ side θ, 0 < h side (if side then r else l, θ))
    (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (positiveHeightTaylorData l r href h side j) :=
  contDiff_radialBoundaryJet_of_contDiffAt (if side then r else l)
    (positiveHeightTaylor_log_contDiffAt hRef hRefPos hRaw hRawPos side) j

theorem positiveHeightTaylorInterpolation_smooth_positive
    {l r : ℝ} {href : PolarPoint → ℝ} {h : Bool → PolarPoint → ℝ}
    (hRef : ContDiff ℝ ∞ href) (hRefPos : ∀ p, 0 < href p)
    (hRaw : ∀ side θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hRawPos : ∀ side θ, 0 < h side (if side then r else l, θ))
    (n : ℕ) (δ : ℝ) :
    ContDiff ℝ ∞ (positiveHeightTaylorInterpolation n l r δ href h) ∧
      ∀ p, 0 < positiveHeightTaylorInterpolation n l r δ href h p := by
  have hE := contDiff_endpointTaylorCorrection (n := n)
    (fun side j _ => contDiff_positiveHeightTaylorData hRef hRefPos hRaw hRawPos side j)
    l r δ
  exact ⟨hRef.mul (Real.contDiff_exp.comp hE), fun p => mul_pos (hRefPos p) (Real.exp_pos _)⟩

/-- The chosen collars leave the height exactly equal to the reference
on any forbidden set which they avoid. -/
theorem positiveHeightTaylorInterpolation_eq_reference
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ)
    (href : PolarPoint → ℝ) (h : Bool → PolarPoint → ℝ)
    {p : PolarPoint} (hl : p.1 ∉ Metric.ball l δ) (hr : p.1 ∉ Metric.ball r δ) :
    positiveHeightTaylorInterpolation n l r δ href h p = href p := by
  simp only [positiveHeightTaylorInterpolation, endpointTaylorCorrection,
    positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hl,
    positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hr,
    zero_mul, zero_add, Real.exp_zero, mul_one]

theorem positiveHeightTaylorInterpolation_angleInvariant
    {n : ℕ} {l r δ : ℝ} {href : PolarPoint → ℝ} {h : Bool → PolarPoint → ℝ}
    (τ : ℝ → ℝ) (hRef : ∀ x θ, href (x, τ θ) = href (x, θ))
    (hData : ∀ side j, j ≤ n → ∀ θ,
      positiveHeightTaylorData l r href h side j (τ θ) =
        positiveHeightTaylorData l r href h side j θ) (x θ : ℝ) :
    positiveHeightTaylorInterpolation n l r δ href h (x, τ θ) =
      positiveHeightTaylorInterpolation n l r δ href h (x, θ) := by
  simp only [positiveHeightTaylorInterpolation, hRef,
    endpointTaylorCorrection_angleInvariant τ hData]

/-- The actual finite height jets match the prescribed positive root
height at either end. No equality of density jets is an input. -/
theorem radialBoundaryJet_positiveHeightTaylorInterpolation
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    {href : PolarPoint → ℝ} {h : Bool → PolarPoint → ℝ}
    (hRef : ContDiff ℝ ∞ href) (hRefPos : ∀ p, 0 < href p)
    (hRaw : ∀ side θ, ContDiffAt ℝ ∞ (h side) (if side then r else l, θ))
    (hRawPos : ∀ side θ, 0 < h side (if side then r else l, θ))
    (n : ℕ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    radialBoundaryJet (positiveHeightTaylorInterpolation n l r δ href h)
      (if side then r else l) k θ =
      radialBoundaryJet (h side) (if side then r else l) k θ := by
  let c : ℝ := if side then r else l
  let F : PolarPoint → ℝ := boundaryHeightLogRatio href (h side)
  let E : PolarPoint → ℝ := endpointTaylorCorrection n l r δ
    (positiveHeightTaylorData l r href h)
  have hE : ContDiff ℝ ∞ E := contDiff_endpointTaylorCorrection
    (fun s j _ => contDiff_positiveHeightTaylorData hRef hRefPos hRaw hRawPos s j) l r δ
  have hline : ContDiffAt ℝ ∞ (fun x : ℝ => (x, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hFs : ContDiffAt ℝ ∞ (fun x => F (x, θ)) c :=
    ContDiffAt.fun_comp (f := fun x : ℝ => (x, θ)) (g := F) c
      (positiveHeightTaylor_log_contDiffAt hRef hRefPos hRaw hRawPos side θ) hline
  have hEs : ContDiffAt ℝ ∞ (fun x => E (x, θ)) c :=
    ContDiffAt.fun_comp (f := fun x : ℝ => (x, θ)) (g := E) c hE.contDiffAt hline
  have hRs : ContDiffAt ℝ ∞ (fun x => href (x, θ)) c :=
    ContDiffAt.fun_comp (f := fun x : ℝ => (x, θ)) (g := href) c hRef.contDiffAt hline
  have hjet (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j (fun x => E (x, θ)) c =
        iteratedDeriv j (fun x => F (x, θ)) c :=
    iteratedDeriv_endpointTaylorCorrection n hδ hgap
      (positiveHeightTaylorData l r href h) side hj θ
  have hexp (j : ℕ) (hj : j ≤ n) :
      iteratedDeriv j (fun x => Real.exp (E (x, θ))) c =
        iteratedDeriv j (fun x => Real.exp (F (x, θ))) c := by
    simpa only [Function.comp_def] using
      iteratedDeriv_vcomp_eq_of_finiteJet_eq hEs hFs Real.contDiff_exp.contDiffAt hjet hj
  have heE : ContDiffAt ℝ ∞ (fun x => Real.exp (E (x, θ))) c :=
    Real.contDiff_exp.contDiffAt.fun_comp c hEs
  have heF : ContDiffAt ℝ ∞ (fun x => Real.exp (F (x, θ))) c :=
    Real.contDiff_exp.contDiffAt.fun_comp c hFs
  have hproduct := iteratedDeriv_mul_left_eq_of_finiteJet_eq heE heF hRs hexp hk
  have hRawSlice : ContDiffAt ℝ ∞ (fun x => h side (x, θ)) c :=
    ContDiffAt.fun_comp (f := fun x : ℝ => (x, θ)) (g := h side) c (hRaw side θ) hline
  have hp : ∀ᶠ x in 𝓝 c, 0 < h side (x, θ) :=
    hRawSlice.continuousAt.eventually (Ioi_mem_nhds (hRawPos side θ))
  have hgerm : (fun x => href (x, θ) * Real.exp (F (x, θ))) =ᶠ[𝓝 c]
      (fun x => h side (x, θ)) := by
    filter_upwards [hp] with x hx
    dsimp only [F, boundaryHeightLogRatio]
    rw [Real.exp_log (div_pos hx (hRefPos _)), mul_comm,
      div_mul_cancel₀ _ (hRefPos _).ne']
  exact hproduct.trans (hgerm.iteratedDeriv k).eq_of_nhds

end ContinuousFlexibility.Analysis
