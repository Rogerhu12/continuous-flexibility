import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
import ContinuousFlexibility.Analysis.PositiveEndpointCutoff

/-!
# A relative boundary patch with an independently small collar

The correction is an explicit sum of two cutoff Taylor polynomials of
the actual target minus the reference field. The radius of the cutoff
is independent of the interval width, so a closed set in the interior
can be kept fixed. The reference field is retained everywhere when the
target is the reference field. All requested radial boundary derivatives
are matched exactly.

The construction is scalar and local in its smoothness assumptions. It
will be applied to both entries of a chart at order four and to the
logarithm of its positive height at order three.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology BigOperators

/-- Taylor corrections in two independently small endpoint collars. -/
def n06SmallBoundaryExtension (n : ℕ) (l r δ : ℝ)
    (a b : ℕ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  positiveEndpointCutoff l δ p.1 * boundaryTaylorPolynomial n l a p +
    positiveEndpointCutoff r δ p.1 * boundaryTaylorPolynomial n r b p

theorem n06SmallBoundaryExtension_swap (n : ℕ) (l r δ : ℝ)
    (a b : ℕ → ℝ → ℝ) :
    n06SmallBoundaryExtension n l r δ a b =
      n06SmallBoundaryExtension n r l δ b a := by
  funext p
  exact add_comm _ _

theorem contDiff_n06SmallBoundaryExtension {n : ℕ} {a b : ℕ → ℝ → ℝ}
    (ha : ∀ j ≤ n, ContDiff ℝ ∞ (a j))
    (hb : ∀ j ≤ n, ContDiff ℝ ∞ (b j)) (l r δ : ℝ) :
    ContDiff ℝ ∞ (n06SmallBoundaryExtension n l r δ a b) :=
  (((contDiff_positiveEndpointCutoff l δ).comp contDiff_fst).mul
    (contDiff_boundaryTaylorPolynomial ha l)).add
      (((contDiff_positiveEndpointCutoff r δ).comp contDiff_fst).mul
        (contDiff_boundaryTaylorPolynomial hb r))

private theorem n06_smallBoundaryExtension_first_germ (n : ℕ)
    {l r δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ |l - r|)
    (a b : ℕ → ℝ → ℝ) (θ : ℝ) :
    (fun x => n06SmallBoundaryExtension n l r δ a b (x, θ)) =ᶠ[𝓝 l]
      (fun x => boundaryTaylorPolynomial n l a (x, θ)) := by
  filter_upwards [positiveEndpointCutoff_one_germ l δ,
    positiveEndpointCutoff_zero_germ_of_separation hδ hsep] with x hx hy
  simp only [n06SmallBoundaryExtension, hx, hy, Pi.one_apply,
    Pi.zero_apply, one_mul, zero_mul, add_zero]

/-- Exact matching of every prescribed radial jet at both endpoints. -/
theorem iteratedDeriv_n06SmallBoundaryExtension (n : ℕ)
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    (a b : ℕ → ℝ → ℝ) (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => n06SmallBoundaryExtension n l r δ a b (x, θ))
      (if side then r else l) = (if side then b else a) k θ := by
  have hsep : δ ≤ |l - r| := by
    rw [abs_sub_comm, abs_of_nonneg (show 0 ≤ r - l by linarith)]
    linarith
  cases side with
  | false =>
      have hj := (n06_smallBoundaryExtension_first_germ n hδ hsep a b θ).iteratedDeriv k
      exact hj.eq_of_nhds.trans (iteratedDeriv_boundaryTaylorPolynomial n l a hk θ)
  | true =>
      rw [n06SmallBoundaryExtension_swap]
      have hsep' : δ ≤ |r - l| := by simpa only [abs_sub_comm r l] using hsep
      have hj := (n06_smallBoundaryExtension_first_germ n hδ hsep' b a θ).iteratedDeriv k
      exact hj.eq_of_nhds.trans (iteratedDeriv_boundaryTaylorPolynomial n r b hk θ)

/-- Outside the two collars the correction vanishes on a neighborhood,
including at boundary points of any closed forbidden set. -/
theorem n06SmallBoundaryExtension_zero_germ (n : ℕ)
    {l r δ : ℝ} (hδ : 0 < δ) (a b : ℕ → ℝ → ℝ) {p : ℝ × ℝ}
    (hl : p.1 ∉ Metric.ball l δ) (hr : p.1 ∉ Metric.ball r δ) :
    n06SmallBoundaryExtension n l r δ a b =ᶠ[𝓝 p] 0 := by
  have hL := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hl).comp_tendsto
    (continuous_fst.tendsto p)
  have hR := (positiveEndpointCutoff_zero_germ_of_not_mem_ball hδ hr).comp_tendsto
    (continuous_fst.tendsto p)
  filter_upwards [hL, hR] with q hqL hqR
  simp only [Function.comp_apply, Pi.zero_apply] at hqL hqR
  simp only [n06SmallBoundaryExtension, hqL, hqR, Pi.zero_apply, zero_mul, add_zero]

/-- The actual relative construction. There is no independently assigned
boundary payload: the coefficients are derivatives of `f side - f₀`. -/
def n06RelativeBoundaryPatch (n : ℕ) (l r δ : ℝ)
    (f₀ : ℝ × ℝ → ℝ) (f : Bool → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f₀ p + n06SmallBoundaryExtension n l r δ
    (radialBoundaryJet (fun q => f false q - f₀ q) l)
    (radialBoundaryJet (fun q => f true q - f₀ q) r) p

private theorem n06_relativeBoundaryData_smooth
    {l r : ℝ} {f₀ : ℝ × ℝ → ℝ} {f : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ f₀ (if side then r else l, θ))
    (hf : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (f side) (if side then r else l, θ))
    (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞
      (radialBoundaryJet (fun q => f side q - f₀ q) (if side then r else l) j) :=
  n06_contDiff_radialBoundaryJet_of_axis (fun θ => (hf side θ).sub (h₀ side θ)) j

/-- Ordinary smoothness is preserved at every point where the reference
field is smooth; the target is needed only on the two boundary axes. -/
theorem n06RelativeBoundaryPatch_contDiffAt {n : ℕ} {l r δ : ℝ}
    {f₀ : ℝ × ℝ → ℝ} {f : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ f₀ (if side then r else l, θ))
    (hf : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (f side) (if side then r else l, θ))
    {p : ℝ × ℝ} (hp : ContDiffAt ℝ ∞ f₀ p) :
    ContDiffAt ℝ ∞ (n06RelativeBoundaryPatch n l r δ f₀ f) p :=
  hp.add (contDiff_n06SmallBoundaryExtension
    (fun j _ => n06_relativeBoundaryData_smooth h₀ hf false j)
    (fun j _ => n06_relativeBoundaryData_smooth h₀ hf true j) l r δ).contDiffAt

/-- The constructed field has the actual target jets through the chosen
degree, at either endpoint and at every angle. -/
theorem iteratedDeriv_n06RelativeBoundaryPatch {n : ℕ} {l r δ : ℝ}
    (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    {f₀ : ℝ × ℝ → ℝ} {f : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ f₀ (if side then r else l, θ))
    (hf : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (f side) (if side then r else l, θ))
    (side : Bool) {k : ℕ} (hk : k ≤ n) (θ : ℝ) :
    iteratedDeriv k (fun x => n06RelativeBoundaryPatch n l r δ f₀ f (x, θ))
      (if side then r else l) =
        iteratedDeriv k (fun x => f side (x, θ)) (if side then r else l) := by
  let a := radialBoundaryJet (fun q => f false q - f₀ q) l
  let b := radialBoundaryJet (fun q => f true q - f₀ q) r
  have hbase : ContDiffAt ℝ ∞ (fun x => f₀ (x, θ)) (if side then r else l) :=
    (h₀ side θ).comp (f := fun x : ℝ => (x, θ)) (if side then r else l)
      (contDiffAt_id.prodMk contDiffAt_const)
  have htarget : ContDiffAt ℝ ∞ (fun x => f side (x, θ))
      (if side then r else l) :=
    (hf side θ).comp (f := fun x : ℝ => (x, θ)) (if side then r else l)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hext : ContDiff ℝ ∞ (fun x => n06SmallBoundaryExtension n l r δ a b (x, θ)) :=
    (contDiff_n06SmallBoundaryExtension
      (fun j _ => n06_relativeBoundaryData_smooth h₀ hf false j)
      (fun j _ => n06_relativeBoundaryData_smooth h₀ hf true j) l r δ).comp
        (contDiff_id.prodMk contDiff_const)
  change iteratedDeriv k
    (fun x => f₀ (x, θ) + n06SmallBoundaryExtension n l r δ a b (x, θ))
      (if side then r else l) = _
  rw [iteratedDeriv_fun_add (hbase.of_le (by simp))
    ((hext.of_le (show (k : ℕ∞ω) ≤ ∞ by simp)).contDiffAt),
    iteratedDeriv_n06SmallBoundaryExtension n hδ hgap a b side hk θ]
  have hdata : (if side then b else a) k θ =
      iteratedDeriv k (fun x => f side (x, θ) - f₀ (x, θ))
        (if side then r else l) := by
    cases side <;> rfl
  rw [hdata, iteratedDeriv_fun_sub (htarget.of_le (by simp)) (hbase.of_le (by simp))]
  ring

/-- The reference state is unchanged on the whole plane. -/
theorem n06RelativeBoundaryPatch_self (n : ℕ) (l r δ : ℝ)
    (f₀ : ℝ × ℝ → ℝ) :
    n06RelativeBoundaryPatch n l r δ f₀ (fun _ => f₀) = f₀ := by
  funext p
  simp [n06RelativeBoundaryPatch, n06SmallBoundaryExtension,
    boundaryTaylorPolynomial, radialBoundaryJet, iteratedDeriv_const]

/-- On a closed set avoided by the collars, the new field agrees with the
reference on a full physical neighborhood, hence with all spatial jets. -/
theorem n06RelativeBoundaryPatch_fixed_germ (n : ℕ)
    {l r δ : ℝ} (hδ : 0 < δ) (f₀ : ℝ × ℝ → ℝ) (f : Bool → ℝ × ℝ → ℝ)
    {F : Set ℝ} (hL : Disjoint (Metric.ball l δ) F)
    (hR : Disjoint (Metric.ball r δ) F) {p : ℝ × ℝ} (hp : p.1 ∈ F) :
    n06RelativeBoundaryPatch n l r δ f₀ f =ᶠ[𝓝 p] f₀ := by
  have hl : p.1 ∉ Metric.ball l δ := fun h => (Set.disjoint_left.mp hL) h hp
  have hr : p.1 ∉ Metric.ball r δ := fun h => (Set.disjoint_left.mp hR) h hp
  have hz := n06SmallBoundaryExtension_zero_germ n hδ
    (radialBoundaryJet (fun q => f false q - f₀ q) l)
    (radialBoundaryJet (fun q => f true q - f₀ q) r) hl hr
  filter_upwards [hz] with q hq
  simp only [n06RelativeBoundaryPatch, hq, Pi.zero_apply, add_zero]

/-- The radius is genuinely selected to avoid the supplied closed set.
Every subsequent patch uses this concrete radius. -/
theorem n06_exists_relativeBoundaryPatch_collar
    {F : Set ℝ} (hF : IsClosed F) {l r ε : ℝ}
    (hl : l ∉ F) (hr : r ∉ F) (hlr : l < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ 2 * δ < r - l ∧
      ∀ (n : ℕ) (f₀ : ℝ × ℝ → ℝ) (f : Bool → ℝ × ℝ → ℝ)
        (p : ℝ × ℝ), p.1 ∈ F →
        n06RelativeBoundaryPatch n l r δ f₀ f =ᶠ[𝓝 p] f₀ := by
  obtain ⟨δ, hδ, hδε, hgap, hL, hR⟩ :=
    exists_positiveEndpoint_collars_avoiding hF hl hr hlr hε
  exact ⟨δ, hδ, hδε, hgap,
    fun n f₀ f p hp => n06RelativeBoundaryPatch_fixed_germ n hδ f₀ f hL hR hp⟩

end ContinuousFlexibility.Analysis
