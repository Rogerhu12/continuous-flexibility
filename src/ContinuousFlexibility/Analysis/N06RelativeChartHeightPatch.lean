import ContinuousFlexibility.Analysis.N06RelativeBoundaryPatch
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Relative coordinate and positive-height patches

Both chart entries are patched through radial order four. The logarithm
of the height is patched through radial order three and then exponentiated.
Every coefficient in these formulas is an actual derivative of the current
boundary field minus the reference boundary field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology

def n06RelativeChartPatch (l r δ : ℝ)
    (F₀ : ℝ × ℝ → ℝ × ℝ) (F : Bool → ℝ × ℝ → ℝ × ℝ)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  (n06RelativeBoundaryPatch 4 l r δ (fun q => (F₀ q).1)
      (fun side q => (F side q).1) p,
    n06RelativeBoundaryPatch 4 l r δ (fun q => (F₀ q).2)
      (fun side q => (F side q).2) p)

def n06RelativeLogHeightPatch (l r δ : ℝ)
    (H₀ : ℝ × ℝ → ℝ) (H : Bool → ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  n06RelativeBoundaryPatch 3 l r δ (fun q => Real.log (H₀ q))
    (fun side q => Real.log (H side q))

def n06RelativeHeightPatch (l r δ : ℝ)
    (H₀ : ℝ × ℝ → ℝ) (H : Bool → ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (n06RelativeLogHeightPatch l r δ H₀ H p)

theorem n06RelativeChartPatch_contDiffAt {l r δ : ℝ}
    {F₀ : ℝ × ℝ → ℝ × ℝ} {F : Bool → ℝ × ℝ → ℝ × ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ F₀ (if side then r else l, θ))
    (hF : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (F side) (if side then r else l, θ))
    {p : ℝ × ℝ} (hp : ContDiffAt ℝ ∞ F₀ p) :
    ContDiffAt ℝ ∞ (n06RelativeChartPatch l r δ F₀ F) p :=
  (n06RelativeBoundaryPatch_contDiffAt
    (fun side θ => (h₀ side θ).fst) (fun side θ => (hF side θ).fst) hp.fst).prodMk
      (n06RelativeBoundaryPatch_contDiffAt
        (fun side θ => (h₀ side θ).snd) (fun side θ => (hF side θ).snd) hp.snd)

theorem n06RelativeLogHeightPatch_contDiffAt {l r δ : ℝ}
    {H₀ : ℝ × ℝ → ℝ} {H : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ H₀ (if side then r else l, θ))
    (hH : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (H side) (if side then r else l, θ))
    (h₀pos : ∀ (side : Bool) (θ : ℝ), 0 < H₀ (if side then r else l, θ))
    (hHpos : ∀ (side : Bool) (θ : ℝ), 0 < H side (if side then r else l, θ))
    {p : ℝ × ℝ} (hp : ContDiffAt ℝ ∞ H₀ p) (hpos : 0 < H₀ p) :
    ContDiffAt ℝ ∞ (n06RelativeLogHeightPatch l r δ H₀ H) p :=
  n06RelativeBoundaryPatch_contDiffAt
    (fun side θ => (h₀ side θ).log (h₀pos side θ).ne')
    (fun side θ => (hH side θ).log (hHpos side θ).ne')
    (hp.log hpos.ne')

theorem n06RelativeHeightPatch_contDiffAt {l r δ : ℝ}
    {H₀ : ℝ × ℝ → ℝ} {H : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ H₀ (if side then r else l, θ))
    (hH : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (H side) (if side then r else l, θ))
    (h₀pos : ∀ (side : Bool) (θ : ℝ), 0 < H₀ (if side then r else l, θ))
    (hHpos : ∀ (side : Bool) (θ : ℝ), 0 < H side (if side then r else l, θ))
    {p : ℝ × ℝ} (hp : ContDiffAt ℝ ∞ H₀ p) (hpos : 0 < H₀ p) :
    ContDiffAt ℝ ∞ (n06RelativeHeightPatch l r δ H₀ H) p :=
  (n06RelativeLogHeightPatch_contDiffAt h₀ hH h₀pos hHpos hp hpos).exp

theorem n06RelativeHeightPatch_pos (l r δ : ℝ)
    (H₀ : ℝ × ℝ → ℝ) (H : Bool → ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    0 < n06RelativeHeightPatch l r δ H₀ H p := Real.exp_pos _

/-- Both actual chart-coordinate jets are retained through order four. -/
theorem n06RelativeChartPatch_boundary_jets {l r δ : ℝ}
    (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    {F₀ : ℝ × ℝ → ℝ × ℝ} {F : Bool → ℝ × ℝ → ℝ × ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ F₀ (if side then r else l, θ))
    (hF : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (F side) (if side then r else l, θ))
    (side : Bool) {j : ℕ} (hj : j ≤ 4) (θ : ℝ) :
    radialBoundaryJet (fun q => (n06RelativeChartPatch l r δ F₀ F q).1)
        (if side then r else l) j θ =
      radialBoundaryJet (fun q => (F side q).1) (if side then r else l) j θ ∧
    radialBoundaryJet (fun q => (n06RelativeChartPatch l r δ F₀ F q).2)
        (if side then r else l) j θ =
      radialBoundaryJet (fun q => (F side q).2) (if side then r else l) j θ :=
  ⟨iteratedDeriv_n06RelativeBoundaryPatch hδ hgap
      (fun side θ => (h₀ side θ).fst) (fun side θ => (hF side θ).fst) side hj θ,
    iteratedDeriv_n06RelativeBoundaryPatch hδ hgap
      (fun side θ => (h₀ side θ).snd) (fun side θ => (hF side θ).snd) side hj θ⟩

/-- The actual logarithmic-height jets are retained through order three. -/
theorem n06RelativeLogHeightPatch_boundary_jets {l r δ : ℝ}
    (hδ : 0 < δ) (hgap : 2 * δ ≤ r - l)
    {H₀ : ℝ × ℝ → ℝ} {H : Bool → ℝ × ℝ → ℝ}
    (h₀ : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ H₀ (if side then r else l, θ))
    (hH : ∀ (side : Bool) (θ : ℝ), ContDiffAt ℝ ∞ (H side) (if side then r else l, θ))
    (h₀pos : ∀ (side : Bool) (θ : ℝ), 0 < H₀ (if side then r else l, θ))
    (hHpos : ∀ (side : Bool) (θ : ℝ), 0 < H side (if side then r else l, θ))
    (side : Bool) {j : ℕ} (hj : j ≤ 3) (θ : ℝ) :
    radialBoundaryJet (n06RelativeLogHeightPatch l r δ H₀ H)
        (if side then r else l) j θ =
      radialBoundaryJet (fun q => Real.log (H side q))
        (if side then r else l) j θ :=
  iteratedDeriv_n06RelativeBoundaryPatch hδ hgap
    (fun side θ => (h₀ side θ).log (h₀pos side θ).ne')
    (fun side θ => (hH side θ).log (hHpos side θ).ne') side hj θ

theorem n06RelativeChartPatch_self (l r δ : ℝ) (F₀ : ℝ × ℝ → ℝ × ℝ) :
    n06RelativeChartPatch l r δ F₀ (fun _ => F₀) = F₀ := by
  funext p
  apply Prod.ext
  · change n06RelativeBoundaryPatch 4 l r δ (fun q => (F₀ q).1)
      (fun _ q => (F₀ q).1) p = (F₀ p).1
    exact congrFun (n06RelativeBoundaryPatch_self 4 l r δ (fun q => (F₀ q).1)) p
  · change n06RelativeBoundaryPatch 4 l r δ (fun q => (F₀ q).2)
      (fun _ q => (F₀ q).2) p = (F₀ p).2
    exact congrFun (n06RelativeBoundaryPatch_self 4 l r δ (fun q => (F₀ q).2)) p

theorem n06RelativeLogHeightPatch_self (l r δ : ℝ) (H₀ : ℝ × ℝ → ℝ) :
    n06RelativeLogHeightPatch l r δ H₀ (fun _ => H₀) = fun p => Real.log (H₀ p) :=
  n06RelativeBoundaryPatch_self 3 l r δ _

theorem n06RelativeHeightPatch_self {l r δ : ℝ} {H₀ : ℝ × ℝ → ℝ}
    {p : ℝ × ℝ} (hp : 0 < H₀ p) :
    n06RelativeHeightPatch l r δ H₀ (fun _ => H₀) p = H₀ p := by
  rw [n06RelativeHeightPatch, n06RelativeLogHeightPatch_self]
  exact Real.exp_log hp

theorem n06RelativeChartPatch_fixed_germ {l r δ : ℝ} (hδ : 0 < δ)
    (F₀ : ℝ × ℝ → ℝ × ℝ) (F : Bool → ℝ × ℝ → ℝ × ℝ)
    {A : Set ℝ} (hL : Disjoint (Metric.ball l δ) A)
    (hR : Disjoint (Metric.ball r δ) A) {p : ℝ × ℝ} (hp : p.1 ∈ A) :
    n06RelativeChartPatch l r δ F₀ F =ᶠ[𝓝 p] F₀ := by
  filter_upwards [n06RelativeBoundaryPatch_fixed_germ 4 hδ (fun q => (F₀ q).1)
      (fun side q => (F side q).1) hL hR hp,
    n06RelativeBoundaryPatch_fixed_germ 4 hδ (fun q => (F₀ q).2)
      (fun side q => (F side q).2) hL hR hp] with q hq₁ hq₂
  exact Prod.ext hq₁ hq₂

theorem n06RelativeHeightPatch_fixed_germ {l r δ : ℝ} (hδ : 0 < δ)
    (H₀ : ℝ × ℝ → ℝ) (H : Bool → ℝ × ℝ → ℝ)
    {A : Set ℝ} (hL : Disjoint (Metric.ball l δ) A)
    (hR : Disjoint (Metric.ball r δ) A) {p : ℝ × ℝ} (hp : p.1 ∈ A)
    (hcont : ContinuousAt H₀ p) (hpos : 0 < H₀ p) :
    n06RelativeHeightPatch l r δ H₀ H =ᶠ[𝓝 p] H₀ := by
  have hpositive : ∀ᶠ q in 𝓝 p, 0 < H₀ q :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
  filter_upwards [n06RelativeBoundaryPatch_fixed_germ 3 hδ (fun q => Real.log (H₀ q))
      (fun side q => Real.log (H side q)) hL hR hp, hpositive] with q hq hqpos
  change Real.exp (n06RelativeLogHeightPatch l r δ H₀ H q) = H₀ q
  rw [show n06RelativeLogHeightPatch l r δ H₀ H q = Real.log (H₀ q) from hq]
  exact Real.exp_log hqpos

end ContinuousFlexibility.Analysis
