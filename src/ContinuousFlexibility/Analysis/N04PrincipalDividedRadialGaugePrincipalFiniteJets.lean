module

public import ContinuousFlexibility.Analysis.N04PrincipalDividedRadialGaugePrincipalTransformation
public import ContinuousFlexibility.Analysis.FiniteFullJetBoundary

/-!
# Finite principal jets for the same fixed reference gauge

The fixed radial inverse and scalar multipliers act on the actual old
principal fields. Common smooth precomposition and multiplication keep
their finite ordinary jet matching. No jets of a separately chosen
inverse map are compared.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem FiniteFullJetMatch.mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {x : E} {f g u v : E → ℝ}
    (hf : FiniteFullJetMatch n x f g) (hu : FiniteFullJetMatch n x u v) :
    FiniteFullJetMatch n x (fun y => f y * u y) (fun y => g y * v y) := by
  have hmul : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) (f x, u x) :=
    contDiffAt_fst.mul contDiffAt_snd
  simpa only [Function.comp_def] using (hf.prodMk hu).comp hmul

def radialGaugePrincipalMultiplier (Y H : ℝ → ℝ) (i : Fin 3)
    (p : PolarPoint) : ℝ :=
  let r := Function.invFun Y p.1
  if i = 0 then H r ^ 2 * deriv Y r
  else if i = 1 then H r ^ 2 else H r ^ 2 / deriv Y r

theorem contDiff_radialGaugePrincipalMultiplier
    {Y H : ℝ → ℝ} (hY : ContDiff ℝ ∞ Y) (hH : ContDiff ℝ ∞ H)
    (hχ : ContDiff ℝ ∞ (positiveReferenceCylinderInverse Y))
    (hYpos : ∀ x, 0 < deriv Y x) (i : Fin 3) :
    ContDiff ℝ ∞ (radialGaugePrincipalMultiplier Y H i) := by
  have hr : ContDiff ℝ ∞ (fun p : PolarPoint => Function.invFun Y p.1) := hχ.fst
  have hh : ContDiff ℝ ∞ (fun p : PolarPoint => H (Function.invFun Y p.1)) :=
    hH.comp hr
  have hd : ContDiff ℝ ∞ (fun p : PolarPoint => deriv Y (Function.invFun Y p.1)) :=
    (contDiff_infty_iff_deriv.mp hY).2.comp hr
  unfold radialGaugePrincipalMultiplier
  dsimp only
  split_ifs with hi0 hi1
  · exact (hh.pow 2).mul hd
  · exact hh.pow 2
  · exact (hh.pow 2).div hd (fun p => (hYpos (Function.invFun Y p.1)).ne')

theorem wholePositiveReferenceGauge_principal_component
    (A : SymmetricCoefficients) {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {Y H : ℝ → ℝ} {l r c d : ℝ}
    (hgeometry : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (hY : ContDiff ℝ ∞ Y) (hYpos : ∀ x, 0 < deriv Y x) (i : Fin 3) :
    canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A
      (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ)
      (wholePositiveReferenceGaugeInverse τ (positiveReferenceCylinderInverse Y))
      (wholePositiveReferenceGaugeHeight (fun q : PolarPoint => H q.1) σ Q)) =
      fun p => radialGaugePrincipalMultiplier Y H i p *
        canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q)
          (positiveReferenceCylinderInverse Y p) := by
  funext p
  have he := wholePositiveReferenceGauge_principal_formula (H := H) A hgeometry hY hYpos p
  simp only [canonicalCoefficientComponent, radialGaugePrincipalMultiplier, ite_apply]
  split_ifs
  · simpa only [positiveReferenceCylinderInverse] using he.1
  · simpa only [positiveReferenceCylinderInverse] using he.2.1
  · simpa only [positiveReferenceCylinderInverse] using he.2.2

/-- The actual current and reference principal fields receive the same
fixed radial gauge. Their finite matching is preserved at its true
inverse image, with no derivative-order loss. -/
theorem finiteFullJetMatch_wholePositiveReferenceGauge_principal
    {A₁ A₀ : SymmetricCoefficients}
    {τ₁ σ₁ τ₀ σ₀ : PolarPoint → PolarPoint} {Q₁ Q₀ : PolarPoint → ℝ}
    {Y H : ℝ → ℝ} {l r c₁ d₁ c₀ d₀ : ℝ} {p : PolarPoint} {n : ℕ}
    (hgeometry₁ : WholePositiveChartGeometry σ₁ τ₁
      (wholePositiveChartHeight σ₁ Q₁) l r c₁ d₁)
    (hgeometry₀ : WholePositiveChartGeometry σ₀ τ₀
      (wholePositiveChartHeight σ₀ Q₀) l r c₀ d₀)
    (hY : ContDiff ℝ ∞ Y) (hH : ContDiff ℝ ∞ H)
    (hχ : ContDiff ℝ ∞ (positiveReferenceCylinderInverse Y))
    (hYpos : ∀ x, 0 < deriv Y x)
    (i : Fin 3)
    (hm : FiniteFullJetMatch n (positiveReferenceCylinderInverse Y p)
      (canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A₁ τ₁ σ₁ Q₁))
      (canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A₀ τ₀ σ₀ Q₀))) :
    FiniteFullJetMatch n p
      (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A₁
        (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₁)
        (wholePositiveReferenceGaugeInverse τ₁ (positiveReferenceCylinderInverse Y))
        (wholePositiveReferenceGaugeHeight (fun q : PolarPoint => H q.1) σ₁ Q₁)))
      (canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A₀
        (wholePositiveReferenceGaugeChart (positiveReferenceCylinderChart Y) σ₀)
        (wholePositiveReferenceGaugeInverse τ₀ (positiveReferenceCylinderInverse Y))
        (wholePositiveReferenceGaugeHeight (fun q : PolarPoint => H q.1) σ₀ Q₀))) := by
  rw [wholePositiveReferenceGauge_principal_component (H := H) A₁ hgeometry₁ hY hYpos i,
    wholePositiveReferenceGauge_principal_component (H := H) A₀ hgeometry₀ hY hYpos i]
  exact (finiteFullJetMatch_refl
    (contDiff_radialGaugePrincipalMultiplier hY hH hχ hYpos i).contDiffAt).mul
      (hm.precomp hχ.contDiffAt)

end ContinuousFlexibility.Analysis
