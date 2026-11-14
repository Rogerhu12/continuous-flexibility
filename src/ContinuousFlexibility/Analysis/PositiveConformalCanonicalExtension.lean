module

public import ContinuousFlexibility.Analysis.PositiveConformalJetTransfer
public import ContinuousFlexibility.Geometry.PlanarOrientation

/-!
# A global representative of the actual positive canonical density

A fixed radial bump equals one near the buffered closed physical interval
and has closed support inside the genuine positive smoothness interval.
Only the physical coefficients are extended. The constructed chart,
inverse, and height retain their actual global smoothness. Their inverse
identity proves the Jacobian nonzero, so the extended canonical density
is globally smooth and has the actual germs on the canonical closed strip.
Finite conformal matching supplies its zero jets through order two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One fixed radial cutoff preserves a neighborhood of the whole closed
interval. The cutoff depends only on the four physical endpoints. -/
theorem exists_bufferedRadialCutoff {a l r b : ℝ}
    (hal : a < l) (hlr : l ≤ r) (hrb : r < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Ioo a b ∧
      ∀ x ∈ Icc l r, χ =ᶠ[𝓝 x] 1 := by
  let δ : ℝ := min (l - a) (b - r) / 4
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hrb))
    (by norm_num)
  have hδa : 4 * δ ≤ l - a := by
    dsimp only [δ]
    linarith [min_le_left (l - a) (b - r)]
  have hδb : 4 * δ ≤ b - r := by
    dsimp only [δ]
    linarith [min_le_right (l - a) (b - r)]
  let c : ℝ := (l + r) / 2
  let R : ℝ := (r - l) / 2
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  let χ : ContDiffBump c :=
    { rIn := R + δ
      rOut := R + 2 * δ
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨χ, χ.contDiff, ?_, ?_⟩
  · intro x hx
    rw [χ.tsupport_eq] at hx
    have hx' : |x - c| ≤ R + 2 * δ := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hx
    have hh := abs_le.mp hx'
    dsimp only [c, R] at hh
    constructor <;> linarith
  · intro x hx
    apply χ.eventuallyEq_one_of_mem_ball
    rw [Metric.mem_ball, Real.dist_eq]
    change |x - c| < R + δ
    apply abs_lt.mpr
    dsimp only [c, R]
    constructor <;> linarith [hx.1, hx.2]

private theorem contDiff_bufferedRadialCutoff_mul
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b : ℝ}
    (hs : tsupport χ ⊆ Ioo a b) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (fun p => χ p.1 * f p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ tsupport χ
  · exact (hχ.comp contDiff_fst).contDiffAt.mul
      (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs hp, mem_univ _⟩))
  · have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
      (continuous_fst.tendsto p)
    have he : (fun q : PolarPoint => χ q.1 * f q) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hz] with q hq
      have hq' : χ q.1 = 0 := by
        simpa only [Function.comp_apply, Pi.zero_apply] using hq
      simp only [hq', zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- The actual positive coefficients admit one globally smooth canonical
representative with the proved cubic boundary vanishing. The mapping
condition is the genuine closed-strip inverse property supplied by the
positive scalar factory, not an assumption about arbitrary total inverses. -/
theorem exists_positiveConformal_canonicalExtension
    {a l r b α β : ℝ} (hal : a < l) (hlr : l < r) (hrb : r < b) (hαβ : α < β)
    {A : SymmetricCoefficients}
    (hAa : ContDiffOn ℝ ∞ A.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hAb : ContDiffOn ℝ ∞ A.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hAc : ContDiffOn ℝ ∞ A.c (Ioo a b ×ˢ (univ : Set ℝ)))
    (ha0 : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < A.a p)
    (hdet : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), 0 < A.a p * A.c p - A.b p ^ 2)
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hh : ContDiff ℝ ∞ h)
    (hGF : Function.LeftInverse G F)
    (hmap : MapsTo G (Icc α β ×ˢ (univ : Set ℝ)) (Icc l r ×ˢ (univ : Set ℝ)))
    (hmatch : ∀ side : Bool,
      let c := if side then r else l
      let v := if side then β else α
      (∀ j ≤ 3, ∀ θ, radialBoundaryJet (fun q => (F q).1) c j θ =
        radialBoundaryJet (positiveConformalBoundaryPolynomial 3 c v
          (positiveConformalSpeed A) (positiveConformalShear A) false) c j θ) ∧
      (∀ j ≤ 3, ∀ θ, radialBoundaryJet (fun q => (F q).2) c j θ =
        radialBoundaryJet (positiveConformalBoundaryPolynomial 3 c v
          (positiveConformalSpeed A) (positiveConformalShear A) true) c j θ) ∧
      (∀ j ≤ 2, ∀ θ, radialBoundaryJet h c j θ =
        radialBoundaryJet (positiveConformalHeight A) c j θ)) :
    let C₀ := inverseChartPrincipalCoefficients A F G h
    ∃ B : SymmetricCoefficients,
      ContDiff ℝ ∞ B.a ∧ ContDiff ℝ ∞ B.b ∧ ContDiff ℝ ∞ B.c ∧
      (∀ p ∈ Icc α β ×ˢ (univ : Set ℝ), ∀ᶠ q in 𝓝 p,
        B.a q = C₀.a q ∧ B.b q = C₀.b q ∧ B.c q = C₀.c q) ∧
      ∀ (side : Bool) θ k, k ≤ 2 →
        radialBoundaryJet (fun p => B.a p - 1) (if side then β else α) k θ = 0 ∧
        radialBoundaryJet B.b (if side then β else α) k θ = 0 ∧
        radialBoundaryJet (fun p => B.c p - 1) (if side then β else α) k θ = 0 := by
  obtain ⟨χ, hχ, hχsupport, hχone⟩ := exists_bufferedRadialCutoff hal hlr.le hrb
  let Aext : SymmetricCoefficients :=
    { a := fun p => χ p.1 * A.a p
      b := fun p => χ p.1 * A.b p
      c := fun p => χ p.1 * A.c p }
  have hAe : ContDiff ℝ ∞ Aext.a ∧ ContDiff ℝ ∞ Aext.b ∧ ContDiff ℝ ∞ Aext.c :=
    ⟨contDiff_bufferedRadialCutoff_mul hχ hχsupport hAa,
      contDiff_bufferedRadialCutoff_mul hχ hχsupport hAb,
      contDiff_bufferedRadialCutoff_mul hχ hχsupport hAc⟩
  have hJ (p : PolarPoint) : planeJacobian F p ≠ 0 := by
    have he : G ∘ F = (id : PolarPoint → PolarPoint) := funext hGF
    have hc := planeJacobian_comp (hF.differentiable (by simp) p)
      (hG.differentiable (by simp) (F p))
    have hid : planeJacobian (id : PolarPoint → PolarPoint) p = 1 := by
      simp only [planeJacobian, fderiv_id, ContinuousLinearMap.id_apply,
        one_mul, zero_mul, sub_zero]
    rw [he, hid] at hc
    intro hz
    rw [hz, mul_zero] at hc
    exact one_ne_zero hc
  let B := inverseChartPrincipalCoefficients Aext F G h
  let C₀ := inverseChartPrincipalCoefficients A F G h
  have hD (p : PolarPoint) := contDiffAt_coordinatePrincipalDensity
    (hAe.1.contDiffAt (x := p)) hAe.2.1.contDiffAt hAe.2.2.contDiffAt
    hF.contDiffAt hh.contDiffAt (hJ p)
  have hBa : ContDiff ℝ ∞ B.a :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).1).comp hG
  have hBb : ContDiff ℝ ∞ B.b :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).2.1).comp hG
  have hBc : ContDiff ℝ ∞ B.c :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).2.2).comp hG
  have hsame (p : PolarPoint) (hp : p ∈ Icc α β ×ˢ (univ : Set ℝ)) :
      ∀ᶠ q in 𝓝 p, B.a q = C₀.a q ∧ B.b q = C₀.b q ∧ B.c q = C₀.c q := by
    have he := (hχone (G p).1 (hmap hp).1).comp_tendsto (hG.continuous.fst.tendsto p)
    filter_upwards [he] with q hq
    have hq' : χ (G q).1 = 1 := by
      simpa only [Function.comp_apply, Pi.one_apply] using hq
    simp only [B, C₀, Aext, inverseChartPrincipalCoefficients,
      coordinatePrincipalDensity, coefficientQuadratic, hq', one_mul, and_self]
  refine ⟨B, hBa, hBb, hBc, hsame, ?_⟩
  intro side θ k hk
  let c : ℝ := if side then r else l
  let v : ℝ := if side then β else α
  have hc : ∀ η, (c, η) ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
    intro η
    cases side
    · exact ⟨⟨hal, hlr.trans hrb⟩, mem_univ _⟩
    · exact ⟨⟨hal.trans hlr, hrb⟩, mem_univ _⟩
  have hp : (v, θ) ∈ Icc α β ×ˢ (univ : Set ℝ) := by
    cases side
    · exact ⟨⟨le_rfl, hαβ.le⟩, mem_univ _⟩
    · exact ⟨⟨hαβ.le, le_rfl⟩, mem_univ _⟩
  obtain ⟨hfst, hsnd, hheight⟩ := hmatch side
  have hzero := (positiveConformal_matchingChart_canonicalJets
    (isOpen_Ioo.prod isOpen_univ) hAa hAb hAc ha0 hdet hF hG hh hGF
    c v hc 2 hfst hsnd hheight θ).2.2 k hk
  have hline : Continuous (fun t : ℝ => (t, θ)) := continuous_id.prodMk continuous_const
  have he := (hline.tendsto v).eventually (hsame (v, θ) hp)
  have hea : (fun t : ℝ => B.a (t, θ) - 1) =ᶠ[𝓝 v]
      (fun t => C₀.a (t, θ) - 1) :=
    he.mono fun _ ht => congrArg (fun x : ℝ => x - 1) ht.1
  have heb : (fun t : ℝ => B.b (t, θ)) =ᶠ[𝓝 v] (fun t => C₀.b (t, θ)) :=
    he.mono fun _ ht => ht.2.1
  have hec : (fun t : ℝ => B.c (t, θ) - 1) =ᶠ[𝓝 v]
      (fun t => C₀.c (t, θ) - 1) :=
    he.mono fun _ ht => congrArg (fun x : ℝ => x - 1) ht.2.2
  exact ⟨((hea.iteratedDeriv k).eq_of_nhds).trans hzero.1,
    ((heb.iteratedDeriv k).eq_of_nhds).trans hzero.2.1,
    ((hec.iteratedDeriv k).eq_of_nhds).trans hzero.2.2⟩

end ContinuousFlexibility.Analysis
