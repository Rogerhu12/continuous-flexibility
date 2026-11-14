module

public import ContinuousFlexibility.Analysis.N04NegativeChartProjectionMixedBounds
public import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# Root projection bounds from a finite parameter representative

The globally smooth inverse coordinate is needed only on a finite plot.
The output is a jet of the actual function on its original parameter
sector, obtained by the exact affine pullback of its joint tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A finite affine representative bounds the genuine sector jet in
its mapped directions. The projection constant is independent of both
parameter spaces and of the selected representative neighborhood. -/
theorem n04NegativeChart_rootProjection_affine_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (odd : Bool) (U : Set X), IsOpen U →
      ∀ (Ω : Set PolarPoint), IsOpen Ω → Convex ℝ Ω → (∀ p ∈ Ω, 0 < p.1) →
      ∀ (f : X × PolarPoint → ℝ), ∀ JF : SmoothDirections (U ×ˢ Ω) f,
      ∀ (center : X) (L : P →L[ℝ] X) (V : Set P), IsOpen V → Convex ℝ V →
      (0 : P) ∈ V → MapsTo (fun y => center + L y) V U →
      ∀ G : P → ℝ × ℝ × ℝ → ℝ,
      (∀ q, ContDiff ℝ ∞ (fun y => G y q)) →
      (∀ y ∈ V, ∀ p ∈ Ω,
        f (center + L y, p) = if odd then rootOddCoefficient (G y) p else rootEven (G y) p) →
      ∀ n : ℕ, ∀ v : Fin n → P,
      ContDiff ℝ ∞ (fun q => iteratedFDeriv ℝ n (fun y => G y q) 0 v) →
      ∀ M : ℝ, 0 ≤ M → ∀ a b : ℕ, a + b ≤ s →
      CSBound (a + b + if odd then 1 else 0)
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
        (fun q => iteratedFDeriv ℝ n (fun y => G y q) 0 v) M →
      ∀ q : PolarPoint, q ∈ Ω → q.1 ∈ Ioc (0 : ℝ) 1 →
      ∀ Q : SmoothDirections U (fun y => mixedDerivative a b (fun p => f (y, p)) q),
        |Q.D n center (fun i => L (v i))| ≤ C * M := by
  obtain ⟨C, hC, hb⟩ := n04NegativeChart_rootProjection_mixedParameter_bound (X := P) s
  refine ⟨C, hC, ?_⟩
  intro odd U hU Ω hΩ hcΩ hpos f JF center L V hV hcV h0 hmap G hG heq
    n v hjet M hM a b hab hraw q hq hq1 Q
  let A : (P × PolarPoint) →L[ℝ] X × PolarPoint :=
    (L.comp (ContinuousLinearMap.fst ℝ P PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ P PolarPoint)
  let c : X × PolarPoint := (center, 0)
  have ha (x : P × PolarPoint) : c + A x = (center + L x.1, x.2) := by
    simp only [c, A, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add]
  have hmaps : MapsTo (fun x => c + A x) (V ×ˢ Ω) (U ×ˢ Ω) := by
    intro x hx
    change c + A x ∈ U ×ˢ Ω
    rw [ha x]
    exact ⟨hmap hx.1, hx.2⟩
  let J : SmoothDirections (V ×ˢ Ω)
      (fun x : P × PolarPoint => f (center + L x.1, x.2)) :=
    (JF.compAffine A c (hV.prod hΩ) hmaps).congrOn
      (fun x _ => congrArg f (ha x))
  let JG : ∀ q, SmoothDirections V (fun y => G y q) :=
    fun q => smoothDirectionsOfContDiffOn hV (hG q).contDiffOn
  have hsame : (fun q => (JG q).D n 0 v) =
      (fun q => iteratedFDeriv ℝ n (fun y => G y q) 0 v) := by
    funext q
    exact congrArg (fun B : P [×n]→L[ℝ] ℝ => B v)
      ((JG q).hasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional hV n h0)
  have hj : ContDiff ℝ ∞ (fun q => (JG q).D n 0 v) := hsame.symm ▸ hjet
  have hr : CSBound (a + b + if odd then 1 else 0)
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (fun q => (JG q).D n 0 v) M := hsame.symm ▸ hraw
  let Q' := Q.compAffine L center hV hmap
  have hbound := hb odd V hV hcV Ω hΩ hcΩ hpos G
    (fun x : P × PolarPoint => f (center + L x.1, x.2)) JG J heq
    n 0 h0 v hj M hM a b hab hr q hq hq1 Q'
  simpa only [Q', SmoothDirections.compAffine_apply, map_zero, add_zero] using hbound

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_affine_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_affine_bound
