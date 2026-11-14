module

public import ContinuousFlexibility.Analysis.N06NuFiniteJets
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smoothness and compact derivative bounds for the true finite nu formula

The coordinates are the radius, the two reference profile jets, the two
cutoff jets, the five actual height jets, q, and nu. The actual column
formula from N06NuFiniteJets is smooth wherever its actual discriminant
is positive. Every finite derivative has a uniform bound on a bounded
coordinate set with discriminant at least one half.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff Topology

/-- Ordinary finite coordinates; no function space or choice of a source
representative occurs in the finite nu function. -/
abbrev N06NuJetCoordinates := Fin 12 → ℝ

def n06NuFiniteDiscriminant (v : N06NuJetCoordinates) : ℝ :=
  let w := v 1 * Real.exp (v 11 * v 3)
  (1 + w ^ 2) * (1 - (v 10 * v 7) ^ 2) - (w + v 10 * v 5) ^ 2

def n06NuFiniteJetMap (v : N06NuJetCoordinates) : ℝ :=
  n06NuFiniteJetValue (v 0) (v 1) (v 2) (v 3) (v 4)
    (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)

/-- Smooth parameter substitution into the explicit factored residual.
The positivity premise is exactly the denominator needed by the square root. -/
theorem n06_contDiffAt_residualFiniteJetValue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r w w' a b c d e q : E → ℝ} {x : E}
    (hr : ContDiffAt ℝ ∞ r x) (hw : ContDiffAt ℝ ∞ w x)
    (hw' : ContDiffAt ℝ ∞ w' x) (ha : ContDiffAt ℝ ∞ a x)
    (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x)
    (hd : ContDiffAt ℝ ∞ d x) (he : ContDiffAt ℝ ∞ e x)
    (hq : ContDiffAt ℝ ∞ q x)
    (hpos : 0 < (1 + w x ^ 2) * (1 - (q x * c x) ^ 2) - (w x + q x * a x) ^ 2) :
    ContDiffAt ℝ ∞ (fun y => n06ResidualFiniteJetValue
      (r y) (w y) (w' y) (a y) (b y) (c y) (d y) (e y) (q y)) x := by
  have hE : ContDiffAt ℝ ∞ (fun y => 1 + w y ^ 2) x :=
    contDiffAt_const.add (hw.pow 2)
  have hdisc : ContDiffAt ℝ ∞
      (fun y => (1 + w y ^ 2) * (1 - (q y * c y) ^ 2) -
        (w y + q y * a y) ^ 2) x :=
    (hE.mul (contDiffAt_const.sub ((hq.mul hc).pow 2))).sub
      ((hw.add (hq.mul ha)).pow 2)
  have hden : ContDiffAt ℝ ∞
      (fun y => inverseDThreeHalves
        ((1 + w y ^ 2) * (1 - (q y * c y) ^ 2) - (w y + q y * a y) ^ 2)) x :=
    contDiffAt_const.div (hdisc.mul (hdisc.sqrt hpos.ne'))
      (mul_ne_zero hpos.ne' (Real.sqrt_pos.mpr hpos).ne')
  have hnum : ContDiffAt ℝ ∞
      (fun y => w' y * (a y + e y) + w y * b y +
        q y * ((a y + (1 + w y ^ 2) * e y) * b y -
          (1 + w y ^ 2) * r y * d y ^ 2 +
            w y * w' y * (c y ^ 2 - a y * e y))) x :=
    ((hw'.mul (ha.add he)).add (hw.mul hb)).add
      (hq.mul ((((ha.add (hE.mul he)).mul hb).sub ((hE.mul hr).mul (hd.pow 2))).add
        ((hw.mul hw').mul ((hc.pow 2).sub (ha.mul he)))))
  exact hnum.mul hden

theorem n06NuFiniteDiscriminant_continuous : Continuous n06NuFiniteDiscriminant := by
  have hc (i : Fin 12) : Continuous (fun v : N06NuJetCoordinates => v i) :=
    continuous_apply i
  have hw : Continuous (fun v : N06NuJetCoordinates =>
      v 1 * Real.exp (v 11 * v 3)) :=
    (hc 1).mul (Real.continuous_exp.comp ((hc 11).mul (hc 3)))
  exact ((continuous_const.add (hw.pow 2)).mul
    (continuous_const.sub (((hc 10).mul (hc 7)).pow 2))).sub
      ((hw.add ((hc 10).mul (hc 5))).pow 2)

/-- Differentiating the actual scalar parameter in the ordinary finite
formula preserves smoothness jointly in all remaining finite coordinates. -/
theorem n06NuFiniteJetMap_contDiffAt {v : N06NuJetCoordinates}
    (hpos : 0 < n06NuFiniteDiscriminant v) :
    ContDiffAt ℝ ∞ n06NuFiniteJetMap v := by
  let W : N06NuJetCoordinates × ℝ → ℝ := fun s =>
    s.1 1 * Real.exp (s.2 * s.1 3)
  let Wr : N06NuJetCoordinates × ℝ → ℝ := fun s =>
    (s.1 2 + s.1 1 * (s.2 * s.1 4)) * Real.exp (s.2 * s.1 3)
  let f : N06NuJetCoordinates → ℝ → ℝ := fun x t =>
    n06ResidualFiniteJetValue (x 0) (W (x, t)) (Wr (x, t))
      (x 5) (x 6) (x 7) (x 8) (x 9) (x 10)
  have hc (i : Fin 12) : ContDiffAt ℝ ∞
      (fun s : N06NuJetCoordinates × ℝ => s.1 i) (v, v 11) :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp _ contDiffAt_fst
  have ht : ContDiffAt ℝ ∞ (Prod.snd : N06NuJetCoordinates × ℝ → ℝ) (v, v 11) :=
    contDiffAt_snd
  have hexp : ContDiffAt ℝ ∞
      (fun s : N06NuJetCoordinates × ℝ => Real.exp (s.2 * s.1 3)) (v, v 11) :=
    (ht.mul (hc 3)).exp
  have hW : ContDiffAt ℝ ∞ W (v, v 11) := (hc 1).mul hexp
  have hWr : ContDiffAt ℝ ∞ Wr (v, v 11) :=
    ((hc 2).add ((hc 1).mul (ht.mul (hc 4)))).mul hexp
  have hf : ContDiffAt ℝ ∞ (Function.uncurry f) (v, v 11) :=
    n06_contDiffAt_residualFiniteJetValue (hc 0) hW hWr (hc 5) (hc 6)
      (hc 7) (hc 8) (hc 9) (hc 10) hpos
  have hd : ContDiffAt ℝ ∞
      (fun x : N06NuJetCoordinates => fderiv ℝ (f x) (x 11) (1 : ℝ)) v :=
    (hf.fderiv (contDiff_apply ℝ ℝ (11 : Fin 12)).contDiffAt (by simp)).clm_apply
      contDiffAt_const
  change ContDiffAt ℝ ∞ (fun x : N06NuJetCoordinates => deriv (f x) (x 11)) v
  exact hd

/-- All finite ordinary derivatives have uniform bounds on the bounded
positive-discriminant coordinate set. The constant precedes the actual
state and spatial point. -/
theorem n06NuFiniteJetMap_iteratedFDeriv_bound (B : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : N06NuJetCoordinates,
      ‖v‖ ≤ B → (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant v →
        ‖iteratedFDeriv ℝ n n06NuFiniteJetMap v‖ ≤ C := by
  let K : Set N06NuJetCoordinates := Metric.closedBall 0 B ∩
    {v | (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant v}
  have hK : IsCompact K := (isCompact_closedBall (0 : N06NuJetCoordinates) B).inter_right
    (isClosed_le continuous_const n06NuFiniteDiscriminant_continuous)
  have hc : ContinuousOn (fun v => ‖iteratedFDeriv ℝ n n06NuFiniteJetMap v‖) K := by
    intro v hv
    have hp : 0 < n06NuFiniteDiscriminant v :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hv.2
    exact ((n06NuFiniteJetMap_contDiffAt hp).continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v hv hdisc
  have hvmem : v ∈ K := ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hdisc⟩
  exact (hC ⟨v, hvmem, rfl⟩).trans (le_max_left _ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The coordinates contain the original height pair, including its actual
left cutoff. No radial cutoff is replaced by the reference-data cutoff. -/
def n06ActualNuJetCoordinates (D : ReferenceData) (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (p : PolarPoint) : N06NuJetCoordinates :=
  ![p.1, D.w p.1, deriv D.w p.1, D.chi p.1, deriv D.chi p.1,
    radialPartial (stateU S z.1) p,
    radialPartial (radialPartial (stateU S z.1)) p,
    heightAngular (stateU S z.1) p,
    radialPartial (heightAngular (stateU S z.1)) p,
    angularPartial (heightAngular (stateU S z.1)) p, z.2, z.1.2.1]

theorem n06_nuColumn_eq_finiteJetMap
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    nuColumnField D S C z p = n06NuFiniteJetMap (n06ActualNuJetCoordinates D S z p) :=
  n06_nuColumn_eq_finiteJets hT hS hN01 z hp

/-- On the positive-type region the finite discriminant is literally the
one in the frozen nonlinear geometry conditions. -/
theorem n06_actualNuJetDiscriminant_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hpos : 0 < deriv D.w p.1) :
    n06NuFiniteDiscriminant (n06ActualNuJetCoordinates D S z p) =
      polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  have hg := n06_stateProfile_germ_on_positive hN01.1.1.choose_spec.1.2.2.1.1
    hN01.2.2.2.1 z.1 hpos
  change (1 + (D.w p.1 * Real.exp (z.1.2.1 * D.chi p.1)) ^ 2) *
      (1 - (z.2 * heightAngular (stateU S z.1) p) ^ 2) -
        (D.w p.1 * Real.exp (z.1.2.1 * D.chi p.1) +
          z.2 * radialPartial (stateU S z.1) p) ^ 2 = _
  simp only [polarDiscriminant, stateHeight_heightRadial_of_contDiff_profile hT hS hw,
    stateHeight_heightAngular_of_contDiff_profile hT hS hw, profileEnergy, radialEnergy,
    heightDiscriminant, hg.self_of_nhds]

/-- No new positivity hypothesis is required for the actual nu field:
N01 supplies the same one-half lower bound on its entire physical support. -/
theorem n06_actualNuJetDiscriminant_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hborder : p.1 ∈ tsupport D.chi) :
    (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant (n06ActualNuJetCoordinates D S z p) := by
  have hb : RadialTrueBorder D := hN01.1.2.2.2.1
  rw [n06_actualNuJetDiscriminant_eq hT hS hN01 z (hb.2.2.1 hborder).2]
  exact (hN01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp).2.2.2.2.1

end ContinuousFlexibility.Statements
