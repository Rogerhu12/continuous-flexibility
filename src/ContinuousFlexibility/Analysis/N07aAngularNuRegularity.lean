import ContinuousFlexibility.Analysis.N07aNuSupport
import ContinuousFlexibility.Analysis.N07aCoefficientSymmetry
import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral
import ContinuousFlexibility.Scalar.S04CalculusProof

/-!
# Spatial smoothness of the actual distinguished parameter column

The profile depends on the distinguished scalar by an explicit exponential.
The real radial primitive and the removable scalar residual are therefore
jointly smooth in that scalar and the physical point. Differentiating that
actual residual gives the original `nuColumnField`, including at construction
parameter zero and across every artificial radial cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem n07a_periodic_height_jets {f : PolarPoint → ℝ} {t : ℝ}
    (hf : Function.Periodic f (0, t)) :
    Function.Periodic (heightRadial f) (0, t) ∧
      Function.Periodic (heightAngular f) (0, t) ∧
      Function.Periodic (radialPartial (heightRadial f)) (0, t) ∧
      Function.Periodic (radialPartial (heightAngular f)) (0, t) ∧
      Function.Periodic (angularPartial (heightAngular f)) (0, t) := by
  have hr : Function.Periodic (heightRadial f) (0, t) := periodic_radialPartial hf
  have hθ : Function.Periodic (heightAngular f) (0, t) := by
    intro p
    simp only [heightAngular, periodic_angularPartial hf p, Prod.fst_add, add_zero]
  exact ⟨hr, hθ, periodic_radialPartial hr, periodic_radialPartial hθ,
    periodic_angularPartial hθ⟩

/-- Periodicity is an exact algebraic property of the actual residual,
including the removable parameter value and totalized quotients. -/
theorem n07a_normalizedHeightResidual_periodic (w : ℝ → ℝ)
    {f g : PolarPoint → ℝ} {t : ℝ}
    (hf : Function.Periodic f (0, t)) (hg : Function.Periodic g (0, t)) (q : ℝ) :
    Function.Periodic (normalizedHeightResidual w f g q) (0, t) := by
  have hE : Function.Periodic (profileEnergy w) (0, t) := by
    intro p
    simp only [profileEnergy, Prod.fst_add, add_zero]
  have hEr := periodic_radialPartial hE
  have hjf := n07a_periodic_height_jets hf
  have hjg := n07a_periodic_height_jets hg
  have htrial : Function.Periodic (heightFamily f g q) (0, t) := by
    intro p
    simp only [heightFamily, hf p, hg p]
  have hjtrial := n07a_periodic_height_jets htrial
  intro p
  simp only [normalizedHeightResidual, polarResidualVariation,
    polarCurvatureNumeratorVariation, polarCoordinateResidual, polarCurvatureNumerator,
    polarDiscriminant, hE p, hEr p,
    hjf.1 p, hjf.2.1 p, hjf.2.2.1 p, hjf.2.2.2.1 p, hjf.2.2.2.2 p,
    hjg.1 p, hjg.2.1 p, hjg.2.2.1 p, hjg.2.2.2.1 p, hjg.2.2.2.2 p,
    hjtrial.1 p, hjtrial.2.1 p, hjtrial.2.2.1 p, hjtrial.2.2.2.1 p,
    hjtrial.2.2.2.2 p, polarDiscriminantVariation, Prod.fst_add, add_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_stateProfile_nu_exp (x : AnnularState S) (ν r : ℝ) :
    stateProfile D S C (x.1, (ν, x.2.2)) r =
      stateProfile D S C x r * Real.exp ((ν - x.2.1) * D.chi r) := by
  simp only [stateProfile, stateKappa]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem n07a_stateProfile_nu_contDiff
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => stateProfile D S C (x.1, (p.1, x.2.2)) p.2) := by
  have hχ : ContDiff ℝ ∞ D.chi := h01.1.2.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT h01 x
  have he : (fun p : ℝ × ℝ => stateProfile D S C (x.1, (p.1, x.2.2)) p.2) =
      fun p => stateProfile D S C x p.2 * Real.exp ((p.1 - x.2.1) * D.chi p.2) :=
    funext fun p => n07a_stateProfile_nu_exp x p.1 p.2
  rw [he]
  exact (hw.comp contDiff_snd).mul
    (((contDiff_fst.sub contDiff_const).mul (hχ.comp contDiff_snd)).exp)

theorem n07a_stateRadialHeight_nu_contDiff
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => stateRadialHeight D S C (x.1, (p.1, x.2.2)) p.2) :=
  contDiff_parametric_primitive (n07a_stateProfile_nu_contDiff hS hT h01 x) D.b

theorem n07a_scalarResidual_nu_contDiffAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (fun s : ℝ × PolarPoint =>
      scalarResidualField D S C ((z.1.1, (s.1, z.1.2.2)), z.2) s.2) (z.1.2.1, p) := by
  let W : ℝ × ℝ → ℝ := fun s => stateProfile D S C (z.1.1, (s.1, z.1.2.2)) s.2
  let H : ℝ × ℝ → ℝ := fun s => stateRadialHeight D S C (z.1.1, (s.1, z.1.2.2)) s.2
  let Z : ℝ × PolarPoint → ℝ := fun s => H (s.1, s.2.1)
  let V : ℝ × PolarPoint → ℝ := fun s => stateU S z.1 s.2
  have hW : ContDiff ℝ ∞ W := n07a_stateProfile_nu_contDiff hS hT h01 z.1
  have hH : ContDiff ℝ ∞ H := n07a_stateRadialHeight_nu_contDiff hS hT h01 z.1
  have hZ : ContDiff ℝ ∞ Z := hH.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hV : ContDiff ℝ ∞ V := (neighborhood_stateU_contDiff hT hS z.1).comp contDiff_snd
  have hHW (ν r : ℝ) : HasDerivAt (fun t => H (ν, t)) (W (ν, r)) r :=
    stateRadialHeight_hasDerivAt_of_contDiff
      (contDiff_stateProfile_of_n01 hS hT h01 (z.1.1, (ν, z.1.2.2))) r
  have hzero : ∀ᶠ ν in 𝓝 z.1.2.1, ∀ y : PolarPoint, y.1 ≠ 0 →
      polarCurvatureNumerator (fun r => W (ν, r)) (fun y => Z (ν, y)) y = 0 := by
    apply Eventually.of_forall
    intro ν y _
    exact Radial.polarCurvatureNumerator_radialHeightField (hHW ν)
      ((hW.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y.1)
  have hrad : p.1 ≠ 0 := ((h01.1.1.choose_spec.1.1).trans hp.1.1).ne'
  have hΔ : 0 < polarDiscriminant (fun r => W (z.1.2.1, r))
      (heightFamily (fun y => Z (z.1.2.1, y)) (fun y => V (z.1.2.1, y)) z.2) p := by
    have hbound := (h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp).2.2.2.2.1
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hbound
  exact contDiffAt_parameter_normalizedHeightResidual hW hZ hV contDiff_const hzero hrad hΔ

theorem n07a_nuColumnField_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiffOn ℝ ∞ (nuColumnField D S C z) (annularOpen D) := by
  have hfun : nuColumnField D S C z = fun x =>
      deriv (fun q => scalarResidualField D S C ((z.1.1, (q, z.1.2.2)), z.2) x)
        z.1.2.1 := by
    funext x
    rfl
  rw [hfun]
  intro p hp
  have h := contDiffAt_parameter_fderiv (n07a_scalarResidual_nu_contDiffAt hS hT h01 hz hs hp)
  have he := (h.clm_apply (contDiffAt_const (c := (1 : ℝ)))).comp p
    (contDiffAt_const.prodMk contDiffAt_id)
  simpa only [fderiv_apply_one_eq_deriv, Function.comp_def, Prod.fst, Prod.snd]
    using he.contDiffWithinAt

theorem n07a_scalarResidualField_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) : Function.Periodic (scalarResidualField D S C z) (0, Real.pi) := by
  have hbase : Function.Periodic
      (Radial.radialHeightField (stateRadialHeight D S C z.1)) (0, Real.pi) := by
    intro p
    simp only [Radial.radialHeightField, Prod.fst_add, add_zero]
  have hU : Function.Periodic (stateU S z.1) (0, Real.pi) := by
    intro p
    simp only [stateU, heightPairField, Prod.fst_add, add_zero,
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.2.1 p]
  exact n07a_normalizedHeightResidual_periodic _ hbase hU z.2

theorem n07a_nuColumnField_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) : Function.Periodic (nuColumnField D S C z) (0, Real.pi) := by
  intro p
  unfold nuColumnField
  congr 1
  funext ν
  exact n07a_scalarResidualField_periodic hS ((z.1.1, (ν, z.1.2.2)), z.2) p

end ContinuousFlexibility.Analysis
