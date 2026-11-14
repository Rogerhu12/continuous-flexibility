module

public import ContinuousFlexibility.Analysis.SmoothPeriodicScalarFlow
public import ContinuousFlexibility.Analysis.ScalarFlowSmooth
public import ContinuousFlexibility.Analysis.ScalarFlowInitialAngle

/-!
# Smooth periodic flow families constructed from the field

Actual Picard trajectories first acquire joint continuity from compact
parameter neighborhoods. The parameter variational theorem and finite
order bootstrap then give their smooth endpoint map. The same actual
time equation gives its strictly positive initial-angle Jacobian.
Neither flow continuity nor a parameter derivative is an input here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

/-- A smooth periodic field produces actual flow lifts with a jointly
smooth endpoint map and a strictly positive angular Jacobian. -/
theorem exists_smooth_periodicScalarFlowFamily
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {F : ℝ × (P × ℝ) → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hT : T ≠ 0) (hF : ContDiff ℝ ∞ F)
    (hperiod : ∀ t ∈ Icc a b, ∀ p : P,
      Function.Periodic (fun θ => F (t, (p, θ))) T) :
    ∃ Θ : P → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p a θ = θ) ∧
      (∀ p θ t, t ∈ Icc a b →
        HasDerivWithinAt (fun r => Θ p r θ)
          (F (t, (p, Θ p t θ))) (Icc a b) t) ∧
      (∀ p θ t, t ∈ Icc a b → Θ p t (θ + T) = Θ p t θ + T) ∧
      ContinuousOn (fun z : (P × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
        (univ ×ˢ Icc a b) ∧
      ContDiff ℝ ∞ (fun z : P × ℝ => Θ z.1 b z.2) ∧
      (∀ p θ, 0 < deriv (fun φ => Θ p b φ) θ) := by
  obtain ⟨Θ, hinit, hflow, hper, hcont⟩ :=
    exists_continuous_periodicScalarFlowFamily hab hT hF hperiod
  have hcontU : ContinuousOn
      (fun z : (P × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2) (univ ×ˢ uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hcont
  have hflowU (p : P) (θ t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivWithinAt (fun r => Θ p r θ)
        (F (t, (p, Θ p t θ))) (uIcc a b) t := by
    have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    simpa only [uIcc_of_le hab] using hflow p θ t ht'
  have hfield : ContDiff ℝ ∞
      (fun z : (P × ℝ) × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2))) :=
    hF.comp (contDiff_snd.fst.prodMk (contDiff_fst.fst.prodMk contDiff_snd.snd))
  have hendpoint : ContDiff ℝ ∞ (fun z : P × ℝ => Θ z.1 b z.2) :=
    contDiff_scalarFlow_endpoint
      (F := fun z : (P × ℝ) × (ℝ × ℝ) => F (z.2.1, (z.1.1, z.2.2)))
      (Θ := fun z : (P × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
      (v := fun z : P × ℝ => z.2)
      hfield contDiff_snd hcontU
      (fun z => hinit z.1 z.2) (fun z t ht => hflowU z.1 z.2 t ht)
  refine ⟨Θ, hinit, hflow, hper, hcont, hendpoint, ?_⟩
  intro p θ
  let D : ℝ × ℝ → ℝ := fun z =>
    (fderiv ℝ F (z.1, (p, z.2))) (0, (0, 1))
  have hDF : Continuous (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).continuous
  have hD : Continuous D :=
    (hDF.comp (continuous_fst.prodMk
      (continuous_const.prodMk continuous_snd))).clm_apply continuous_const
  have hangle (t x : ℝ) :
      HasDerivAt (fun y => F (t, (p, y))) (D (t, x)) x := by
    have hcurve : HasDerivAt (fun y : ℝ => (t, (p, y))) (0, (0, 1)) x := by
      simpa only [id_eq] using
        HasDerivAt.prodMk (hasDerivAt_const (x := x) (c := t))
          (HasDerivAt.prodMk (hasDerivAt_const (x := x) (c := p)) (hasDerivAt_id x))
    have hd := (hF.differentiable (by simp) (t, (p, x))).hasFDerivAt.comp_hasDerivAt x hcurve
    have he : F ∘ (fun y : ℝ => (t, (p, y))) = (fun y => F (t, (p, y))) := by
      funext y
      exact Function.comp_apply
    rw [he] at hd
    exact hd
  have hslice : ContinuousOn (fun z : ℝ × ℝ => Θ p z.2 z.1)
      ((univ : Set ℝ) ×ˢ uIcc a b) :=
    hcontU.comp ((continuousOn_const.prodMk continuousOn_fst).prodMk continuousOn_snd)
      (fun z hz => ⟨mem_univ _, hz.2⟩)
  exact scalarFlow_initialAngle_deriv_pos
    (F := fun z : ℝ × ℝ => F (z.1, (p, z.2))) (D := D)
    (Θ := fun z : ℝ × ℝ => Θ p z.2 z.1) (a := a) (b := b)
    hD hangle hslice (hinit p) (hflowU p) θ

end ContinuousFlexibility.Analysis
