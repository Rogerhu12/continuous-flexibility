module

public import ContinuousFlexibility.Radial.InnerLiouvilleEnergyDomain
public import ContinuousFlexibility.Radial.InnerLiouvilleBorderTransport
public import ContinuousFlexibility.Radial.InnerBufferLocalizedConstruction
public import ContinuousFlexibility.Radial.InnerWeakGreen

/-!
# The actual model inverse has the physical domain and scalar row

The source is the adjoint of the same field lift used for the output.
Its support is proved from its actual representative, so the original
localized Dirichlet inverse applies to every physical L² source.
Its original energy witness then maps into the actual radial
zero-endpoint closure, and the inverse-adjoint border preserves the
single scalar row exactly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

section General

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleSource_support (F : RadialModeL2 D) :
    (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv F : ℝ → ℝ) =ᵐ[
      volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) := by
  filter_upwards [ae_restrict_of_ae
    (innerLiouvilleSource_ae D hab hlam hR hs hp hcore hw U hU hv F),
    ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
  rw [hx, indicator_of_notMem hout]

omit hab in
theorem innerLiouvilleBorderedGraph_realization (hab : a < b) (hDw : Continuous D.w)
    {V : ℝ → ℝ} {g : RadialL2} {bordered : Bool}
    {Z : RadialL2 × ℝ} {F : RadialModeL2 D × ℝ}
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0))
    (hG : BorderedIntervalGraph V g bordered a b Z
      (innerLiouvilleSource D hab.le hlam hR hs hp hcore hw U hU hv F.1, F.2)) :
    ∃ d q : RadialL2,
      (Z.1, d, q) ∈ closure (IntervalEnergyCore V a b) ∧
      (∀ t ∈ closure (IntervalEnergyCore V a b),
        ⟪innerLiouvilleSource D hab.le hlam hR hs hp hcore hw U hU hv F.1 - Z.2 • g,
          t.1⟫_ℝ = ⟪d, t.2.1⟫_ℝ + ∫ x : ℝ, V x * Z.1 x * t.1 x) ∧
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv Z.1,
        innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (Z.1, d)) ∈
          innerRadialH1Zero D (R a) (R b) ∧
      (if bordered then
        ⟪innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g,
          innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv Z.1⟫_ℝ = F.2
       else Z.2 = 0 ∧ F.2 = 0) := by
  obtain ⟨d, q, hclosure, hform⟩ := innerBorderedIntervalGraph_effectiveForm hG
  refine ⟨d, q, hclosure, hform, ?_, ?_⟩
  · have hd := innerLiouvilleEnergyLift_closure D hlam hR hs hp hcore hw
      hab hDw U hU hv V (Z.1, d, q) hclosure
    simpa only [innerLiouvilleEnergyLift_apply] using hd
  · cases bordered with
    | false =>
      simp only [BorderedIntervalGraph, Bool.false_eq_true, ite_false] at hG ⊢
      exact hG.2
    | true =>
      simp only [BorderedIntervalGraph, ite_true] at hG ⊢
      rw [innerLiouvilleColumnLift_field_pairing D hab.le hlam hR hs hp hcore hw
        U hU hv g Z.1 hg]
      exact hG.2

end General

section Localized

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
  (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)

/-- The same localized model inverse solves its original graph for the
actual physical adjoint source. No support assumption on that source is added. -/
theorem innerLiouvilleLocalizedDirichlet_graph (F : RadialModeL2 D × ℝ)
    (hscalar : B.bordered = false → F.2 = 0) :
    BorderedIntervalGraph B.potential B.border B.bordered B.l B.h
      (M.dirichlet
        (innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1, F.2))
      (innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1, F.2) :=
  M.dirichlet_solves _ hscalar
    (innerLiouvilleSource_support D hB.1.le hlam hR hs hp hcore hw U hU hv F.1)

/-- The physical output of the already constructed CLM has an actual
radial H1 witness and the original single scalar row. -/
theorem innerLiouvilleLocalizedDirichlet_realization (hDw : Continuous D.w)
    (F : RadialModeL2 D × ℝ) (hscalar : B.bordered = false → F.2 = 0) :
    let Z := M.dirichlet
      (innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1, F.2)
    let P := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hs hp hcore hw
      U hU hv M.dirichlet F
    ∃ d q : RadialL2,
      (Z.1, d, q) ∈ closure (IntervalEnergyCore B.potential B.l B.h) ∧
      (∀ t ∈ closure (IntervalEnergyCore B.potential B.l B.h),
        ⟪innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1 -
          Z.2 • B.border, t.1⟫_ℝ =
          ⟪d, t.2.1⟫_ℝ + ∫ x : ℝ, B.potential x * Z.1 x * t.1 x) ∧
      (P.1, innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw (Z.1, d)) ∈
        innerRadialH1Zero D (R B.l) (R B.h) ∧
      (if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, P.1⟫_ℝ = F.2
       else P.2 = 0 ∧ F.2 = 0) := by
  have hborder : (B.border : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0) := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    exact hb
  have hG := innerLiouvilleLocalizedDirichlet_graph D hB M hlam hR hs hp hcore hw U hU hv
    F hscalar
  have hreal := innerLiouvilleBorderedGraph_realization D hlam hR hs hp hcore hw U hU hv
    hB.1 hDw hborder hG
  dsimp only
  rw [innerLiouvillePhysicalDirichlet_apply]
  exact hreal

end Localized

end ContinuousFlexibility.Radial
