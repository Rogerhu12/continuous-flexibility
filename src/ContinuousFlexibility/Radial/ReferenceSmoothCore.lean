module

public import ContinuousFlexibility.Radial.ReferenceGraphNorms
public import ContinuousFlexibility.Radial.ReferenceCommonInverse

/-!
# Transport of source-core density through the actual inverse

This is the functional-analytic assembly step.  A concrete dense class of
sources and smooth solutions on that class give the frozen smooth graph
core.  The density and the smooth inverse images are separate analytic
inputs to this lemma, to be proved for the finite cosine source class.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem referenceRepresentative_sub {D : ReferenceData}
    {U V U' V' : RadialUnknown} (hU : RadialRepresentativeEq D U U')
    (hV : RadialRepresentativeEq D V V') :
    RadialRepresentativeEq D (U - V) (U' - V') := by
  constructor
  · change U.2 - V.2 = U'.2 - V'.2
    rw [hU.1, hV.1]
  · filter_upwards [hU.2, hV.2] with x hx hy
    change U.1 x - V.1 x = U'.1 x - V'.1 x
    rw [hx, hy]

theorem referenceSmoothCoreClosure_of_dense_inverse_core {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M₀ M₁ : ℝ}
    {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (CoreSource : RadialSource → Prop)
    (hdense : ∀ F, SourceMember D γ M₀ F →
      ∃ Fₙ : ℕ → RadialSource,
        (∀ n, SourceMember D γ M₀ (Fₙ n) ∧ CoreSource (Fₙ n)) ∧
        Tendsto (fun n => sourceNormSquare D γ M₀ (Fₙ n - F)) atTop (𝓝 0))
    (hsmooth : ∀ F, SourceMember D γ M₀ F → CoreSource F →
      ∃ U, ReferenceGraph D γ M₀ M₁ U F ∧ SmoothAdmissibleField D U) :
    ReferenceSmoothCoreClosure D γ M₀ M₁ := by
  intro U F hUF
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  obtain ⟨Fₙ, hFₙ, hFconv⟩ := hdense F hUF.2.1
  choose Uₙ hgraph hsmoothField using
    (fun n => hsmooth (Fₙ n) (hFₙ n).1 (hFₙ n).2)
  have hsame : RadialRepresentativeEq D (G F) U := hG.2.1 U F hUF
  have hsamen (n : ℕ) : RadialRepresentativeEq D (G (Fₙ n)) (Uₙ n) :=
    hG.2.1 (Uₙ n) (Fₙ n) (hgraph n)
  have hdiffSource (n : ℕ) : SourceMember D γ M₀ (Fₙ n - F) :=
    referenceSource_sub hD (hFₙ n).1 hUF.2.1
  have hdiff (n : ℕ) :
      RadialRepresentativeEq D (G (Fₙ n - F)) (Uₙ n - U) := by
    have hlin : RadialRepresentativeEq D (G (Fₙ n - F))
        (G (Fₙ n) - G F) := by
      simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
        hG.2.2.1 (Fₙ n) F (hFₙ n).1 hUF.2.1 1 (-1)
    exact hlin.trans (referenceRepresentative_sub (hsamen n) hsame)
  obtain ⟨C, _, hbound⟩ := hG.2.2.2
  choose aₙ haₙ hnorm using
    (fun n => hbound (Fₙ n - F) (hdiffSource n))
  have hout (n : ℕ) : OutputRealization D γ M₁ (aₙ n) (Uₙ n - U) := by
    apply (haₙ n).congr_ae hab (hdiff n)
    · intro x
      change (Uₙ n).1 (x + (0, Real.pi)) - U.1 (x + (0, Real.pi)) =
        (Uₙ n).1 x - U.1 x
      rw [(hgraph n).1.choose_spec.2.2.1 x, hUF.1.choose_spec.2.2.1 x]
    · intro r θ
      change (Uₙ n).1 (r, -θ) - U.1 (r, -θ) =
        (Uₙ n).1 (r, θ) - U.1 (r, θ)
      rw [(hgraph n).1.choose_spec.2.2.2 r θ, hUF.1.choose_spec.2.2.2 r θ]
  have hnorm' (n : ℕ) :
      outputNormSquare D γ M₁ (aₙ n) (Uₙ n - U) ≤
        C ^ 2 * sourceNormSquare D γ M₀ (Fₙ n - F) := by
    rw [← outputNormSquare_congr_ae hab (haₙ n) (hdiff n)]
    exact hnorm n
  refine ⟨Uₙ, Fₙ, aₙ, fun n => ⟨hgraph n, hsmoothField n, hout n⟩, hFconv, ?_⟩
  apply squeeze_zero (fun n => outputNormSquare_nonneg hab (hout n)) hnorm'
  simpa only [mul_zero] using hFconv.const_mul (C ^ 2)

end ContinuousFlexibility.Radial
