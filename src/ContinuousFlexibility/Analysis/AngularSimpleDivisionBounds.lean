import ContinuousFlexibility.Analysis.MixedSimpleDivisionBounds
import ContinuousFlexibility.Analysis.BoundaryMixedJets
import ContinuousFlexibility.Analysis.PointwiseCylinderJets

/-!
# Removing actual angular factors with fixed derivative loss

The ordinary radial jet of an angular factorization has the same angular
factor. Applying the existing one-dimensional Taylor division to that
jet gives mixed bounds, without a new differentiation-under-integral
argument. A translated zero costs one angular derivative; its square
costs two. The constants and the physical radial point are unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Translation of the angle preserves the actual mixed derivative. -/
theorem mixedDerivative_angularTranslate (F : PolarPoint → ℝ) (c : ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => F (q.1, q.2 + c)) p =
      mixedDerivative a b F (p.1, p.2 + c) := by
  simp only [mixedDerivative, iteratedDeriv_comp_add_const]

/-- A genuine simple angular factor loses exactly one angular derivative.
Both signs of the angle are covered by the same segment hypothesis. -/
theorem abs_mixedDerivative_smoothAngularFactor_le
    {F G : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hfactor : ∀ q : PolarPoint, F q = q.2 * G q)
    (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative a (b + 1) F (p.1, t * p.2)| ≤ M) :
    |mixedDerivative a b G p| ≤ M := by
  let f : ℝ → ℝ := radialBoundaryJet F p.1 a
  let g : ℝ → ℝ := radialBoundaryJet G p.1 a
  have hf : ContDiff ℝ ∞ f :=
    contDiff_radialBoundaryJet_of_contDiffAt p.1 (fun _ => hF.contDiffAt) a
  have hg : ContDiff ℝ ∞ g :=
    contDiff_radialBoundaryJet_of_contDiffAt p.1 (fun _ => hG.contDiffAt) a
  have hfg (θ : ℝ) : f θ = θ * g θ := by
    change iteratedDeriv a (fun r => F (r, θ)) p.1 =
      θ * iteratedDeriv a (fun r => G (r, θ)) p.1
    have he : (fun r => F (r, θ)) = (fun r => θ * G (r, θ)) :=
      funext fun r => hfactor (r, θ)
    rw [he, iteratedDeriv_const_mul_field]
  have hfjet (n : ℕ) (θ : ℝ) :
      iteratedDeriv n f θ = mixedDerivative a n F (p.1, θ) :=
    iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      isOpen_univ hF.contDiffOn p.1 (fun _ => mem_univ _) a n θ
  have hgjet : iteratedDeriv b g p.2 = mixedDerivative a b G p :=
    iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      isOpen_univ hG.contDiffOn p.1 (fun _ => mem_univ _) a b p.2
  have h := abs_mixedDerivative_smoothRadialFactor_le
    (F := fun q : PolarPoint => f q.1) (G := fun q : PolarPoint => g q.1)
    (hf.comp contDiff_fst) (hg.comp contDiff_fst)
    (fun q : PolarPoint => hfg q.1) b 0 (p := (p.2, 0))
    (M := M) (fun t ht => by
      have hb := hbound t ht
      rw [← hfjet (b + 1) (t * p.2)] at hb
      simpa only [mixedDerivative, iteratedDeriv_zero] using hb)
  have h' : |iteratedDeriv b g p.2| ≤ M := by
    simpa only [mixedDerivative, iteratedDeriv_zero] using h
  rwa [hgjet] at h'

/-- The zero may be any fixed angular value. The bound follows the
actual closed segment from that zero to the evaluation angle. -/
theorem abs_mixedDerivative_translatedAngularFactor_le
    {F G : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (c : ℝ) (hfactor : ∀ q : PolarPoint, F q = (q.2 - c) * G q)
    (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative a (b + 1) F (p.1, t * (p.2 - c) + c)| ≤ M) :
    |mixedDerivative a b G p| ≤ M := by
  have hs : ContDiff ℝ ∞ (fun q : PolarPoint => (q.1, q.2 + c)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have h := abs_mixedDerivative_smoothAngularFactor_le
    (F := fun q : PolarPoint => F (q.1, q.2 + c))
    (G := fun q : PolarPoint => G (q.1, q.2 + c))
    (hF.comp hs) (hG.comp hs)
    (fun q : PolarPoint => by
      simpa only [add_sub_cancel_right] using hfactor (q.1, q.2 + c))
    a b (p := (p.1, p.2 - c)) (M := M) (fun t ht => by
      rw [mixedDerivative_angularTranslate]
      exact hbound t ht)
  simpa only [mixedDerivative_angularTranslate, sub_add_cancel] using h

/-- A genuine squared angular factor has a loss of two, obtained by
applying the same simple-factor result twice. No new smooth quotient
or independently assumed numerator jets are used. -/
theorem abs_mixedDerivative_squaredAngularFactor_le
    {F G : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (c : ℝ) (hfactor : ∀ q : PolarPoint, F q = (q.2 - c) ^ 2 * G q)
    (a b : ℕ) {p : PolarPoint} {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |mixedDerivative a (b + 2) F (p.1, t * (p.2 - c) + c)| ≤ M) :
    |mixedDerivative a b G p| ≤ M := by
  let H : PolarPoint → ℝ := fun q => (q.2 - c) * G q
  have hH : ContDiff ℝ ∞ H := (contDiff_snd.sub contDiff_const).mul hG
  have hFH (q : PolarPoint) : F q = (q.2 - c) * H q := by
    rw [hfactor q]
    dsimp only [H]
    ring
  apply abs_mixedDerivative_translatedAngularFactor_le hH hG c (fun _ => rfl) a b
  intro t ht
  apply abs_mixedDerivative_translatedAngularFactor_le hF hH c hFH a (b + 1)
  intro s hs
  have hst : s * t ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg hs.1 ht.1, ?_⟩
    exact (mul_le_mul_of_nonneg_right hs.2 ht.1).trans (by simpa using ht.2)
  have he : s * (t * (p.2 - c) + c - c) + c =
      (s * t) * (p.2 - c) + c := by ring
  rw [he, show b + 1 + 1 = b + 2 by omega]
  exact hbound (s * t) hst

end ContinuousFlexibility.Analysis
