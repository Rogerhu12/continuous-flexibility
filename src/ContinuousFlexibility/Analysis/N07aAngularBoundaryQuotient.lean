import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The height jump cancels in the actual transport ratio

At a middle cut the reference and current height derivatives have the
same logarithmic jump after the actual coordinate first jets are aligned.
Consequently the quotient used to transport a physical field has one
common first derivative. The zero jump is the same argument at a root.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

theorem n07a_hasFDerivAt_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : E → ℝ} {a' b' : E →L[ℝ] ℝ} {p : E}
    (ha : HasFDerivAt a a' p) (hb : HasFDerivAt b b' p) (hne : b p ≠ 0) :
    HasFDerivAt (fun q => a q / b q)
      ((b p)⁻¹ • a' - (a p / (b p) ^ 2) • b') p := by
  have h := ha.fun_mul ((hasDerivAt_inv hne).comp_hasFDerivAt p hb)
  have h' : HasFDerivAt (fun q => a q / b q)
      (a p • (-(b p ^ 2)⁻¹ • b') + (b p)⁻¹ • a') p := by
    simpa only [Function.comp_def, div_eq_mul_inv] using h
  apply h'.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sub_apply,
    smul_apply, smul_eq_mul]
  ring

/-- Equal values and equal logarithmic jumps give equal quotient one-jets. -/
theorem n07a_quotient_firstJet_match {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a₀ a₁ b₀ b₁ : E → ℝ} {p : E}
    (ha₀ : DifferentiableAt ℝ a₀ p) (ha₁ : DifferentiableAt ℝ a₁ p)
    (hb₀ : DifferentiableAt ℝ b₀ p) (hb₁ : DifferentiableAt ℝ b₁ p)
    (ha : a₁ p = a₀ p) (hb : b₁ p = b₀ p) (hne : b₀ p ≠ 0)
    (κ : ℝ) (ell : E →L[ℝ] ℝ)
    (hda : fderiv ℝ a₁ p - fderiv ℝ a₀ p = (κ * a₀ p) • ell)
    (hdb : fderiv ℝ b₁ p - fderiv ℝ b₀ p = (κ * b₀ p) • ell) :
    a₁ p / b₁ p = a₀ p / b₀ p ∧
      fderiv ℝ (fun q => a₁ q / b₁ q) p =
        fderiv ℝ (fun q => a₀ q / b₀ q) p := by
  refine ⟨by rw [ha, hb], ?_⟩
  rw [(n07a_hasFDerivAt_quotient ha₁.hasFDerivAt hb₁.hasFDerivAt
      (hb.trans_ne hne)).fderiv,
    (n07a_hasFDerivAt_quotient ha₀.hasFDerivAt hb₀.hasFDerivAt hne).fderiv,
    ha, hb]
  apply ContinuousLinearMap.ext
  intro v
  have hda' := congrArg (fun A : E →L[ℝ] ℝ => A v) hda
  have hdb' := congrArg (fun A : E →L[ℝ] ℝ => A v) hdb
  simp only [sub_apply, smul_apply,
    smul_eq_mul] at hda' hdb' ⊢
  have ha' : fderiv ℝ a₁ p v = fderiv ℝ a₀ p v + κ * a₀ p * ell v := by
    linarith only [hda']
  have hb' : fderiv ℝ b₁ p v = fderiv ℝ b₀ p v + κ * b₀ p * ell v := by
    linarith only [hdb']
  rw [ha', hb']
  field_simp [hne]
  ring

/-- Pulling the current height jet back by the actual transport sends its
logarithmic jump to the same normal covector as the reference height. -/
theorem n07a_logarithmicJump_comp
    {f₀ f₁ : PolarPoint → ℝ} {T₀ T₁ : PolarPoint → PolarPoint}
    {p q : PolarPoint} {A : PolarPoint →L[ℝ] PolarPoint}
    (hf₀ : DifferentiableAt ℝ f₀ q) (hf₁ : DifferentiableAt ℝ f₁ q)
    (hT₀ : HasFDerivAt T₀ A p) (hT₁ : HasFDerivAt T₁ A p)
    (hvalue₀ : T₀ p = q) (hvalue₁ : T₁ p = q)
    {κ : ℝ} {ell ell₀ : PolarPoint →L[ℝ] ℝ}
    (hjump : fderiv ℝ f₁ q - fderiv ℝ f₀ q = (κ * f₀ q) • ell)
    (halign : ell.comp A = ell₀) :
    fderiv ℝ (f₁ ∘ T₁) p - fderiv ℝ (f₀ ∘ T₀) p =
      (κ * f₀ q) • ell₀ := by
  have hdf₀ : HasFDerivAt f₀ (fderiv ℝ f₀ q) (T₀ p) :=
    hvalue₀.symm ▸ hf₀.hasFDerivAt
  have hdf₁ : HasFDerivAt f₁ (fderiv ℝ f₁ q) (T₁ p) :=
    hvalue₁.symm ▸ hf₁.hasFDerivAt
  have hd₀ := hdf₀.comp p hT₀
  have hd₁ := hdf₁.comp p hT₁
  rw [hd₁.fderiv, hd₀.fderiv, ← halign]
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun B : PolarPoint →L[ℝ] ℝ => B (A v)) hjump
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply] using h

/-- Once the coordinate one-jets agree, both logarithmic height jumps
cancel in the actual transported scalar field. -/
theorem n07a_heightTransport_firstJet_match
    {a₀ a₁ b₀ b₁ f χ : PolarPoint → ℝ} {T₀ T₁ : PolarPoint → PolarPoint}
    {p q : PolarPoint} {A : PolarPoint →L[ℝ] PolarPoint}
    (ha₀ : DifferentiableAt ℝ a₀ p) (ha₁ : DifferentiableAt ℝ a₁ p)
    (hb₀ : DifferentiableAt ℝ b₀ q) (hb₁ : DifferentiableAt ℝ b₁ q)
    (hf : DifferentiableAt ℝ f q) (hχ : DifferentiableAt ℝ χ p)
    (hT₀ : HasFDerivAt T₀ A p) (hT₁ : HasFDerivAt T₁ A p)
    (hvalue₀ : T₀ p = q) (hvalue₁ : T₁ p = q)
    (ha : a₁ p = a₀ p) (hb : b₁ q = b₀ q) (hne : b₀ q ≠ 0)
    {κ : ℝ} {ell ell₀ : PolarPoint →L[ℝ] ℝ}
    (hda : fderiv ℝ a₁ p - fderiv ℝ a₀ p = (κ * a₀ p) • ell₀)
    (hdb : fderiv ℝ b₁ q - fderiv ℝ b₀ q = (κ * b₀ q) • ell)
    (halign : ell.comp A = ell₀) :
    (a₁ p / b₁ (T₁ p)) * f (T₁ p) + χ p =
      (a₀ p / b₀ (T₀ p)) * f (T₀ p) + χ p ∧
    fderiv ℝ (fun x => (a₁ x / b₁ (T₁ x)) * f (T₁ x) + χ x) p =
      fderiv ℝ (fun x => (a₀ x / b₀ (T₀ x)) * f (T₀ x) + χ x) p := by
  have hbT₀ : DifferentiableAt ℝ (b₀ ∘ T₀) p := by
    apply DifferentiableAt.comp p _ hT₀.differentiableAt
    simpa only [hvalue₀] using hb₀
  have hbT₁ : DifferentiableAt ℝ (b₁ ∘ T₁) p := by
    apply DifferentiableAt.comp p _ hT₁.differentiableAt
    simpa only [hvalue₁] using hb₁
  have hbT : (b₁ ∘ T₁) p = (b₀ ∘ T₀) p := by
    simpa only [Function.comp_apply, hvalue₀, hvalue₁] using hb
  have hbTne : (b₀ ∘ T₀) p ≠ 0 := by
    simpa only [Function.comp_apply, hvalue₀] using hne
  have hdbT := n07a_logarithmicJump_comp hb₀ hb₁ hT₀ hT₁ hvalue₀ hvalue₁ hdb halign
  have hquot := n07a_quotient_firstJet_match ha₀ ha₁ hbT₀ hbT₁ ha hbT hbTne κ ell₀ hda
    (by simpa only [Function.comp_apply, hvalue₀] using hdbT)
  simp only [Function.comp_apply] at hquot
  have hρ₀ : DifferentiableAt ℝ (fun x => a₀ x / b₀ (T₀ x)) p :=
    (n07a_hasFDerivAt_quotient ha₀.hasFDerivAt hbT₀.hasFDerivAt hbTne).differentiableAt
  have hρ₁ : DifferentiableAt ℝ (fun x => a₁ x / b₁ (T₁ x)) p :=
    (n07a_hasFDerivAt_quotient ha₁.hasFDerivAt hbT₁.hasFDerivAt
      (hbT.trans_ne hbTne)).differentiableAt
  have hdf₀ : HasFDerivAt f (fderiv ℝ f q) (T₀ p) := hvalue₀.symm ▸ hf.hasFDerivAt
  have hdf₁ : HasFDerivAt f (fderiv ℝ f q) (T₁ p) := hvalue₁.symm ▸ hf.hasFDerivAt
  have hd₀ := (hρ₀.hasFDerivAt.fun_mul (hdf₀.comp p hT₀)).fun_add hχ.hasFDerivAt
  have hd₁ := (hρ₁.hasFDerivAt.fun_mul (hdf₁.comp p hT₁)).fun_add hχ.hasFDerivAt
  simp only [Function.comp_apply] at hd₀ hd₁
  refine ⟨by rw [hquot.1, hvalue₀, hvalue₁], ?_⟩
  rw [hd₁.fderiv, hd₀.fderiv, hquot.1, hquot.2, hvalue₀, hvalue₁]

end ContinuousFlexibility.Analysis
