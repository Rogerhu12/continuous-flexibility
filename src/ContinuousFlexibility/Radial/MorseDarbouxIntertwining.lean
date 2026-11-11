import ContinuousFlexibility.Radial.MorseDarbouxForms

/-!
# Darboux transfer of actual Morse graph eigenvectors

The differential intertwining identities hold on smooth compact tests.
The true first-order adjoint pairings move those identities onto `L²`
eigenvectors of the associated graphs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory
open scoped ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem contDiff_morseExpression {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (α w b : ℝ) :
    ContDiff ℝ ∞ (morseExpression α w b φ) :=
  ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2.neg).add
    ((morsePartnerPotential_contDiff α w b).mul hφ)

theorem hasCompactSupport_morseExpression {φ : ℝ → ℝ} (hc : HasCompactSupport φ) (α w b : ℝ) :
    HasCompactSupport (morseExpression α w b φ) :=
  hc.deriv.deriv.neg.add (hc.mul_left (f := morsePartnerPotential α w b))

private theorem morseDeriv_add_const_mul {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (c x : ℝ) :
    deriv (fun y => f y + c * g y) x = deriv f x + c * deriv g x :=
  (((hf x).hasDerivAt).add (((hg x).hasDerivAt).const_mul c)).deriv

private theorem morseAnnihilation_add_const_mul {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α w c x : ℝ) :
    morseAnnihilation α w (fun y => f y + c * g y) x =
      morseAnnihilation α w f x + c * morseAnnihilation α w g x := by
  unfold morseAnnihilation
  rw [morseDeriv_add_const_mul hf hg]
  ring

private theorem morseCreation_add_const_mul {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (α w c x : ℝ) :
    morseCreation α w (fun y => f y + c * g y) x =
      morseCreation α w f x + c * morseCreation α w g x := by
  unfold morseCreation
  rw [morseDeriv_add_const_mul hf hg]
  ring

theorem morseAnnihilation_intertwines {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (α w b : ℝ) :
    morseAnnihilation α w (morseExpression α w b φ) =
      morseExpression (α - 1) w b (morseAnnihilation α w φ) := by
  have hD := contDiff_morseAnnihilation hφ α w
  have hCD := contDiff_morseCreation hD α w
  have hF : morseExpression α w b φ =
      fun x => morseCreation α w (morseAnnihilation α w φ) x + (b - α ^ 2) * φ x :=
    funext (morseExpression_factor (hφ.of_le (by simp)) α w b)
  funext x
  calc
    _ = morseAnnihilation α w
        (fun y => morseCreation α w (morseAnnihilation α w φ) y + (b - α ^ 2) * φ y) x := by rw [hF]
    _ = morseAnnihilation α w (morseCreation α w (morseAnnihilation α w φ)) x +
        (b - α ^ 2) * morseAnnihilation α w φ x :=
      morseAnnihilation_add_const_mul (hCD.differentiable (by simp)) (hφ.differentiable (by simp)) α w _ x
    _ = _ := (morseExpression_partner_factor (hD.of_le (by simp)) α w b x).symm

theorem morseCreation_intertwines {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (α w b : ℝ) :
    morseCreation α w (morseExpression (α - 1) w b φ) =
      morseExpression α w b (morseCreation α w φ) := by
  have hC := contDiff_morseCreation hφ α w
  have hDC := contDiff_morseAnnihilation hC α w
  have hF : morseExpression (α - 1) w b φ =
      fun x => morseAnnihilation α w (morseCreation α w φ) x + (b - α ^ 2) * φ x :=
    funext (morseExpression_partner_factor (hφ.of_le (by simp)) α w b)
  funext x
  calc
    _ = morseCreation α w
        (fun y => morseAnnihilation α w (morseCreation α w φ) y + (b - α ^ 2) * φ y) x := by rw [hF]
    _ = morseCreation α w (morseAnnihilation α w (morseCreation α w φ)) x +
        (b - α ^ 2) * morseCreation α w φ x :=
      morseCreation_add_const_mul (hDC.differentiable (by simp)) (hφ.differentiable (by simp)) α w _ x
    _ = _ := (morseExpression_factor (hC.of_le (by simp)) α w b x).symm

private theorem morseIntegral_smul_test (c : ℝ) (u : MorseL2) {φ : ℝ → ℝ} (hφ : MemLp φ 2 volume) :
    (∫ x : ℝ, (c • u) x * φ x) = c * ∫ x : ℝ, u x * φ x := by
  rw [← morseTestPairing_apply φ hφ (c • u), map_smul, smul_eq_mul, morseTestPairing_apply]

private theorem morseAnnihilationL2_compact_integral (α w : ℝ) (U : MorseWeakEnergy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x : ℝ, morseAnnihilationL2 α w U x * φ x) =
      ∫ x : ℝ, morseEnergyBase U x * morseCreation α w φ x := by
  rw [← morseL2_inner_right_toLp _ (compactSmooth_morseEnergyDomain hφ hc).2.1]
  exact morseAnnihilationL2_compact_adjoint α w U hφ hc

private theorem morseCreationL2_compact_integral (α w : ℝ) (U : MorseWeakEnergy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x : ℝ, morseCreationL2 α w U x * φ x) =
      ∫ x : ℝ, morseEnergyBase U x * morseAnnihilation α w φ x := by
  rw [← morseL2_inner_right_toLp _ (compactSmooth_morseEnergyDomain hφ hc).2.1]
  exact morseCreationL2_compact_adjoint α w U hφ hc

/-- The true annihilation image of a graph eigenvector satisfies the partner
graph equation at the same energy. -/
theorem morseAnnihilationL2_mem_partnerGraph {α w b E : ℝ} (hw : 0 < w) (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph α w b) :
    (morseAnnihilationL2 α w U, E • morseAnnihilationL2 α w U) ∈ morseAssociatedGraph (α - 1) w b := by
  apply (morsePartner_compactWeak_iff_associated (α - 1) b hw _ _).mp
  intro φ hφ hc
  let T := morseCreation α w φ
  let H := morseExpression (α - 1) w b φ
  have hT : ContDiff ℝ ∞ T := contDiff_morseCreation hφ α w
  have hcT : HasCompactSupport T := hasCompactSupport_morseCreation hc α w
  have hH : ContDiff ℝ ∞ H := contDiff_morseExpression hφ (α - 1) w b
  have hcH : HasCompactSupport H := hasCompactSupport_morseExpression hc (α - 1) w b
  have h := morseAssociatedGraph_compact_weak α w b _ _ hU
  calc
    _ = E * ∫ x : ℝ, morseAnnihilationL2 α w U x * φ x :=
      morseIntegral_smul_test E _ (compactSmooth_morseEnergyDomain hφ hc).2.1
    _ = E * ∫ x : ℝ, morseEnergyBase U x * T x :=
      congrArg (E * ·) (morseAnnihilationL2_compact_integral α w U hφ hc)
    _ = ∫ x : ℝ, (E • morseEnergyBase U) x * T x :=
      (morseIntegral_smul_test E _ (compactSmooth_morseEnergyDomain hT hcT).2.1).symm
    _ = ∫ x : ℝ, morseEnergyBase U x * morseExpression α w b T x := h T hT hcT
    _ = ∫ x : ℝ, morseEnergyBase U x * morseCreation α w H x := by
      simp only [T, H, morseCreation_intertwines hφ α w b]
    _ = _ := (morseAnnihilationL2_compact_integral α w U hH hcH).symm

/-- The true creation image of a partner graph eigenvector satisfies the
original graph equation at the same energy. -/
theorem morseCreationL2_mem_graph {α w b E : ℝ} (hw : 0 < w) (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph (α - 1) w b) :
    (morseCreationL2 α w U, E • morseCreationL2 α w U) ∈ morseAssociatedGraph α w b := by
  apply (morsePartner_compactWeak_iff_associated α b hw _ _).mp
  intro φ hφ hc
  let T := morseAnnihilation α w φ
  let H := morseExpression α w b φ
  have hT : ContDiff ℝ ∞ T := contDiff_morseAnnihilation hφ α w
  have hcT : HasCompactSupport T := hasCompactSupport_morseAnnihilation hc α w
  have hH : ContDiff ℝ ∞ H := contDiff_morseExpression hφ α w b
  have hcH : HasCompactSupport H := hasCompactSupport_morseExpression hc α w b
  have h := morseAssociatedGraph_compact_weak (α - 1) w b _ _ hU
  calc
    _ = E * ∫ x : ℝ, morseCreationL2 α w U x * φ x :=
      morseIntegral_smul_test E _ (compactSmooth_morseEnergyDomain hφ hc).2.1
    _ = E * ∫ x : ℝ, morseEnergyBase U x * T x :=
      congrArg (E * ·) (morseCreationL2_compact_integral α w U hφ hc)
    _ = ∫ x : ℝ, (E • morseEnergyBase U) x * T x :=
      (morseIntegral_smul_test E _ (compactSmooth_morseEnergyDomain hT hcT).2.1).symm
    _ = ∫ x : ℝ, morseEnergyBase U x * morseExpression (α - 1) w b T x := h T hT hcT
    _ = ∫ x : ℝ, morseEnergyBase U x * morseAnnihilation α w H x := by
      simp only [T, H, morseAnnihilation_intertwines hφ α w b]
    _ = _ := (morseCreationL2_compact_integral α w U hH hcH).symm

theorem morseEigenForm_pairing {α w b E : ℝ} (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph α w b)
    (W : MorseWeakEnergy) :
    morsePhysicalForm α w b U W = E * ⟪morseEnergyBase U, morseEnergyBase W⟫_ℝ := by
  obtain ⟨Z, hZ, hpair⟩ := hU
  have he : Z = U := morseEnergyBase_injective hZ
  subst Z
  rw [hpair W, real_inner_smul_left]

theorem morseAnnihilationL2_eigen_norm_sq {α w b E : ℝ} (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph α w b) :
    ‖morseAnnihilationL2 α w U‖ ^ 2 = (E - b + α ^ 2) * ‖morseEnergyBase U‖ ^ 2 := by
  have h := morseEigenForm_pairing U hU U
  simp only [morsePhysicalForm_factorization, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

theorem morseCreationL2_eigen_norm_sq {α w b E : ℝ} (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph (α - 1) w b) :
    ‖morseCreationL2 α w U‖ ^ 2 = (E - b + α ^ 2) * ‖morseEnergyBase U‖ ^ 2 := by
  have h := morseEigenForm_pairing U hU U
  simp only [morsePartnerPhysicalForm_factorization, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

private theorem morseFactor_ne_zero_iff {u v : MorseL2} {c : ℝ}
    (hu : u ≠ 0) (h : ‖v‖ ^ 2 = c * ‖u‖ ^ 2) : v ≠ 0 ↔ 0 < c := by
  have hu₂ := sq_pos_of_pos (norm_pos_iff.mpr hu)
  constructor
  · intro hv
    have hv₂ := sq_pos_of_pos (norm_pos_iff.mpr hv)
    rw [h] at hv₂
    exact (mul_pos_iff_of_pos_right hu₂).mp hv₂
  · intro hc hv
    have hv₂ : 0 < ‖v‖ ^ 2 := h.symm ▸ mul_pos hc hu₂
    simp only [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hv₂

theorem morseAnnihilationL2_eigen_ne_zero_iff {α w b E : ℝ} (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph α w b)
    (hu : morseEnergyBase U ≠ 0) : morseAnnihilationL2 α w U ≠ 0 ↔ b - α ^ 2 < E := by
  rw [morseFactor_ne_zero_iff hu (morseAnnihilationL2_eigen_norm_sq U hU)]
  constructor <;> intro h <;> linarith

theorem morseCreationL2_eigen_ne_zero_iff {α w b E : ℝ} (U : MorseWeakEnergy)
    (hU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph (α - 1) w b)
    (hu : morseEnergyBase U ≠ 0) : morseCreationL2 α w U ≠ 0 ↔ b - α ^ 2 < E := by
  rw [morseFactor_ne_zero_iff hu (morseCreationL2_eigen_norm_sq U hU)]
  constructor <;> intro h <;> linarith

end ContinuousFlexibility.Radial
