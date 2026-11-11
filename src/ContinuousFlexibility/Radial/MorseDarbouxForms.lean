import ContinuousFlexibility.Radial.MorsePartnerWeakGraph

/-!
# Darboux factorization on the Morse energy space

The first-order maps use the weak derivative and the exponential coordinate
of the closed energy graph. Compact test pairings identify them with the
classical Darboux expressions. Energy-core density extends both factorizations
to arbitrary energy vectors.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private def morseSignedFirstOrder (c α w : ℝ) : MorseWeakEnergy →L[ℝ] MorseL2 :=
  c • morseEnergyDerivative + α • morseEnergyBase - w • morseEnergyWeight

def morseAnnihilationL2 (α w : ℝ) : MorseWeakEnergy →L[ℝ] MorseL2 :=
  morseSignedFirstOrder 1 α w

def morseCreationL2 (α w : ℝ) : MorseWeakEnergy →L[ℝ] MorseL2 :=
  morseSignedFirstOrder (-1) α w

private theorem morseSignedFirstOrder_apply (c α w : ℝ) (U : MorseWeakEnergy) :
    morseSignedFirstOrder c α w U =
      c • morseEnergyDerivative U + α • morseEnergyBase U - w • morseEnergyWeight U := rfl

theorem morseAnnihilationL2_apply (α w : ℝ) (U : MorseWeakEnergy) :
    morseAnnihilationL2 α w U =
      morseEnergyDerivative U + α • morseEnergyBase U - w • morseEnergyWeight U := by
  rw [morseAnnihilationL2, morseSignedFirstOrder_apply, one_smul]

theorem morseCreationL2_apply (α w : ℝ) (U : MorseWeakEnergy) :
    morseCreationL2 α w U =
      -morseEnergyDerivative U + α • morseEnergyBase U - w • morseEnergyWeight U := by
  rw [morseCreationL2, morseSignedFirstOrder_apply, neg_one_smul]

theorem contDiff_morseCreation {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (α w : ℝ) :
    ContDiff ℝ ∞ (morseCreation α w φ) :=
  (contDiff_infty_iff_deriv.mp hφ).2.neg.add
    ((contDiff_const.sub (contDiff_const.mul contDiff_id.neg.exp)).mul hφ)

theorem hasCompactSupport_morseAnnihilation {φ : ℝ → ℝ} (hc : HasCompactSupport φ) (α w : ℝ) :
    HasCompactSupport (morseAnnihilation α w φ) :=
  hc.deriv.add (hc.mul_left (f := fun x => α - w * exp (-x)))

theorem hasCompactSupport_morseCreation {φ : ℝ → ℝ} (hc : HasCompactSupport φ) (α w : ℝ) :
    HasCompactSupport (morseCreation α w φ) :=
  hc.deriv.neg.add (hc.mul_left (f := fun x => α - w * exp (-x)))

private theorem morseSignedFirstOrder_ae {φ F : ℝ → ℝ} (c α w : ℝ)
    (hFormula : ∀ x, F x = c * deriv φ x + (α - w * exp (-x)) * φ x) :
    ((c • deriv φ + α • φ) - w • (fun x => exp (-x) * φ x)) =ᵐ[volume] F := by
  apply Eventually.of_forall
  intro x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hFormula]
  ring

private theorem morseSignedFirstOrder_memLp {φ F : ℝ → ℝ} (hφ : MorseEnergyDomain φ) (c α w : ℝ)
    (hFormula : ∀ x, F x = c * deriv φ x + (α - w * exp (-x)) * φ x) : MemLp F 2 volume :=
  (memLp_congr_ae (morseSignedFirstOrder_ae c α w hFormula)).mp
    (((hφ.2.2.1.const_smul c).add (hφ.2.1.const_smul α)).sub (hφ.2.2.2.const_smul w))

theorem morseAnnihilation_memLp_of_energy {φ : ℝ → ℝ} (hφ : MorseEnergyDomain φ) (α w : ℝ) :
    MemLp (morseAnnihilation α w φ) 2 volume :=
  morseSignedFirstOrder_memLp hφ 1 α w (fun x => by rw [morseAnnihilation, one_mul])

theorem morseCreation_memLp_of_energy {φ : ℝ → ℝ} (hφ : MorseEnergyDomain φ) (α w : ℝ) :
    MemLp (morseCreation α w φ) 2 volume :=
  morseSignedFirstOrder_memLp hφ (-1) α w (fun x => by rw [morseCreation, neg_one_mul])

private theorem morseSignedFirstOrder_lift {φ : ℝ → ℝ} (hφ : MorseEnergyDomain φ)
    (c α w : ℝ) {F : ℝ → ℝ} (hF : MemLp F 2 volume)
    (hFormula : ∀ x, F x = c * deriv φ x + (α - w * exp (-x)) * φ x) :
    morseSignedFirstOrder c α w (morseEnergyLift hφ) = hF.toLp F := by
  let d := hφ.2.2.1.const_smul c
  let a := hφ.2.1.const_smul α
  let z := hφ.2.2.2.const_smul w
  calc
    _ = d.toLp (c • deriv φ) + a.toLp (α • φ) - z.toLp (w • (fun x => exp (-x) * φ x)) := by
      rw [morseSignedFirstOrder_apply, morseEnergyLift_derivative, morseEnergyLift_base,
        morseEnergyLift_weight, MemLp.toLp_const_smul c hφ.2.2.1,
        MemLp.toLp_const_smul α hφ.2.1, MemLp.toLp_const_smul w hφ.2.2.2]
    _ = ((d.add a).sub z).toLp
        ((c • deriv φ + α • φ) - w • (fun x => exp (-x) * φ x)) := by
      rw [MemLp.toLp_sub (d.add a) z, MemLp.toLp_add d a]
    _ = _ := MemLp.toLp_congr _ _ (morseSignedFirstOrder_ae c α w hFormula)

theorem morseAnnihilationL2_lift {φ : ℝ → ℝ} (hφ : MorseEnergyDomain φ) (α w : ℝ)
    (hD : MemLp (morseAnnihilation α w φ) 2 volume) :
    morseAnnihilationL2 α w (morseEnergyLift hφ) = hD.toLp (morseAnnihilation α w φ) :=
  morseSignedFirstOrder_lift hφ 1 α w hD (fun x => by rw [morseAnnihilation, one_mul])

theorem morseCreationL2_lift {φ : ℝ → ℝ} (hφ : MorseEnergyDomain φ) (α w : ℝ)
    (hC : MemLp (morseCreation α w φ) 2 volume) :
    morseCreationL2 α w (morseEnergyLift hφ) = hC.toLp (morseCreation α w φ) :=
  morseSignedFirstOrder_lift hφ (-1) α w hC (fun x => by rw [morseCreation, neg_one_mul])

private theorem morseSignedFirstOrder_compact_adjoint (c α w : ℝ) (U : MorseWeakEnergy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let h := (compactSmooth_morseEnergyDomain hφ hc).2.1
    ⟪morseSignedFirstOrder c α w U, h.toLp φ⟫_ℝ =
      ∫ x : ℝ, morseEnergyBase U x * (-c * deriv φ x + (α - w * exp (-x)) * φ x) := by
  intro h
  let ht := compactSmooth_morseEnergyDomain hφ hc
  have hd := morseEnergyDerivative_weak U φ hφ hc
  have hw : (∫ x : ℝ, morseEnergyWeight U x * φ x) =
      ∫ x : ℝ, morseEnergyBase U x * (exp (-x) * φ x) := by
    apply integral_congr_ae
    filter_upwards [morseEnergyWeight_ae U] with x hx
    rw [hx]
    ring
  have hD : Integrable (fun x => morseEnergyBase U x * deriv φ x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul ht.2.2.1
  have hB : Integrable (fun x => morseEnergyBase U x * φ x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul ht.2.1
  have hW : Integrable (fun x => morseEnergyBase U x * (exp (-x) * φ x)) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul ht.2.2.2
  simp only [morseSignedFirstOrder_apply, inner_sub_left, inner_add_left, real_inner_smul_left,
    morseL2_inner_right_toLp, hd, hw]
  calc
    _ = (-c) * (∫ x : ℝ, morseEnergyBase U x * deriv φ x) +
        α * (∫ x : ℝ, morseEnergyBase U x * φ x) -
        w * (∫ x : ℝ, morseEnergyBase U x * (exp (-x) * φ x)) := by ring
    _ = ∫ x : ℝ, (-c) * (morseEnergyBase U x * deriv φ x) +
        α * (morseEnergyBase U x * φ x) - w * (morseEnergyBase U x * (exp (-x) * φ x)) := by
      have hs := integral_sub ((hD.const_mul (-c)).add (hB.const_mul α)) (hW.const_mul w)
      simp only [Pi.add_apply] at hs
      rw [hs, integral_add (hD.const_mul (-c)) (hB.const_mul α)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)

/-- The first-order adjoint relation against an actual smooth compact test. -/
theorem morseAnnihilationL2_compact_adjoint (α w : ℝ) (U : MorseWeakEnergy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let h := (compactSmooth_morseEnergyDomain hφ hc).2.1
    ⟪morseAnnihilationL2 α w U, h.toLp φ⟫_ℝ =
      ∫ x : ℝ, morseEnergyBase U x * morseCreation α w φ x := by
  intro h
  simpa only [morseAnnihilationL2, morseCreation, neg_one_mul] using
    morseSignedFirstOrder_compact_adjoint 1 α w U hφ hc

theorem morseCreationL2_compact_adjoint (α w : ℝ) (U : MorseWeakEnergy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let h := (compactSmooth_morseEnergyDomain hφ hc).2.1
    ⟪morseCreationL2 α w U, h.toLp φ⟫_ℝ =
      ∫ x : ℝ, morseEnergyBase U x * morseAnnihilation α w φ x := by
  intro h
  simpa only [morseCreationL2, morseAnnihilation, neg_neg, one_mul] using
    morseSignedFirstOrder_compact_adjoint (-1) α w U hφ hc

private theorem morseEnergy_eq_of_compact
    (F G : MorseWeakEnergy →L[ℝ] ℝ)
    (h : ∀ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      F (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) =
        G (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc))) (W : MorseWeakEnergy) :
    F W = G W := by
  let S : Set MorseWeakEnergy := {z | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    z = morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)}
  have hs : S ⊆ {z | F z = G z} := by
    rintro _ ⟨φ, hφ, hc, rfl⟩
    exact h φ hφ hc
  exact closure_minimal hs (isClosed_eq F.continuous G.continuous) (morseCompactSmoothEnergy_dense W)

theorem morseAnnihilationL2_adjoint (α w : ℝ) (U W : MorseWeakEnergy) :
    ⟪morseAnnihilationL2 α w U, morseEnergyBase W⟫_ℝ =
      ⟪morseEnergyBase U, morseCreationL2 α w W⟫_ℝ := by
  let F := (innerSL ℝ (morseAnnihilationL2 α w U)).comp morseEnergyBase
  let G := (innerSL ℝ (morseEnergyBase U)).comp (morseCreationL2 α w)
  change F W = G W
  apply morseEnergy_eq_of_compact F G _ W
  intro φ hφ hc
  let hE := compactSmooth_morseEnergyDomain hφ hc
  change ⟪morseAnnihilationL2 α w U, morseEnergyBase (morseEnergyLift hE)⟫_ℝ =
    ⟪morseEnergyBase U, morseCreationL2 α w (morseEnergyLift hE)⟫_ℝ
  have hC := morseCreation_memLp_of_energy hE α w
  rw [morseEnergyLift_base, morseCreationL2_lift hE α w hC,
    morseL2_inner_right_toLp (morseEnergyBase U) hC]
  exact morseAnnihilationL2_compact_adjoint α w U hφ hc

private theorem morseForm_of_compact_expression (U : MorseWeakEnergy) {φ F : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (a w b c : ℝ)
    (hExpr : ∀ x, morseExpression a w b φ x = F x + c * φ x) :
    let Z := morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)
    morsePhysicalForm a w b U Z = (∫ x : ℝ, morseEnergyBase U x * F x) +
      c * ⟪morseEnergyBase U, morseEnergyBase Z⟫_ℝ := by
  intro Z
  let H := morseExpression a w b φ
  have hH : Integrable (fun x => morseEnergyBase U x * H x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul (morseCompactImage_memLp hφ hc a w b)
  have hI : Integrable (fun x => morseEnergyBase U x * φ x) volume :=
    (Lp.memLp (morseEnergyBase U)).integrable_mul (compactSmooth_morseEnergyDomain hφ hc).2.1
  have hdiff : (∫ x : ℝ, morseEnergyBase U x * F x) =
      (∫ x : ℝ, morseEnergyBase U x * H x) - c * ∫ x : ℝ, morseEnergyBase U x * φ x := by
    calc
      _ = ∫ x : ℝ, morseEnergyBase U x * H x - c * (morseEnergyBase U x * φ x) := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun x => ?_)
        change _ = morseEnergyBase U x * morseExpression a w b φ x - c * (morseEnergyBase U x * φ x)
        rw [hExpr x]
        ring
      _ = _ := by rw [integral_sub hH (hI.const_mul c), integral_const_mul]
  change morsePhysicalForm a w b U (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc)) =
    (∫ x : ℝ, morseEnergyBase U x * F x) + c * ⟪morseEnergyBase U,
      morseEnergyBase (morseEnergyLift (compactSmooth_morseEnergyDomain hφ hc))⟫_ℝ
  rw [morsePhysicalForm_weak_test U hφ hc a w b, hdiff, morseEnergyLift_base,
    morseL2_inner_right_toLp]
  exact (sub_add_cancel _ _).symm

private def morseFirstOrderForm (D : MorseWeakEnergy →L[ℝ] MorseL2) (c : ℝ)
    (U : MorseWeakEnergy) : MorseWeakEnergy →L[ℝ] ℝ :=
  (innerSL ℝ (D U)).comp D + c • (innerSL ℝ (morseEnergyBase U)).comp morseEnergyBase

private theorem morseFirstOrderForm_apply (D : MorseWeakEnergy →L[ℝ] MorseL2) (c : ℝ)
    (U W : MorseWeakEnergy) : morseFirstOrderForm D c U W =
      ⟪D U, D W⟫_ℝ + c * ⟪morseEnergyBase U, morseEnergyBase W⟫_ℝ := rfl

/-- The first Darboux factorization holds on the entire closed energy space. -/
theorem morsePhysicalForm_factorization (α w b : ℝ) (U W : MorseWeakEnergy) :
    morsePhysicalForm α w b U W =
      ⟪morseAnnihilationL2 α w U, morseAnnihilationL2 α w W⟫_ℝ +
        (b - α ^ 2) * ⟪morseEnergyBase U, morseEnergyBase W⟫_ℝ := by
  let F := morsePhysicalForm α w b U
  let G := morseFirstOrderForm (morseAnnihilationL2 α w) (b - α ^ 2) U
  change F W = G W
  apply morseEnergy_eq_of_compact F G _ W
  intro φ hφ hc
  let hE := compactSmooth_morseEnergyDomain hφ hc
  change morsePhysicalForm α w b U (morseEnergyLift hE) =
    morseFirstOrderForm (morseAnnihilationL2 α w) (b - α ^ 2) U (morseEnergyLift hE)
  rw [morseFirstOrderForm_apply]
  have hD := contDiff_morseAnnihilation hφ α w
  have hcD := hasCompactSupport_morseAnnihilation hc α w
  rw [morseAnnihilationL2_lift hE α w (compactSmooth_morseEnergyDomain hD hcD).2.1,
    morseAnnihilationL2_compact_adjoint α w U hD hcD]
  exact morseForm_of_compact_expression U hφ hc α w b (b - α ^ 2)
    (morseExpression_factor (hφ.of_le (by simp)) α w b)

/-- The partner factorization shifts `α` by one and keeps the same energy
offset `b - α²`. -/
theorem morsePartnerPhysicalForm_factorization (α w b : ℝ) (U W : MorseWeakEnergy) :
    morsePhysicalForm (α - 1) w b U W =
      ⟪morseCreationL2 α w U, morseCreationL2 α w W⟫_ℝ +
        (b - α ^ 2) * ⟪morseEnergyBase U, morseEnergyBase W⟫_ℝ := by
  let F := morsePhysicalForm (α - 1) w b U
  let G := morseFirstOrderForm (morseCreationL2 α w) (b - α ^ 2) U
  change F W = G W
  apply morseEnergy_eq_of_compact F G _ W
  intro φ hφ hc
  let hE := compactSmooth_morseEnergyDomain hφ hc
  change morsePhysicalForm (α - 1) w b U (morseEnergyLift hE) =
    morseFirstOrderForm (morseCreationL2 α w) (b - α ^ 2) U (morseEnergyLift hE)
  rw [morseFirstOrderForm_apply]
  have hC := contDiff_morseCreation hφ α w
  have hcC := hasCompactSupport_morseCreation hc α w
  rw [morseCreationL2_lift hE α w (compactSmooth_morseEnergyDomain hC hcC).2.1,
    morseCreationL2_compact_adjoint α w U hC hcC]
  exact morseForm_of_compact_expression U hφ hc (α - 1) w b (b - α ^ 2)
    (morseExpression_partner_factor (hφ.of_le (by simp)) α w b)

end ContinuousFlexibility.Radial
