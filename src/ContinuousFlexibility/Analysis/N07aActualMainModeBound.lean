module

public import ContinuousFlexibility.Analysis.N07aRelativeMainIdentity
public import ContinuousFlexibility.Analysis.N07aActualPrincipalBlock
public import ContinuousFlexibility.Analysis.N07aModeEnergyNorm

/-!
# The mode bound for the actual relative source without its scalar columns

The original reference equation supplies the weak jets and the mode
energy.  Both ordinary blocks and frequency-commutator blocks retain a
positive height gain.  All geometric factors are collected into actual
sample subpower envelopes before the outer weighted estimate is taken.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}

local instance n07aActualMainModeBoundLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aActualMainModeBoundLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aActualMainModeBoundUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aActualMainModeBoundUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aActualMainModeBoundGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aActualMainModeBoundGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n07a_referenceInverse_field_reflection
    (h05 : N05Properties D T S C K V b B)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    n07aAngularReflection m (n07aReferenceInverseField (B := B) F m) =
      n07aReferenceInverseField (B := B) F m := by
  have hrel := (h05.2.2.2.2.2.2.1 (B.inverse F).val).mp (B.inverse F).property
  let W := hrel.1.choose
  have hW := hrel.1.choose_spec
  have h := n07a_volume_forget_reflection h05.2.1 W m
  rw [hW] at h
  exact h

private theorem n07a_scaledMode_bound {m : ℕ} (hm : K.left m < K.right m)
    (u v : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u)
    (j l : ℕ) (hb : n07aAngularBand m hm j u = u) {κ A : ℝ}
    (h : ‖κ • n07aCanonicalUnitMode hm v l‖ ≤ A * ‖n07aCanonicalUnitMode hm u j‖) :
    Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ‖κ • n07aCanonicalUnitMode hm v l‖ ≤ A * ‖u‖ := by
  have hn := n07aAngularBand_norm_unitMode hm u hu j
  rw [hb] at hn
  calc
    _ ≤ Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (A * ‖n07aCanonicalUnitMode hm u j‖) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = A * (Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ‖n07aCanonicalUnitMode hm u j‖) := by ring
    _ = _ := by rw [← hn]

private theorem n07a_principalMode_rearrange
    (a B E H p t Q N U : ℝ) :
    N * ((a * (B * E * H * p) * t) * (Q * U)) =
      H * t * ((a * B * E * Q * N) * p) * U := by
  ring

private theorem n07a_scaledMode_sum_bound {m : ℕ} (hm : K.left m < K.right m)
    (v w : CanonicalL2 S K m) (l : ℕ) (κ N H t a b U : ℝ) (hN : 0 ≤ N)
    (hv : N * ‖κ • n07aCanonicalUnitMode hm v l‖ ≤ H * t * a * U)
    (hw : N * ‖κ • n07aCanonicalUnitMode hm w l‖ ≤ H * t * b * U) :
    N * ‖κ • n07aCanonicalUnitMode hm (v + w) l‖ ≤ H * t * (a + b) * U := by
  rw [n07aCanonicalUnitMode_add, smul_add]
  calc
    _ ≤ N * (‖κ • n07aCanonicalUnitMode hm v l‖ +
        ‖κ • n07aCanonicalUnitMode hm w l‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hN
    _ = N * ‖κ • n07aCanonicalUnitMode hm v l‖ +
        N * ‖κ • n07aCanonicalUnitMode hm w l‖ := mul_add _ _ _
    _ ≤ H * t * a * U + H * t * b * U := add_le_add hv hw
    _ = _ := by ring

theorem n07a_actualRelativeMain_mode_bound
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hI : ∀ m, K.left m < K.right m) :
    ∃ d₁ d₂ : ℕ, ∀ s : ℕ, ∃ e₁ e₂ : ℕ → ℝ,
      N07aSampleSubpower T K e₁ ∧ N07aSampleSubpower T K e₂ ∧
      (∀ m, 0 ≤ e₁ m) ∧ (∀ m, 0 ≤ e₂ m) ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε),
      ∀ F : V.level (3 / 4 : ℝ) 0 b, ∀ m j l : ℕ,
      n07aAngularBand m (hI m) j (n07aReferenceInverseField (B := B) F m) =
        n07aReferenceInverseField (B := B) F m → ∀ commute : Bool,
      Real.sqrt (Real.pi * (K.right m - K.left m)) *
        ‖(((1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s) *
          (if commute then ((l : ℝ) - j) else 1)) •
          n07aCanonicalUnitMode (hI m)
            (n07aRelativeMainSource (P := P) href hcur z hz F m (hI m)) l‖ ≤
        T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * n07aAngularTail ((j : ℤ) - l) *
          (e₁ m * parameterGrading S (s + 4 + d₁) z +
            e₂ m * parameterGrading S (s + 4 + d₂) z) *
          (‖n07aReferenceInverseField (B := B) F m‖ +
            ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
              (V.forget (3 / 4 : ℝ) 0 b F)‖) := by
  have hE (m : ℕ) : 0 < T.E0 (T.sample (K.cell m)) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample (K.cell m)) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))).2.1
  have hab : D.a ≤ D.b := hD.choose_spec.1.2.1.le
  let energy := n07a_reference_actualMode_root_bound href hprincipal hE hI
  let A : ℝ := energy.choose
  let A₁ : ℝ := energy.choose_spec.choose
  let A₂ : ℝ := energy.choose_spec.choose_spec.choose
  have henergy := energy.choose_spec.choose_spec.choose_spec.2.2.2
  let principal := n07a_actualPrincipal_block_bound h01 h04 href hcur
  let potential := n07a_actualPotential_block_bound href hcur
  let d₁ : ℕ := principal.choose
  let d₂ : ℕ := potential.choose
  refine ⟨d₁, d₂, fun s => ?_⟩
  let B₁ : ℝ := (principal.choose_spec s).choose
  let B₂ : ℝ := (potential.choose_spec s).choose
  have hB₁ : 0 < B₁ := (principal.choose_spec s).choose_spec.1
  have hB₂ : 0 < B₂ := (potential.choose_spec s).choose_spec.1
  have hp := (principal.choose_spec s).choose_spec.2
  have hq := (potential.choose_spec s).choose_spec.2
  let e₁ : ℕ → ℝ := fun m =>
    112 * (1 + (K.right m - K.left m)) ^ 6 * B₁ * T.E0 (T.sample (K.cell m)) ^ B₁ *
      Real.sqrt (n07aReferenceModeBudget A A₁ A₂ (K.right m - K.left m)
        (T.E0 (T.sample (K.cell m)))) * Real.sqrt (Real.pi * (K.right m - K.left m))
  let e₂ : ℕ → ℝ := fun m => 8 * B₂ * T.E0 (T.sample (K.cell m)) ^ B₂
  have he₁ : N07aSampleSubpower T K e₁ :=
    n07a_principalModeEnvelope_subpower hD hT href A A₁ A₂ B₁
  have he₂ : N07aSampleSubpower T K e₂ := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT (8 * B₂)) (N07aSampleSubpower.e0_rpow hD hT B₂)
  have he₁₀ (m : ℕ) : 0 ≤ e₁ m := by
    have hEm := hE m
    have hℓ := sub_pos.mpr (hI m)
    dsimp only [e₁]
    positivity
  have he₂₀ (m : ℕ) : 0 ≤ e₂ m := by
    have hEm := hE m
    dsimp only [e₂]
    positivity
  refine ⟨e₁, e₂, he₁, he₂, he₁₀, he₂₀, fun z hz F m j l hband commute => ?_⟩
  let u := n07aReferenceInverseField (B := B) F m
  let G := n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
    (V.forget (3 / 4 : ℝ) 0 b F)
  let κ := ((1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s) *
    (if commute then ((l : ℝ) - j) else 1)
  let N := Real.sqrt (Real.pi * (K.right m - K.left m))
  let H := T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)
  let tail := n07aAngularTail ((j : ℤ) - l)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hH₀ : 0 ≤ H := (Real.rpow_pos_of_pos (hH m) _).le
  have ht : 0 ≤ tail := by unfold tail n07aAngularTail; positivity
  have hu := n07a_referenceInverse_field_reflection h05 F m
  have hpot : N * ‖κ • n07aCanonicalUnitMode (hI m)
      ((n07aRelativePotentialCoefficient href hcur z hz m (hI m)).mul u) l‖ ≤
      H * tail * (e₂ m * parameterGrading S (s + 4 + d₂) z) * (‖u‖ + ‖G‖) := by
    have h := n07a_scaledMode_bound (hI m) u _ hu j l hband
      (hq z hz m (hI m) u hu j l hband commute)
    have heq : (8 * n07aDifferenceBlockBudget T S K d₂ s B₂ z m * tail) * ‖u‖ =
        H * tail * (e₂ m * parameterGrading S (s + 4 + d₂) z) * ‖u‖ := by
      dsimp only [n07aDifferenceBlockBudget, H, e₂]
      ring
    exact (h.trans_eq heq).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg G))
      (mul_nonneg (mul_nonneg hH₀ ht) (mul_nonneg (he₂₀ m) (apply_nonneg _ _))))
  cases hm : K.positive m with
  | false =>
    rw [n07a_relativeMain_negative hab hS hT h01 h02 h03 h04 href hcur h05 h06
      z hz F m (hI m) hm]
    apply hpot.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
        (mul_nonneg (he₁₀ m) (apply_nonneg _ _))) (mul_nonneg hH₀ ht))
      (add_nonneg (norm_nonneg u) (norm_nonneg G))
  | true =>
    let jets := n07a_referenceInverse_finiteJets h05 F m
    let ur : CanonicalL2 S K m := jets.choose
    let uθ : CanonicalL2 S K m := jets.choose_spec.choose
    let urθ : CanonicalL2 S K m := jets.choose_spec.choose_spec.choose
    let uθθ : CanonicalL2 S K m := jets.choose_spec.choose_spec.choose_spec.choose
    have hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0 :=
      jets.choose_spec.choose_spec.choose_spec.choose_spec.1
    have hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1 :=
      jets.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    have hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1 :=
      jets.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
    have hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1 :=
      jets.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2
    have heqRaw := n07a_referenceDomain_distribution hab hS hT h01 h02 h03 h04 href
      h05 h06 (B.inverse F) m (hI m)
    have hsource : n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
        (V.forget (3 / 4 : ℝ) 0 b (B.inverse F).val.2) = G :=
      congrArg (fun F' : V.level (3 / 4 : ℝ) 0 b =>
        n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
          (V.forget (3 / 4 : ℝ) 0 b F')) (h05.2.2.2.2.2.2.2.1 F)
    have heq : N07aCanonicalDistributionEquation S K m
        (K.coefficients (C.referenceState, 0) m) u G :=
      Eq.mp (congrArg (fun G' : CanonicalL2 S K m =>
        N07aCanonicalDistributionEquation S K m
          (K.coefficients (C.referenceState, 0) m) u G') hsource) heqRaw
    let second :=
      n07a_reference_secondNormal_of_fourJets href hprincipal (hI m) hr hθ hrθ hθθ heq
    let urr : CanonicalL2 S K m := second.choose
    have hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 := second.choose_spec.1
    have he := henergy m hm u ur urr G hr hrr heq j
    have hb := hp z hz m hm (hI m) u ur uθ urr urθ uθθ hu j l hband hr hθ hrr hrθ hθθ commute
    have hc : 0 ≤ 112 * (1 + (K.right m - K.left m)) ^ 6 *
        n07aDifferenceBlockBudget T S K d₁ s B₁ z m * tail := by
      have hEm := hE m
      have hHm := hH m
      have hg := apply_nonneg (parameterGrading S (s + 4 + d₁)) z
      dsimp only [n07aDifferenceBlockBudget]
      positivity
    have hpr : N * ‖κ • n07aCanonicalUnitMode (hI m)
        (n07aRelativePrincipalJet href hcur z hz m (hI m) ur uθ urr urθ uθθ) l‖ ≤
        H * tail * (e₁ m * parameterGrading S (s + 4 + d₁) z) * (‖u‖ + ‖G‖) := by
      exact (mul_le_mul_of_nonneg_left
        (hb.trans (mul_le_mul_of_nonneg_left he hc)) hN).trans_eq
        (n07a_principalMode_rearrange (112 * (1 + (K.right m - K.left m)) ^ 6)
          B₁ (T.E0 (T.sample (K.cell m)) ^ B₁) H
          (parameterGrading S (s + 4 + d₁) z) tail
          (Real.sqrt (n07aReferenceModeBudget A A₁ A₂ (K.right m - K.left m)
            (T.E0 (T.sample (K.cell m))))) N (‖u‖ + ‖G‖))
    have hsource := n07a_relativeMain_expanded hab hS hT h01 h02 h03 h04 href hcur h05 h06
      z hz F m (hI m) ur uθ urr urθ uθθ hr hθ hrr hrθ hθθ
    have hmode := congrArg (fun v : CanonicalL2 S K m =>
      N * ‖κ • n07aCanonicalUnitMode (hI m) v l‖) hsource
    exact hmode.le.trans (n07a_scaledMode_sum_bound (hI m)
      (n07aRelativePrincipalJet href hcur z hz m (hI m) ur uθ urr urθ uθθ)
      ((n07aRelativePotentialCoefficient href hcur z hz m (hI m)).mul u)
      l κ N H tail (e₁ m * parameterGrading S (s + 4 + d₁) z)
      (e₂ m * parameterGrading S (s + 4 + d₂) z) (‖u‖ + ‖G‖) hN hpr hpot)

end ContinuousFlexibility.Analysis
