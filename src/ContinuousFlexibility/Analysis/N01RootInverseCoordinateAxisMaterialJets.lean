import ContinuousFlexibility.Analysis.N01RootStationaryFlowMaterialJets
import ContinuousFlexibility.Analysis.N01RootLabelUniformJets
import ContinuousFlexibility.Analysis.ActualRootChart

/-!
# Uniform material jets of the same normalized inverse coordinate

The actual stationary flow inverse and the original normalized root label
are composed at the zero parameter axis. Reassociation is an isometry.
Only the angular displacement is estimated at order zero; its bound is
the genuine pi bound of the original label. Neither a strip radius nor
the arbitrary parameter normalization contributes an inverse cost.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_rootInverseCoordinate_unit_axis_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ x, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * x) = x * g x) →
      ∀ R : ℝ, ∀ hR : 0 < R,
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R →
      ∀ δ : ℝ, δ ≠ 0 → ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z) δ) Θ →
      ∀ θ : ℝ, ∀ n : ℕ,
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => G q - q.2.2) (0, 0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨C0, lowF, lossF, hC0, hfloor, BF, hBF, hroot⟩ :=
    n01_rootFlow_unit_axis_material_jets_of_component_optical hS hT hN hK
  obtain ⟨lowL, lossL, BL, hBL, hlabels⟩ :=
    n01_rootLabels_displacement_uniform hS hT hN hflow
  let inputLoss := max lossL lossF
  obtain ⟨lowC, lossC, htarget⟩ :=
    coordinateComposition_fixed_loss_material_bound
      (X := ℝ × ℝ × ℝ) (Y := ℝ) (Z := ℝ) hp hI inputLoss
  let A : ℕ → ℝ := fun n => 1 + BL n + BF n
  have hA (n : ℕ) : 1 ≤ A n := by
    dsimp only [A]
    linarith only [hBL n, hBF n]
  obtain ⟨BC, hBC, hcompose⟩ := htarget A hA
  let B : ℕ → ℝ := fun n => Real.pi + BC (n - 1) + 2
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith only [Real.pi_pos, hBC (n - 1)]
  refine ⟨C0, max lowF (max lowL lowC), lossC, hC0, hfloor, B, hB, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ n
  have hzF := (hp (le_max_left lowF (max lowL lowC)) _).trans hlow
  have hzL := (hp ((le_max_left lowL lowC).trans
    (le_max_right lowF (max lowL lowC))) _).trans hlow
  have hzC := (hp ((le_max_right lowL lowC).trans
    (le_max_right lowF (max lowL lowC))) _).trans hlow
  let W := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  let Θ₁ := rootFlowParameterUnscale Θ δ
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hfield := contDiff_rootRegularizedField hregular.1 hregular.2
  have hfieldPeriod := rootRegularizedField_periodic hperiod.1 hperiod.2
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  let f : N04FlowPoint → ℝ := fun q => Θ₁ q.1 1 q.2
  let I : N04FlowPoint → ℝ := parameterizedCircleInverse f
  let e : (ℝ × ℝ × ℝ) ≃ₗᵢ[ℝ] N04FlowPoint :=
    (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm
  let J : ℝ × ℝ × ℝ → ℝ := I ∘ e
  let l : ℝ → ℝ := n01RootLabel S C z m side
  let G := rootInverseCoordinate Θ₁ l
  have hl : ContDiff ℝ ∞ l := n01RootLabel_contDiff hS hT hN hz hs m side
  have hIregular : ContDiff ℝ ∞ I :=
    contDiff_n04FlowInverse hfield hfieldPeriod hΘ₁ ht
  have hJ : ContDiff ℝ ∞ J := hIregular.comp e.contDiff
  have hGeq : G = l ∘ J := by funext q; rfl
  have hG : ContDiff ℝ ∞ G := by rw [hGeq]; exact hl.comp hJ
  have hGzero : G (0, 0, θ) = l θ :=
    rootInverseCoordinate_zero Real.pi_ne_zero hΘ₁.1 hΘ₁.2
      (n04Flow_contDiff_slice hfield hfieldPeriod hΘ₁ ht)
      (fun v η => n04Flow_period_add hfield hfieldPeriod hΘ₁ v η ht) θ
  have hstate (k : ℕ) : 1 ≤ 1 + pairGrading (stateGrading S) realGrading
      (k + lossC) (z - (C.referenceState, 0)) :=
    le_add_of_nonneg_right (apply_nonneg _ _)
  have hBweight (k : ℕ) : 1 ≤ W ^ (B k) *
      (1 + pairGrading (stateGrading S) realGrading (k + lossC)
        (z - (C.referenceState, 0))) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW (hB k).le) (hstate k)
  by_cases hn0 : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    change |G (0, 0, θ) - θ| ≤ _
    rw [hGzero]
    apply (n01_rootLabel_displacement_le_pi hN hflow hz hs m side θ).trans
    have hπB : Real.pi ≤ B 0 := by
      dsimp only [B]
      linarith only [hBC (0 - 1)]
    exact hπB.trans (by
      simpa only [mul_one, mul_assoc] using
        mul_le_mul_of_nonneg_left (hBweight 0) (hB 0).le)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have houter (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k l (J (0, 0, θ))‖ ≤
      A k * W ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
        (k + inputLoss) (z - (C.referenceState, 0))) := by
    have hb := hlabels m z hz hs hzL side k (J (0, 0, θ))
    have hid : ‖iteratedFDeriv ℝ k (id : ℝ → ℝ) (J (0, 0, θ))‖ ≤ 1 :=
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℝ) hk _).trans
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
    have he : l = (fun η => l η - η) + id := by funext η; simp
    have hraw : ‖iteratedFDeriv ℝ k l (J (0, 0, θ))‖ ≤
        BL k * (1 + pairGrading (stateGrading S) realGrading
          (k + lossL) (z - (C.referenceState, 0))) + 1 := by
      rw [he, iteratedFDeriv_add_apply
        ((hl.sub contDiff_id).contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
        (contDiffAt_id.of_le (by simp : (k : ℕ∞ω) ≤ ∞))]
      exact (norm_add_le _ _).trans (add_le_add hb hid)
    have hgrade := hp (Nat.add_le_add_left (le_max_left lossL lossF) k)
      (z - (C.referenceState, 0))
    have hnonneg := apply_nonneg (pairGrading (stateGrading S) realGrading
      (k + inputLoss)) (z - (C.referenceState, 0))
    have hcoef : 1 + BL k ≤ A k := by dsimp only [A]; linarith only [hBF k]
    have hraw' : ‖iteratedFDeriv ℝ k l (J (0, 0, θ))‖ ≤ A k *
        (1 + pairGrading (stateGrading S) realGrading (k + inputLoss)
          (z - (C.referenceState, 0))) := hraw.trans (by
      calc
        _ ≤ BL k * (1 + pairGrading (stateGrading S) realGrading (k + inputLoss)
            (z - (C.referenceState, 0))) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hgrade) (hBL k).le) le_rfl
        _ ≤ (1 + BL k) * (1 + pairGrading (stateGrading S) realGrading (k + inputLoss)
            (z - (C.referenceState, 0))) := by nlinarith only [hnonneg]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (add_nonneg zero_le_one hnonneg))
    exact hraw'.trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.one_le_rpow hW (zero_le_one.trans (hA k)))
            (zero_le_one.trans (hA k))) (add_nonneg zero_le_one hnonneg))
  have hinner (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k J (0, 0, θ)‖ ≤
      A k * W ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
        (k + inputLoss) (z - (C.referenceState, 0))) := by
    have hb := (hroot z hz hs hzF m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ 1 ht k hk).2
    have hb' : ‖iteratedFDeriv ℝ k J (0, 0, θ)‖ ≤
        BF k * W ^ (BF k) * (1 + pairGrading (stateGrading S) realGrading
          (k + lossF) (z - (C.referenceState, 0))) := by
      change ‖iteratedFDeriv ℝ k (I ∘ e) (0, 0, θ)‖ ≤ _
      rw [e.norm_iteratedFDeriv_comp_right I (0, 0, θ) k]
      exact hb
    have hcoef : BF k ≤ A k := by dsimp only [A]; linarith only [hBL k]
    exact hb'.trans (mul_le_mul
      (mul_le_mul hcoef (Real.rpow_le_rpow_of_exponent_le hW hcoef)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans (hA k)))
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lossL lossF) k) _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg (zero_le_one.trans (hA k))
        (Real.rpow_nonneg (zero_le_one.trans hW) _)))
  have hc := hcompose (z - (C.referenceState, 0)) hzC W hW l J (0, 0, θ)
    hl.contDiffAt hJ.contDiffAt houter hinner (n - 1)
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hpred, ← hGeq] at hc
  let π : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hπnorm : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa only [π, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      one_mul] using (norm_snd_le q.2).trans (norm_snd_le q)
  have hπjet : ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => q.2.2) (0, 0, θ)‖ ≤ 1 :=
    (flowJet_norm_iteratedFDeriv_clm_le π hn (0, 0, θ)).trans hπnorm
  have hdisp : ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => G q - q.2.2) (0, 0, θ)‖ ≤
      BC (n - 1) * W ^ (BC (n - 1)) *
        (1 + pairGrading (stateGrading S) realGrading (n + lossC)
          (z - (C.referenceState, 0))) + 1 := by
    rw [iteratedFDeriv_sub_apply
      (hG.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      ((contDiff_snd.snd : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.2)).contDiffAt.of_le
        (by simp : (n : ℕ∞ω) ≤ ∞))]
    exact (norm_sub_le _ _).trans (add_le_add hc hπjet)
  have hcoef : BC (n - 1) + 1 ≤ B n := by
    dsimp only [B]
    linarith only [Real.pi_pos]
  have hpwr := Real.rpow_le_rpow_of_exponent_le hW
    (show BC (n - 1) ≤ B n by linarith only [hcoef])
  apply hdisp.trans
  calc
    _ ≤ BC (n - 1) * W ^ (B n) *
        (1 + pairGrading (stateGrading S) realGrading (n + lossC)
          (z - (C.referenceState, 0))) + W ^ (B n) *
        (1 + pairGrading (stateGrading S) realGrading (n + lossC)
          (z - (C.referenceState, 0))) :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpwr (hBC (n - 1)).le)
        (zero_le_one.trans (hstate n))) (hBweight n)
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_right hcoef (zero_le_one.trans (hBweight n))]

end ContinuousFlexibility.Analysis
