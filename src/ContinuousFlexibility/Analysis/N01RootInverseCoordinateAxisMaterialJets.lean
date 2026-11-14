module

public import ContinuousFlexibility.Analysis.N01RootStationaryFlowMaterialJets
public import ContinuousFlexibility.Analysis.N01RootLabelUniformJets
public import ContinuousFlexibility.Analysis.ActualRootChart

/-!
# Uniform material jets of the same normalized inverse coordinate

The actual stationary flow inverse and the original normalized root label
are composed at the zero parameter axis. Reassociation is an isometry.
Only the angular displacement is estimated at order zero; its bound is
the genuine pi bound of the original label. Neither a strip radius nor
the arbitrary parameter normalization contributes an inverse cost.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem le_mul_rpow_of_le_pi {y B W t : ℝ} (hy : y ≤ Real.pi) (hB : Real.pi ≤ B)
    (hW : 1 ≤ W) (ht : 0 ≤ t) : y ≤ B * W ^ B * (1 + t) := by
  have hB0 : 0 ≤ B := Real.pi_pos.le.trans hB
  have h1 : 1 ≤ W ^ B * (1 + t) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hW hB0) (le_add_of_nonneg_right ht)
  calc
    y ≤ Real.pi := hy
    _ ≤ B := hB
    _ = B * 1 := (mul_one B).symm
    _ ≤ B * (W ^ B * (1 + t)) := mul_le_mul_of_nonneg_left h1 hB0
    _ = B * W ^ B * (1 + t) := (mul_assoc _ _ _).symm

/-- The positive-order estimate for an arbitrary graded state space. All
grading manipulations happen here, away from the actual state spaces. -/
private theorem rootInverse_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E)
    {lossL lossF lossC lowC : ℕ} (hxC : p lowC x ≤ 1)
    {BL BF A BC : ℕ → ℝ} (hBL : ∀ k, 0 < BL k) (hBF : ∀ k, 0 < BF k)
    (hA : ∀ k, 1 ≤ A k) (hLA : ∀ k, 1 + BL k ≤ A k) (hFA : ∀ k, BF k ≤ A k)
    (hBC : ∀ k, 0 < BC k) {W B : ℝ} (hW : 1 ≤ W)
    {l : ℝ → ℝ} {J G : ℝ × ℝ × ℝ → ℝ} (hl : ContDiff ℝ ∞ l) (hJ : ContDiff ℝ ∞ J)
    (hGeq : G = l ∘ J) {q : ℝ × ℝ × ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hπjet : ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => q.2.2) q‖ ≤ 1)
    (hlabel : ∀ k, ‖iteratedFDeriv ℝ k (fun η => l η - η) (J q)‖ ≤
      BL k * (1 + p (k + lossL) x))
    (hinnerJ : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k J q‖ ≤
      BF k * W ^ (BF k) * (1 + p (k + lossF) x))
    (hcompose : ∀ z : E, p lowC z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ (f : ℝ → ℝ) (g : ℝ × ℝ × ℝ → ℝ) (y : ℝ × ℝ × ℝ),
        ContDiffAt ℝ ∞ f (g y) → ContDiffAt ℝ ∞ g y →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k f (g y)‖ ≤
          A k * W ^ (A k) * (1 + p (k + max lossL lossF) z)) →
        (∀ k : ℕ, 1 ≤ k → ‖iteratedFDeriv ℝ k g y‖ ≤
          A k * W ^ (A k) * (1 + p (k + max lossL lossF) z)) →
        ∀ n : ℕ, ‖iteratedFDeriv ℝ (n + 1) (f ∘ g) y‖ ≤
          BC n * W ^ (BC n) * (1 + p ((n + 1) + lossC) z))
    (hcoef : BC (n - 1) + 1 ≤ B) :
    ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => G q - q.2.2) q‖ ≤
      B * W ^ B * (1 + p (n + lossC) x) := by
  have hw (i : ℕ) : 0 ≤ p i x := apply_nonneg _ _
  have hWpos : 0 ≤ W := zero_le_one.trans hW
  have houter (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k l (J q)‖ ≤
      A k * W ^ (A k) * (1 + p (k + max lossL lossF) x) := by
    have hid : ‖iteratedFDeriv ℝ k (id : ℝ → ℝ) (J q)‖ ≤ 1 :=
      (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℝ) hk _).trans
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
    have he : l = (fun η => l η - η) + id := by
      funext η
      simp only [Pi.add_apply, id_eq, sub_add_cancel]
    have hraw : ‖iteratedFDeriv ℝ k l (J q)‖ ≤ BL k * (1 + p (k + lossL) x) + 1 := by
      rw [he, iteratedFDeriv_add_apply (f := fun η => l η - η) (g := id)
        ((hl.sub contDiff_id).contDiffAt.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
        (contDiffAt_id.of_le (by simp : (k : ℕ∞ω) ≤ ∞))]
      exact (norm_add_le _ _).trans (add_le_add (hlabel k) hid)
    have hgrade : p (k + lossL) x ≤ p (k + max lossL lossF) x :=
      hp (Nat.add_le_add_left (le_max_left lossL lossF) k) x
    have hwk := hw (k + max lossL lossF)
    have hWA : 1 ≤ W ^ (A k) := Real.one_le_rpow hW (zero_le_one.trans (hA k))
    have hprod := mul_le_mul_of_nonneg_left hgrade (hBL k).le
    calc
      ‖iteratedFDeriv ℝ k l (J q)‖ ≤ BL k * (1 + p (k + lossL) x) + 1 := hraw
      _ ≤ (1 + BL k) * (1 + p (k + max lossL lossF) x) := by
        nlinarith only [hprod, hwk]
      _ ≤ A k * (1 + p (k + max lossL lossF) x) :=
        mul_le_mul_of_nonneg_right (hLA k) (add_nonneg zero_le_one hwk)
      _ ≤ A k * W ^ (A k) * (1 + p (k + max lossL lossF) x) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans (hA k)) hWA)
          (add_nonneg zero_le_one hwk)
  have hinner (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k J q‖ ≤
      A k * W ^ (A k) * (1 + p (k + max lossL lossF) x) :=
    (hinnerJ k hk).trans (mul_le_mul
      (mul_le_mul (hFA k) (Real.rpow_le_rpow_of_exponent_le hW (hFA k))
        (Real.rpow_nonneg hWpos _) (zero_le_one.trans (hA k)))
      (add_le_add le_rfl (hp (Nat.add_le_add_left (le_max_right lossL lossF) k) x))
      (add_nonneg zero_le_one (hw _))
      (mul_nonneg (zero_le_one.trans (hA k)) (Real.rpow_nonneg hWpos _)))
  have hc := hcompose x hxC W hW l J q hl.contDiffAt hJ.contDiffAt houter hinner (n - 1)
  rw [Nat.sub_add_cancel hn, ← hGeq] at hc
  have hG : ContDiff ℝ ∞ G := by
    rw [hGeq]
    exact hl.comp hJ
  have hsub : (fun q : ℝ × ℝ × ℝ => G q - q.2.2) = G - (fun q : ℝ × ℝ × ℝ => q.2.2) := by
    funext y
    simp only [Pi.sub_apply]
  have hdisp' : ‖iteratedFDeriv ℝ n (G - fun q : ℝ × ℝ × ℝ => q.2.2) q‖ ≤
      BC (n - 1) * W ^ (BC (n - 1)) * (1 + p (n + lossC) x) + 1 := by
    rw [iteratedFDeriv_sub_apply
      (hG.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      ((contDiff_snd.snd : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.2.2)).contDiffAt.of_le
        (by simp : (n : ℕ∞ω) ≤ ∞))]
    exact (norm_sub_le _ _).trans (add_le_add hc hπjet)
  have hdisp : ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ × ℝ => G q - q.2.2) q‖ ≤
      BC (n - 1) * W ^ (BC (n - 1)) * (1 + p (n + lossC) x) + 1 :=
    (congrArg (fun F => ‖iteratedFDeriv ℝ n F q‖) hsub).trans_le hdisp'
  have hw' := hw (n + lossC)
  have hB0 : 0 ≤ B := by linarith only [hBC (n - 1), hcoef]
  have hWB : W ^ (BC (n - 1)) ≤ W ^ B :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith only [hcoef])
  have hWB1 : 1 ≤ W ^ B := Real.one_le_rpow hW hB0
  have hT : 1 ≤ W ^ B * (1 + p (n + lossC) x) :=
    one_le_mul_of_one_le_of_one_le hWB1 (le_add_of_nonneg_right hw')
  have hfin := mul_le_mul_of_nonneg_right hcoef (zero_le_one.trans hT)
  calc
    _ ≤ BC (n - 1) * W ^ (BC (n - 1)) * (1 + p (n + lossC) x) + 1 := hdisp
    _ ≤ BC (n - 1) * W ^ B * (1 + p (n + lossC) x) + W ^ B * (1 + p (n + lossC) x) :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hWB (hBC (n - 1)).le)
        (add_nonneg zero_le_one hw')) hT
    _ ≤ B * W ^ B * (1 + p (n + lossC) x) := by nlinarith only [hfin]

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
  refine (n01_rootFlow_unit_axis_material_jets_of_component_optical hS hT hN hK).elim ?_
  intro C0 hF1
  refine hF1.elim ?_
  intro lowF hF2
  refine hF2.elim ?_
  intro lossF hF3
  have hC0 := hF3.1
  have hfloor := hF3.2.1
  refine hF3.2.2.elim ?_
  intro BF hBFr
  have hBF := hBFr.1
  have hroot := hBFr.2
  refine (n01_rootLabels_displacement_uniform hS hT hN hflow).elim ?_
  intro lowL hL1
  refine hL1.elim ?_
  intro lossL hL2
  refine hL2.elim ?_
  intro BL hBLl
  have hBL := hBLl.1
  have hlabels := hBLl.2
  refine (coordinateComposition_fixed_loss_material_bound
      (X := ℝ × ℝ × ℝ) (Y := ℝ) (Z := ℝ) hp hI (max lossL lossF)).elim ?_
  intro lowC hC1
  refine hC1.elim ?_
  intro lossC htarget
  let A : ℕ → ℝ := fun n => 1 + BL n + BF n
  have hA (n : ℕ) : 1 ≤ A n := by
    dsimp only [A]
    linarith only [hBL n, hBF n]
  have hLA (n : ℕ) : 1 + BL n ≤ A n := by
    dsimp only [A]
    linarith only [hBF n]
  have hFA (n : ℕ) : BF n ≤ A n := by
    dsimp only [A]
    linarith only [hBL n]
  refine (htarget A hA).elim ?_
  intro BC hBCc
  have hBC := hBCc.1
  have hcompose := hBCc.2
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
  have hGzero : G (0, 0, θ) = l θ :=
    rootInverseCoordinate_zero Real.pi_ne_zero hΘ₁.1 hΘ₁.2
      (n04Flow_contDiff_slice hfield hfieldPeriod hΘ₁ ht)
      (fun v η => n04Flow_period_add hfield hfieldPeriod hΘ₁ v η ht) θ
  by_cases hn0 : n = 0
  · subst n
    have hπB : Real.pi ≤ B 0 := by
      dsimp only [B]
      linarith only [hBC (0 - 1)]
    have hy : ‖iteratedFDeriv ℝ 0 (fun q : ℝ × ℝ × ℝ => G q - q.2.2) (0, 0, θ)‖ ≤
        Real.pi := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      change |G (0, 0, θ) - θ| ≤ _
      rw [hGzero]
      exact n01_rootLabel_displacement_le_pi hN hflow hz hs m side θ
    exact le_mul_rpow_of_le_pi hy hπB (hfloor j) (apply_nonneg _ _)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hJI (k : ℕ) : ‖iteratedFDeriv ℝ k J (0, 0, θ)‖ =
      ‖iteratedFDeriv ℝ k I ((0, 0), θ)‖ :=
    e.norm_iteratedFDeriv_comp_right I (0, 0, θ) k
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
  have hcoef : BC (n - 1) + 1 ≤ B n := by
    dsimp only [B]
    linarith only [Real.pi_pos]
  exact rootInverse_jet_bound_generic hp (z - (C.referenceState, 0)) hzC hBL hBF hA hLA hFA
    hBC (hfloor j) hl hJ hGeq hn hπjet
    (fun k => hlabels m z hz hs hzL side k (J (0, 0, θ)))
    (fun k hk => (hJI k).trans_le (hroot z hz hs hzF m j hhost hoptical side g hg hfactor
      R hR hstrip δ hδ Θ hΘ θ 1 ht k hk).2)
    hcompose hcoef

end ContinuousFlexibility.Analysis
