import ContinuousFlexibility.Analysis.N01RootSpeedPowerMaterialJets
import ContinuousFlexibility.Analysis.N01RootFieldLocalization
import ContinuousFlexibility.Analysis.RootFlowParameterUnscale
import ContinuousFlexibility.Analysis.RootStationaryInverseMaterialJets

/-!
# The same actual root flow with uniform zero-axis material costs

The localized fields have exactly the original jets at the root, at
every order. The already chosen scaled flow is then reparametrized to
unit scale. Its forward and actual circle-inverse jets follow from the
stationary ODE estimates. No inverse model radius or normalization scale
is charged. The raw optical lower remains an explicit same-witness input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem rootFlow_material_envelope_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {a b V W : ℝ} {k l m : ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 ≤ b)
    (hV : 1 ≤ V) (hVW : V ≤ W) (hlm : l ≤ m) (z : E) :
    a * V ^ a * (1 + p (k + l) z) ≤ b * W ^ b * (1 + p (k + m) z) := by
  have hW : 1 ≤ W := hV.trans hVW
  have hpower : V ^ a ≤ W ^ b :=
    (Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
      (Real.rpow_le_rpow_of_exponent_le hW hab)
  exact mul_le_mul
    (mul_le_mul hab hpower (Real.rpow_nonneg (zero_le_one.trans hV) _) hb)
    (add_le_add le_rfl (hp (Nat.add_le_add_left hlm k) z))
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (mul_nonneg hb (Real.rpow_nonneg (zero_le_one.trans hW) _))

/-- The flow and inverse estimates for an arbitrary graded state space. All
grading manipulations happen here, away from the actual state spaces. -/
private theorem rootFlow_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E)
    {lossD lossC flowLoss inverseLoss flowLow inverseLow outLoss : ℕ}
    (hxF : p flowLow x ≤ 1) (hxI : p inverseLow x ≤ 1)
    (hFout : flowLoss ≤ outLoss) (hIout : inverseLoss ≤ outLoss)
    {BD BC A BF BI B : ℕ → ℝ} (hBD : ∀ k, 0 < BD k) (hBC : ∀ k, 0 < BC k)
    (hA : ∀ k, 1 ≤ A k) (hDA : ∀ k, BD k ≤ A k) (hCA : ∀ k, BC k ≤ A k)
    (hBF : ∀ k, 0 < BF k) (hBI : ∀ k, 0 < BI k) (hB : ∀ k, 0 < B k)
    (hBFB : ∀ k, BF (k - 1) ≤ B k) (hBIB : ∀ k, BI k ≤ B k)
    {VD VC W : ℝ} (hVD : 1 ≤ VD) (hVC : 1 ≤ VC) (hVDW : VD ≤ W) (hVCW : VC ≤ W)
    {d c : PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdper : ∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi)
    (hcper : ∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} (hΘ : N04FlowEquations (rootRegularizedField d c) Θ)
    {θ : ℝ}
    (hdj : ∀ k, ‖iteratedFDeriv ℝ k d (0, θ)‖ ≤ BD k * VD ^ (BD k) * (1 + p (k + lossD) x))
    (hcj : ∀ k, ‖iteratedFDeriv ℝ k c (0, θ)‖ ≤ BC k * VC ^ (BC k) * (1 + p (k + lossC) x))
    (hforward : ∀ z : E, p flowLow z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
        (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRegularizedField d c) Θ →
      ∀ θ : ℝ,
      (∀ n, ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + max lossD lossC) z)) →
      (∀ n, ‖iteratedFDeriv ℝ n c (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + max lossD lossC) z)) →
      ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1)
          (fun y : N04FlowPoint => Θ y.1 t y.2) ((0, 0), θ)‖ ≤
          BF n * W ^ (BF n) * (1 + p ((n + 1) + flowLoss) z))
    (hbackward : ∀ z : E, p inverseLow z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ d c : PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) →
        (∀ r, Function.Periodic (fun θ => c (r, θ)) Real.pi) →
      ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
        N04FlowEquations (rootRegularizedField d c) Θ →
      ∀ θ : ℝ,
      (∀ n, ‖iteratedFDeriv ℝ n d (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + max lossD lossC) z)) →
      (∀ n, ‖iteratedFDeriv ℝ n c (0, θ)‖ ≤
        A n * W ^ (A n) * (1 + p (n + max lossD lossC) z)) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n →
        ‖iteratedFDeriv ℝ n
          (parameterizedCircleInverse (fun y : N04FlowPoint => Θ y.1 t y.2))
            ((0, 0), θ)‖ ≤
          BI n * W ^ (BI n) * (1 + p (n + inverseLoss) z))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y : N04FlowPoint => Θ y.1 t y.2) ((0, 0), θ)‖ ≤
        B n * W ^ (B n) * (1 + p (n + outLoss) x) ∧
      ‖iteratedFDeriv ℝ n (parameterizedCircleInverse
          (fun y : N04FlowPoint => Θ y.1 t y.2)) ((0, 0), θ)‖ ≤
        B n * W ^ (B n) * (1 + p (n + outLoss) x) := by
  have hW : 1 ≤ W := hVD.trans hVDW
  have hdb (k : ℕ) : ‖iteratedFDeriv ℝ k d (0, θ)‖ ≤
      A k * W ^ (A k) * (1 + p (k + max lossD lossC) x) :=
    (hdj k).trans (rootFlow_material_envelope_mono hp (hBD k).le (hDA k)
      (zero_le_one.trans (hA k)) hVD hVDW (le_max_left lossD lossC) x)
  have hcb (k : ℕ) : ‖iteratedFDeriv ℝ k c (0, θ)‖ ≤
      A k * W ^ (A k) * (1 + p (k + max lossD lossC) x) :=
    (hcj k).trans (rootFlow_material_envelope_mono hp (hBC k).le (hCA k)
      (zero_le_one.trans (hA k)) hVC hVCW (le_max_right lossD lossC) x)
  have hf := hforward x hxF W hW d c hd hc hdper hcper Θ hΘ θ hdb hcb (n - 1) t ht
  have hi := hbackward x hxI W hW d c hd hc hdper hcper Θ hΘ θ hdb hcb t ht n hn
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hpred] at hf
  exact ⟨hf.trans (rootFlow_material_envelope_mono hp (hBF (n - 1)).le (hBFB n) (hB n).le
      hW le_rfl hFout x),
    hi.trans (rootFlow_material_envelope_mono hp (hBI n).le (hBIB n) (hB n).le
      hW le_rfl hIout x)⟩

theorem n01_rootFlow_unit_axis_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hK : 0 < K) :
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
      ∀ θ : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n →
        let f : N04FlowPoint → ℝ :=
          fun y => rootFlowParameterUnscale Θ δ y.1 t y.2
        ‖iteratedFDeriv ℝ n f ((0, 0), θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) ∧
        ‖iteratedFDeriv ℝ n (parameterizedCircleInverse f) ((0, 0), θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  refine (n01_orientedRootDrift_axis_material_jets hS hT hN).elim ?_
  intro CD hD1
  refine hD1.elim ?_
  intro lowD hD2
  refine hD2.elim ?_
  intro lossD hD3
  have hCD := hD3.1
  have hfloorD := hD3.2.1
  refine hD3.2.2.elim ?_
  intro BD hBDj
  have hBD := hBDj.1
  have hjetsD := hBDj.2
  refine (n01_rootSpeed_axis_rpow_material_jets_of_component_optical hS hT hN hK).elim ?_
  intro CC hC1
  refine hC1.elim ?_
  intro lowC hC2
  refine hC2.elim ?_
  intro lossC hC3
  have hfloorC := hC3.2.1
  have hpowersC := hC3.2.2
  refine (hpowersC (1 : ℝ)).elim ?_
  intro BC hBCj
  have hBC := hBCj.1
  have hjetsC := hBCj.2
  let C0 := max CD CC
  have hC0 : 1 ≤ C0 := hCD.trans (le_max_left _ _)
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorD j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ((hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1.le))
  let A : ℕ → ℝ := fun n => max 1 (max (BD n) (BC n))
  have hA (n : ℕ) : 1 ≤ A n := le_max_left _ _
  have hDA (n : ℕ) : BD n ≤ A n := (le_max_left _ _).trans (le_max_right _ _)
  have hCA (n : ℕ) : BC n ≤ A n := (le_max_right _ _).trans (le_max_right _ _)
  refine (rootRegularizedFlow_zero_positiveJets_le_material hp hI
    (max lossD lossC)).elim ?_
  intro flowLow hF1
  refine hF1.elim ?_
  intro flowLoss hflow
  refine (rootRegularizedFlow_zero_inverseJets_le_material hp hI
    (max lossD lossC)).elim ?_
  intro inverseLow hI1
  refine hI1.elim ?_
  intro inverseLoss hinverse
  refine (hflow A hA).elim ?_
  intro BF hBFf
  have hBF := hBFf.1
  have hforward := hBFf.2
  refine (hinverse A hA).elim ?_
  intro BI hBIb
  have hBI := hBIb.1
  have hbackward := hBIb.2
  let B : ℕ → ℝ := fun n => max 1 (max (BF (n - 1)) (BI n))
  have hB (n : ℕ) : 0 < B n := zero_lt_one.trans_le (le_max_left _ _)
  have hBFB (n : ℕ) : BF (n - 1) ≤ B n := (le_max_left _ _).trans (le_max_right _ _)
  have hBIB (n : ℕ) : BI n ≤ B n := (le_max_right _ _).trans (le_max_right _ _)
  let low := max lowD (max lowC (max flowLow inverseLow))
  let outLoss := max flowLoss inverseLoss
  refine ⟨C0, low, outLoss, hC0, hsample, B, hB, ?_⟩
  intro z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ t ht n hn
  have hzD := (hp (le_max_left lowD (max lowC (max flowLow inverseLow))) _).trans hzlow
  have hzC := (hp ((le_max_left lowC (max flowLow inverseLow)).trans
    (le_max_right lowD (max lowC (max flowLow inverseLow)))) _).trans hzlow
  have hzF := (hp ((le_max_left flowLow inverseLow).trans
    ((le_max_right lowC (max flowLow inverseLow)).trans
      (le_max_right lowD (max lowC (max flowLow inverseLow))))) _).trans hzlow
  have hzI := (hp ((le_max_right flowLow inverseLow).trans
    ((le_max_right lowC (max flowLow inverseLow)).trans
      (le_max_right lowD (max lowC (max flowLow inverseLow))))) _).trans hzlow
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hWD : CD * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
  have hWC : CC * T.E0 (T.sample j) ≤ C0 * T.E0 (T.sample j) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hzero : |((0, θ) : PolarPoint).1| ≤ R / 4 := by
    simpa only [abs_zero] using (div_pos hR (by norm_num : (0 : ℝ) < 4)).le
  have hlocal (k : ℕ) :=
    iteratedFDeriv_localizedRootFields_eq D S C g r σ hR z k (q := (0, θ)) hzero
  have hFone : (fun p => factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ p ^ (1 : ℝ)) =
      factoredCharacteristicSpeed D.w g (stateProfile D S C z.1) (stateHeight D S C z) r σ :=
    funext fun p => Real.rpow_one _
  have hcF (k : ℕ) : ‖iteratedFDeriv ℝ k c (0, θ)‖ =
      ‖iteratedFDeriv ℝ k (fun p => factoredCharacteristicSpeed D.w g
        (stateProfile D S C z.1) (stateHeight D S C z) r σ p ^ (1 : ℝ)) (0, θ)‖ :=
    (congrArg norm (hlocal k).2).trans
      (congrArg (fun f => ‖iteratedFDeriv ℝ k f (0, θ)‖) hFone).symm
  let Θ₁ := rootFlowParameterUnscale Θ δ
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  exact rootFlow_jet_bound_generic hp (z - (C.referenceState, 0)) hzF hzI
    (le_max_left flowLoss inverseLoss) (le_max_right flowLoss inverseLoss)
    hBD hBC hA hDA hCA hBF hBI hB hBFB hBIB (hfloorD j) (hfloorC j) hWD hWC
    hregular.1 hregular.2 hperiod.1 hperiod.2 hΘ₁
    (fun k => (congrArg norm (hlocal k).1).trans_le ((hjetsD z hz hs hzD m j hhost side θ).2 k))
    (fun k => (hcF k).trans_le
      (hjetsC z hz hs hzC m j hhost hoptical side g hg hfactor R hR hstrip θ k))
    hforward hbackward ht hn

end ContinuousFlexibility.Analysis
