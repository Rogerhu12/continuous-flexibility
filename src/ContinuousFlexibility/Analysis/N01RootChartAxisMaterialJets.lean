import ContinuousFlexibility.Analysis.N01RootOddPowerMaterialJets
import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
import Mathlib.Data.Nat.Choose.Sum

/-!
# Actual root-chart jets without a localization-radius cost

At the root axis the radial coordinate is the product of the vanishing
first projection and the genuine odd-coefficient power. The ordinary
Leibniz inequality costs only a finite binomial sum. The angular lift is
handled through its displacement at positive jet orders, so its
unbounded zero-order angular coordinate is never estimated.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

private theorem rootChart_axis_bound_of_power_prefix
    (n : ℕ) (hn : 1 ≤ n) {G : ℝ × ℝ × ℝ → ℝ} {θ M : ℝ}
    (hM : 1 ≤ M)
    (hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G))
    (hφ : ContDiff ℝ ∞ (extendedRootEven G))
    (hχpos : 0 < extendedRootOddCoefficient G (0, θ))
    (hφjet : ‖iteratedFDeriv ℝ n
      (fun p : PolarPoint => extendedRootEven G p - p.2) (0, θ)‖ ≤ M)
    (hpower : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k
      (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) (0, θ)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)‖ ≤
      (2 + (3 / 2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ n) * M := by
  let Q : ℝ := (3 / 2 : ℝ) ^ (2 / 3 : ℝ)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2) _
  have hp : ContDiffAt ℝ ∞
      (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) (0, θ) :=
    hχ.contDiffAt.rpow_const_of_ne hχpos.ne'
  have hf : ContDiffAt ℝ ∞ (extendedRootRadialFactor G) (0, θ) :=
    (contDiffAt_const.mul hχ.contDiffAt).rpow_const_of_ne
      (mul_ne_zero (by norm_num : (3 / 2 : ℝ) ≠ 0) hχpos.ne')
  have he : extendedRootRadialFactor G =ᶠ[𝓝 (0, θ)]
      (fun p => Q * extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) := by
    filter_upwards [hχ.continuousAt.eventually (Ioi_mem_nhds hχpos)] with p hpos
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hpos.le
  have hfjet (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDeriv ℝ k (extendedRootRadialFactor G) (0, θ)‖ ≤ Q * M := by
    rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
    have hscale := congrArg norm (iteratedFDeriv_const_smul_apply' (a := Q)
      (hp.of_le (by simp : (k : ℕ∞ω) ≤ ∞)))
    have hscale' : ‖iteratedFDeriv ℝ k
        (fun p => Q * extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) (0, θ)‖ =
        Q * ‖iteratedFDeriv ℝ k
          (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) (0, θ)‖ := by
      simpa only [smul_eq_mul, norm_smul, Real.norm_of_nonneg hQ.le] using hscale
    rw [hscale']
    exact mul_le_mul_of_nonneg_left (hpower k hk) hQ.le
  have hfst (k : ℕ) :
      ‖iteratedFDeriv ℝ k (Prod.fst : PolarPoint → ℝ) (0, θ)‖ ≤ 1 := by
    cases k with
    | zero =>
        rw [norm_iteratedFDeriv_zero]
        change ‖(0 : ℝ)‖ ≤ 1
        norm_num
    | succ k => exact
        (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.fst ℝ ℝ ℝ)
          (Nat.succ_pos k) (0, θ)).trans (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ)
  have hrad : ‖iteratedFDeriv ℝ n (extendedRootRadialCoordinate G) (0, θ)‖ ≤
      (2 : ℝ) ^ n * (Q * M) := by
    change ‖iteratedFDeriv ℝ n
      (fun p : PolarPoint => p.1 * extendedRootRadialFactor G p) (0, θ)‖ ≤ _
    apply (norm_iteratedFDeriv_mul_le_at contDiffAt_fst hf n).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Q * M) := by
        apply Finset.sum_le_sum
        intro i hi
        have hc : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hfst i) hc)
          (hfjet (n - i) (Nat.sub_le _ _)) (norm_nonneg _) hc
      _ = (2 : ℝ) ^ n * (Q * M) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hsnd : ‖iteratedFDeriv ℝ n (Prod.snd : PolarPoint → ℝ) (0, θ)‖ ≤ 1 :=
    (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ ℝ ℝ)
      hn (0, θ)).trans (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
  have hdisp : ContDiffAt ℝ ∞
      (fun p : PolarPoint => extendedRootEven G p - p.2) (0, θ) :=
    hφ.contDiffAt.sub contDiffAt_snd
  have hφbound : ‖iteratedFDeriv ℝ n (extendedRootEven G) (0, θ)‖ ≤ 2 * M := by
    have hadd : extendedRootEven G =
        (fun p : PolarPoint => extendedRootEven G p - p.2) + Prod.snd := by
      funext p
      simp only [Pi.add_apply, sub_add_cancel]
    rw [hadd, iteratedFDeriv_add_apply
      (hdisp.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (contDiffAt_snd : ContDiffAt ℝ n (Prod.snd : PolarPoint → ℝ) (0, θ))]
    exact ((norm_add_le _ _).trans (add_le_add hφjet hsnd)).trans
      (by linarith only [hM])
  change ‖iteratedFDeriv ℝ n
    (fun p => (extendedRootRadialCoordinate G p, extendedRootEven G p)) (0, θ)‖ ≤ _
  rw [iteratedFDeriv_prodMk
    ((contDiffAt_fst.mul hf).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hφ.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · apply hrad.trans
    change (2 : ℝ) ^ n * (Q * M) ≤ (2 + Q * (2 : ℝ) ^ n) * M
    have hM0 := zero_le_one.trans hM
    nlinarith only [hM0]
  · apply hφbound.trans
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (mul_nonneg hQ.le (pow_nonneg (by norm_num) n)))
      (zero_le_one.trans hM)

theorem n01_rootChart_unit_positive_material_jets_of_component_optical
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
      ∀ θ : ℝ, ∀ n : ℕ, 1 ≤ n →
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        ‖iteratedFDeriv ℝ n (extendedRootEvenOddChart G) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  classical
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨CE, lowE, lossE, hCE, hfloorE, BE, hBE, heven⟩ :=
    n01_rootEvenOdd_unit_axis_material_jets_of_component_optical hS hT hN hflow hK
  obtain ⟨CP, lowP, lossP, hCP, hfloorP, hpowers⟩ :=
    n01_rootOddCoefficient_unit_rpow_material_jets_of_component_optical hS hT hN hflow hK
  obtain ⟨_, lowPos, _, _, _, _, hvalues⟩ :=
    n01_rootOddCoefficient_unit_material_values_of_component_optical hS hT hN hflow hK
  obtain ⟨BP, hBP, hpower⟩ := hpowers (2 / 3 : ℝ)
  let C0 : ℝ := max CE CP
  have hC0 : 1 ≤ C0 := hCE.trans (le_max_left _ _)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorE j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le)
  let outLoss : ℕ := max lossE lossP
  let A : ℕ → ℝ := fun n => 1 + ∑ k ∈ Finset.range (n + 1), (BE k + BP k)
  have hA (n : ℕ) : 1 ≤ A n := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => add_nonneg (hBE k).le (hBP k).le))
  have hEA (n k : ℕ) (hk : k ≤ n) : BE k ≤ A n :=
    (le_add_of_nonneg_right (hBP k).le).trans
      ((Finset.single_le_sum (fun i _ => add_nonneg (hBE i).le (hBP i).le)
        (Finset.mem_range.mpr (by omega : k < n + 1))).trans
          (le_add_of_nonneg_left zero_le_one))
  have hPA (n k : ℕ) (hk : k ≤ n) : BP k ≤ A n :=
    (le_add_of_nonneg_left (hBE k).le).trans
      ((Finset.single_le_sum (fun i _ => add_nonneg (hBE i).le (hBP i).le)
        (Finset.mem_range.mpr (by omega : k < n + 1))).trans
          (le_add_of_nonneg_left zero_le_one))
  let DC : ℕ → ℝ := fun n => 2 + (3 / 2 : ℝ) ^ (2 / 3 : ℝ) * (2 : ℝ) ^ n
  have hDC (n : ℕ) : 0 < DC n := by
    exact add_pos_of_pos_of_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) n))
  let B : ℕ → ℝ := fun n => 1 + A n + DC n * A n
  have hCA (n : ℕ) : 0 < DC n * A n :=
    mul_pos (hDC n) (zero_lt_one.trans_le (hA n))
  have hB (n : ℕ) : 0 < B n := by dsimp only [B]; linarith only [hA n, hCA n]
  refine ⟨C0, max lowE (max lowP lowPos), outLoss, hC0, hfloor, B, hB, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ n hn
  have hzE := (hp (le_max_left lowE (max lowP lowPos)) _).trans hlow
  have hzP := (hp ((le_max_left lowP lowPos).trans
    (le_max_right lowE (max lowP lowPos))) _).trans hlow
  have hzPos := (hp ((le_max_right lowP lowPos).trans
    (le_max_right lowE (max lowP lowPos))) _).trans hlow
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hWE : CE * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le
  have hWP : CP * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hE j).le
  let P : ℝ := 1 + pairGrading (stateGrading S) realGrading
    (n + outLoss) (z - (C.referenceState, 0))
  have hP : 1 ≤ P := le_add_of_nonneg_right (apply_nonneg _ _)
  let M : ℝ := A n * W ^ (A n) * P
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hA n)
      (Real.one_le_rpow hW (zero_le_one.trans (hA n)))) hP
  have hmono {a V : ℝ} {k l : ℕ} (ha : 0 ≤ a) (haA : a ≤ A n)
      (hV : 1 ≤ V) (hVW : V ≤ W) (hkl : k + l ≤ n + outLoss) :
      a * V ^ a * (1 + pairGrading (stateGrading S) realGrading (k + l)
        (z - (C.referenceState, 0))) ≤ M := by
    apply mul_le_mul
      (mul_le_mul haA
        ((Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
          (Real.rpow_le_rpow_of_exponent_le hW haA))
        (Real.rpow_nonneg (zero_le_one.trans hV) _) (zero_le_one.trans (hA n)))
      (add_le_add_left (hp hkl _) 1)
      (add_nonneg zero_le_one (apply_nonneg _ _))
      (mul_nonneg (zero_le_one.trans (hA n))
        (Real.rpow_nonneg (zero_le_one.trans hW) _))
  let r : ℝ := n01ComponentRoot C m side
  let σ : ℝ := n01ComponentRootOrientation side
  let d : PolarPoint → ℝ := localizedRootDrift D S C r σ hR z
  let c : PolarPoint → ℝ := localizedRootSpeed D S C g r σ hR z
  let Θ₁ : (ℝ × ℝ) → ℝ → ℝ → ℝ := rootFlowParameterUnscale Θ δ
  let l : ℝ → ℝ := n01RootLabel S C z m side
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ₁ l
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hfield := contDiff_rootRegularizedField hregular.1 hregular.2
  have hfieldPeriod := rootRegularizedField_periodic hperiod.1 hperiod.2
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ₁ q.1 1 q.2) :=
    n04Flow_contDiff_slice hfield hfieldPeriod hΘ₁ ht
  have hpositive : ∀ p θ, 0 < deriv (fun η => Θ₁ p 1 η) θ :=
    fun p θ => n04Flow_angular_deriv_pos hfield hfieldPeriod hΘ₁ ht p θ
  have hendpointPeriod : ∀ p θ, Θ₁ p 1 (θ + Real.pi) = Θ₁ p 1 θ + Real.pi :=
    fun p θ => n04Flow_period_add hfield hfieldPeriod hΘ₁ p θ ht
  have hG : ContDiff ℝ ∞ G := contDiff_rootInverseCoordinate Real.pi_ne_zero
    hEndpoint hpositive hendpointPeriod (n01RootLabel_contDiff hS hT hN hz hs m side)
  have hGperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi :=
    rootInverseCoordinate_period_add Real.pi_ne_zero hEndpoint hpositive hendpointPeriod
      (n01RootLabel_period_add hN hz hs m side)
  have hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
    contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero
      (fun x _ => rootOddCoefficient_periodic hGperiod x)
  have hφ : ContDiff ℝ ∞ (extendedRootEven G) :=
    contDiff_extendedRootEven hG Real.pi_ne_zero
      (fun x _ θ => rootEven_period_add hGperiod x θ)
  have hχpos : 0 < extendedRootOddCoefficient G (0, θ) :=
    (hvalues z hz hs hzPos m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ).1
  have hφjet := (heven z hz hs hzE m j hhost hoptical side g hg hfactor R hR hstrip
    δ hδ Θ hΘ θ n).1
  have hφM : ‖iteratedFDeriv ℝ n
      (fun p : PolarPoint => extendedRootEven G p - p.2) (0, θ)‖ ≤ M :=
    hφjet.trans (hmono (hBE n).le (hEA n n le_rfl) (hfloorE j) hWE
      (Nat.add_le_add_left (le_max_left lossE lossP) n))
  have hpM (k : ℕ) (hk : k ≤ n) : ‖iteratedFDeriv ℝ k
      (fun p => extendedRootOddCoefficient G p ^ (2 / 3 : ℝ)) (0, θ)‖ ≤ M :=
    (hpower z hz hs hzP m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ k).trans
      (hmono (hBP k).le (hPA n k hk) (hfloorP j) hWP
        (Nat.add_le_add hk (le_max_right lossE lossP)))
  have hb := rootChart_axis_bound_of_power_prefix n hn hM hχ hφ hχpos hφM hpM
  have hAB : A n ≤ B n := by dsimp only [B]; linarith only [hCA n]
  have hCAB : DC n * A n ≤ B n := by dsimp only [B]; linarith only [hA n]
  apply hb.trans
  calc
    _ = (DC n * A n) * W ^ (A n) * P := by dsimp only [DC, M]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hCAB (Real.rpow_le_rpow_of_exponent_le hW hAB)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (hB n).le)
      (zero_le_one.trans hP)

end ContinuousFlexibility.Analysis
