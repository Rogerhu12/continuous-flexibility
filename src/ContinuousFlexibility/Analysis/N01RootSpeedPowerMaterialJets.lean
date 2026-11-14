import ContinuousFlexibility.Analysis.N01RootFactorPowerMaterialJets
import ContinuousFlexibility.Analysis.N01RootDriftAxisMaterialJets
import ContinuousFlexibility.Analysis.PointwiseProductPolynomialMaterialJets

/-!
# Actual root speed powers with uniform material costs

On the genuine positive germ, c^gamma = G^(gamma/2) a^(-gamma).
The two already derived material towers are combined at the same root.
The radial coefficient is pulled back only by a translation and the
inward sign, whose linear part has norm one. No model radius or flow
normalization enters the bound. The raw optical lower is still explicit.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem rootSpeed_rpow_factorization
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (γ : ℝ) :
    c ^ γ = (a ^ 2 * c ^ 2) ^ (γ / 2) * a ^ (-γ) := by
  rw [Real.mul_rpow (sq_nonneg a) (sq_nonneg c),
    ← Real.rpow_natCast_mul ha.le 2 (γ / 2),
    ← Real.rpow_natCast_mul hc.le 2 (γ / 2)]
  have htwo : ((2 : ℕ) : ℝ) * (γ / 2) = γ := by push_cast; ring
  rw [htwo]
  calc
    c ^ γ = (a ^ γ * a ^ (-γ)) * c ^ γ := by
      rw [← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero, one_mul]
    _ = a ^ γ * c ^ γ * a ^ (-γ) := by ring

private theorem rootSpeed_material_envelope_mono
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

/-- The pointwise product estimate for an arbitrary graded state space. All
grading manipulations happen here, away from the actual state spaces. -/
private theorem rootSpeed_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E)
    {lossG lossA outLoss productLow : ℕ} (hx : p productLow x ≤ 1)
    {BG BA M B : ℕ → ℝ} (hBG : ∀ k, 0 < BG k) (hBA : ∀ k, 0 < BA k)
    (hM : ∀ k, 1 ≤ M k) (hGM : ∀ k, BG k ≤ M k) (hAM : ∀ k, BA k ≤ M k)
    {VG VA W : ℝ} (hVG : 1 ≤ VG) (hVA : 1 ≤ VA) (hVGW : VG ≤ W) (hVAW : VA ≤ W)
    {u v F : PolarPoint → ℝ} {q : PolarPoint}
    (hu : ContDiffAt ℝ ∞ u q) (hv : ContDiffAt ℝ ∞ v q)
    (hF : F =ᶠ[𝓝 q] fun y => u y * v y)
    (hju : ∀ k, ‖iteratedFDeriv ℝ k u q‖ ≤ BG k * VG ^ (BG k) * (1 + p (k + lossG) x))
    (hjv : ∀ k, ‖iteratedFDeriv ℝ k v q‖ ≤ BA k * VA ^ (BA k) * (1 + p (k + lossA) x))
    (hbound : ∀ z : E, p productLow z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ f g : PolarPoint → ℝ, ∀ y : PolarPoint,
        ContDiffAt ℝ ∞ f y → ContDiffAt ℝ ∞ g y →
        (∀ n, ‖iteratedFDeriv ℝ n f y‖ ≤
          M n * W ^ (M n) * (1 + p (n + max lossG lossA) z)) →
        (∀ n, ‖iteratedFDeriv ℝ n g y‖ ≤
          M n * W ^ (M n) * (1 + p (n + max lossG lossA) z)) →
        ∀ n, ‖iteratedFDeriv ℝ n (fun y => f y * g y) y‖ ≤
          B n * W ^ (B n) * (1 + p (n + outLoss) z))
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n F q‖ ≤ B n * W ^ (B n) * (1 + p (n + outLoss) x) := by
  rw [(hF.iteratedFDeriv ℝ n).self_of_nhds]
  refine hbound x hx W (hVG.trans hVGW) u v q hu hv ?_ ?_ n
  · intro k
    exact (hju k).trans (rootSpeed_material_envelope_mono hp (hBG k).le
      (hGM k) (zero_le_one.trans (hM k)) hVG hVGW (le_max_left lossG lossA) x)
  · intro k
    exact (hjv k).trans (rootSpeed_material_envelope_mono hp (hBA k).le
      (hAM k) (zero_le_one.trans (hM k)) hVA hVAW (le_max_right lossG lossA) x)

theorem n01_rootSpeed_axis_rpow_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ t, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * t) = t * g t) →
      ∀ R : ℝ, 0 < R →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R → ∀ θ : ℝ, ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n
          (fun p => factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) (n01ComponentRoot C m side)
            (n01ComponentRootOrientation side) p ^ γ) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  refine (n01_rootFactor_axis_rpow_material_jets_of_component_optical hS hT hN hK).elim ?_
  intro CG hG1
  refine hG1.elim ?_
  intro lowG hG2
  refine hG2.elim ?_
  intro lossG hG3
  have hCG := hG3.1
  have hfloorG := hG3.2.1
  have hpowersG := hG3.2.2
  refine (n01_radialCoefficient_rpow_component_material_jets hS hT hN).elim ?_
  intro CA hA1
  refine hA1.elim ?_
  intro lowA hA2
  refine hA2.elim ?_
  intro lossA hA3
  have hfloorA := hA3.2.1
  have hpowersA := hA3.2.2
  let C0 := max CG CA
  have hC0 : 1 ≤ C0 := hCG.trans (le_max_left _ _)
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorG j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ((hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1.le))
  refine (pointwiseProduct_polynomial_material_bound (X := PolarPoint) hp hI
    (max lossG lossA)).elim ?_
  intro productLow hP1
  refine hP1.elim ?_
  intro outLoss hproduct
  refine ⟨C0, max lowG (max lowA productLow), outLoss, hC0, hsample, ?_⟩
  intro γ
  refine (hpowersG (γ / 2)).elim ?_
  intro BG hBGj
  have hBG := hBGj.1
  have hjetsG := hBGj.2
  refine (hpowersA (-γ)).elim ?_
  intro BA hBAj
  have hBA := hBAj.1
  have hjetsA := hBAj.2
  let M : ℕ → ℝ := fun n => max 1 (max (BG n) (BA n))
  have hM (n : ℕ) : 1 ≤ M n := le_max_left _ _
  have hGM (n : ℕ) : BG n ≤ M n := (le_max_left _ _).trans (le_max_right _ _)
  have hAM (n : ℕ) : BA n ≤ M n := (le_max_right _ _).trans (le_max_right _ _)
  refine (hproduct M hM).elim ?_
  intro B hBb
  have hB := hBb.1
  have hbound := hBb.2
  refine ⟨B, hB, ?_⟩
  intro z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip θ n
  have hzG := (hp (le_max_left lowG (max lowA productLow)) _).trans hzlow
  have hzA := (hp ((le_max_left lowA productLow).trans
    (le_max_right lowG (max lowA productLow))) _).trans hzlow
  have hzP := (hp ((le_max_right lowA productLow).trans
    (le_max_right lowG (max lowA productLow))) _).trans hzlow
  let W := C0 * T.E0 (T.sample j)
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hWG : CG * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
  have hWA : CA * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let a : PolarPoint → ℝ := fun p => (originalCoefficients D S C z).a (rootProfileShift r σ p)
  let c := factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  let G := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
  have hpoint : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  have hroot := n01_component_root_data hN m side
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hrcc : r ∈ Icc (C.left m) (C.right m) := by
    cases side <;>
      simp only [r, n01ComponentRoot, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
    · exact ⟨le_rfl, hcomp.2.1.le⟩
    · exact ⟨hcomp.2.1.le, le_rfl⟩
  have hq : (r, θ) ∈ annularOpen D := ⟨hroot.1, mem_univ _⟩
  have hapos : 0 < (originalCoefficients D S C z).a (r, θ) :=
    (div_pos (hN.1.1.choose_spec.1.2.2.2.2.1 r hroot.1)
      (by norm_num : (0 : ℝ) < 16)).trans_le
        (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hq)
  have ha0 : 0 < a (0, θ) := by simpa only [a, hpoint] using hapos
  have hcomp0 : canonicalCoefficientComponent 0 (originalCoefficients D S C z) =
      (originalCoefficients D S C z).a := by
    unfold canonicalCoefficientComponent
    exact if_pos rfl
  have haPhysical : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a (r, θ) := by
    rw [← hcomp0]
    exact (contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (0 : Fin 3)).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)
  have haPhysical' : ContDiffAt ℝ ∞ (originalCoefficients D S C z).a
      (rootProfileShift r σ (0, θ)) := by rw [hpoint]; exact haPhysical
  have haPhysicalPos : 0 < (originalCoefficients D S C z).a
      (rootProfileShift r σ (0, θ)) := by rw [hpoint]; exact hapos
  have hshift : ContDiff ℝ ∞ (rootProfileShift r σ) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have ha : ContDiffAt ℝ ∞ a (0, θ) := by
    simpa only [a, Function.comp_def] using
      haPhysical'.comp (0, θ) hshift.contDiffAt
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hc : ContDiffAt ℝ ∞ c (0, θ) :=
    (contDiffAt_factoredCharacteristicField hN.1.1.choose_spec.1.2.2.1.1 hg
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z)
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1).1
  have hc0 : 0 < c (0, θ) := factoredCharacteristicSpeed_pos
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  have hGformula (p : PolarPoint) : G p = a p ^ 2 * c p ^ 2 := rfl
  have hG : ContDiffAt ℝ ∞ G (0, θ) := (ha.pow 2).mul (hc.pow 2)
  have hG0 : 0 < G (0, θ) := mul_pos (pow_pos ha0 2) (pow_pos hc0 2)
  have heq : (fun p => c p ^ γ) =ᶠ[𝓝 (0, θ)]
      (fun p => G p ^ (γ / 2) * a p ^ (-γ)) := by
    filter_upwards [ha.continuousAt.eventually (eventually_gt_nhds ha0),
      hc.continuousAt.eventually (eventually_gt_nhds hc0)] with p hap hcp
    rw [hGformula]
    exact rootSpeed_rpow_factorization hap hcp γ
  have hjetA (k : ℕ) : ‖iteratedFDeriv ℝ k (fun p => a p ^ (-γ)) (0, θ)‖ ≤
      BA k * (CA * T.E0 (T.sample j)) ^ (BA k) *
        (1 + pairGrading (stateGrading S) realGrading (k + lossA)
          (z - (C.referenceState, 0))) := by
    have hpow : ContDiffAt ℝ ∞
        (fun p => (originalCoefficients D S C z).a p ^ (-γ))
        (rootProfileShift r σ (0, θ)) :=
      haPhysical'.rpow_const_of_ne haPhysicalPos.ne'
    have hb := norm_iteratedFDeriv_rootProfileShift_le
      (r := r) (σ := σ) (x := (0, θ)) (n01ComponentRootOrientation_eq side) hpow k
    rw [hpoint] at hb
    exact hb.trans (hjetsA z hz hs hzA m j hhost (r, θ) hrcc k)
  exact rootSpeed_jet_bound_generic hp (z - (C.referenceState, 0)) hzP hBG hBA hM hGM hAM
    (hfloorG j) (hfloorA j) hWG hWA (hG.rpow_const_of_ne hG0.ne')
    (ha.rpow_const_of_ne ha0.ne') heq
    (fun k => hjetsG z hz hs hzG m j hhost hoptical side g hg hfactor R hR hstrip θ k)
    hjetA hbound n

end ContinuousFlexibility.Analysis
