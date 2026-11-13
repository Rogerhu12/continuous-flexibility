import ContinuousFlexibility.Analysis.N01ReturnInverseJets
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# Uniform positive angular jets of the actual return maps

The positive material height power absorbs the coefficient factor in
the genuine closed-time N01 estimate, uniformly over the actual cells.
The reference return is a translation, so its higher angular jets vanish.
Only positive inverse jets are estimated; no bound on the reference
translation or on an arbitrarily chosen component constant is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n01_returnForward_higherJets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ A : ℕ → ℝ, (∀ n, 1 ≤ A n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m n : ℕ, 2 ≤ n → ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n (C.minusFlow z m (C.right m)) θ‖ ≤
          A n * (1 + pairGrading (stateGrading S) realGrading
            (n + (base + loss)) (z - (C.referenceState, 0))) := by
  choose B hB hclosed using
    fun n => ordinaryFlowFamily_le_linear_high_on_closed_of_n01 hS hT hN n
  choose K hK hweight using fun n =>
    material_sample_height_coefficient_power_bounded hN.1.1 hT C.cell (B n)
      (by norm_num : (0 : ℝ) < 3 / 4)
  have hε : 0 < 2 + 2 * ε := by linarith only [hN.2.1]
  let A : ℕ → ℝ := fun n => 1 + B n * K n * (2 + 2 * ε)
  have hA (n : ℕ) : 1 ≤ A n :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (hB n).le (hK n).le) hε.le)
  refine ⟨A, hA, ?_⟩
  intro z hz hs m n hn θ
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  let f₀ : ℝ → ℝ := C.minusFlow (C.referenceState, 0) m (C.right m)
  let c : ℝ := f₀ 0
  have href : f₀ = fun η => c + η := funext
    (ordinaryFlow_zeroParameter_eq_zeroAngle_add hN.2.2.2.2.2.2.1
      (reference_mem_stateNeighborhood S C base hN.2.1) m hr)
  have hf₀ : ContDiff ℝ ∞ f₀ := by
    rw [href]
    exact contDiff_const.add contDiff_id
  have hf := (n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr
  have hzero : iteratedDeriv n f₀ θ = 0 := by
    rw [href, iteratedDeriv_const_add (by omega : 0 < n) c]
    simp only [iteratedDeriv_id, iteratedDeriv_fun_id,
      if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ 1)]
  have he : iteratedDeriv n (fun η => C.minusFlow z m (C.right m) η - f₀ η) θ =
      iteratedDeriv n (C.minusFlow z m (C.right m)) θ := by
    simpa only [hzero, sub_zero] using iteratedDeriv_fun_sub (n := n) (x := θ)
      (hf.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (hf₀.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
  have hdiff := hclosed n m n (C.right m, θ) le_rfl hr z hz hs
  have hweight' :
      B n * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B n ≤ B n * K n := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hweight n m) (hB n).le
  have hdiff' :
      |iteratedDeriv n (fun η => C.minusFlow z m (C.right m) η - f₀ η) θ| ≤
        (B n * K n * (2 + 2 * ε)) * pairGrading (stateGrading S) realGrading
          (max base (n + loss)) (z - (C.referenceState, 0)) :=
    hdiff.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hweight' hε.le) (apply_nonneg _ _))
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have horder : max base (n + loss) ≤ n + (base + loss) := by omega
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, ← he]
  apply hdiff'.trans
  apply mul_le_mul (le_add_of_nonneg_left zero_le_one)
    (((hp horder) _).trans (le_add_of_nonneg_left zero_le_one))
    (apply_nonneg _ _)
  exact zero_le_one.trans (hA n)

theorem n01_returnInverse_positiveJets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m n : ℕ, 1 ≤ n → ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n (C.minusReturnInverse z m) θ‖ ≤
          B n * (1 + pairGrading (stateGrading S) realGrading
            (n + outLoss) (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨A, hA, hforward⟩ := n01_returnForward_higherJets_uniform hS hT hN
  obtain ⟨low, outLoss, htarget⟩ :=
    nonlinearInverse_positiveJets_le_material hp hI (base + loss)
  let Q : ℕ → ℝ := fun j => 2 + A (j + 1)
  have hQ (j : ℕ) : 1 ≤ Q j := by
    dsimp only [Q]
    linarith only [hA (j + 1)]
  obtain ⟨B, hB, hbound⟩ := htarget Q hQ
  refine ⟨low, outLoss, B, hB, ?_⟩
  intro z hz hs hlow m n hn θ
  let f : ℝ → ℝ := C.minusFlow z m (C.right m)
  let g : ℝ → ℝ := C.minusReturnInverse z m
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩
  have hf : ContDiff ℝ ∞ f :=
    (n01_ordinaryFlow_angularRegularity hS hT hN hz hs m).1 _ hr
  have hg : ContDiff ℝ ∞ g := n01_minusReturnInverse_contDiff hS hT hN hz hs m
  have hright (η : ℝ) : f (g η) = η :=
    (hN.2.2.2.2.2.2.2.2.1 z hz hs m η).1
  have hleft (η : ℝ) : g (f η) = η :=
    (hN.2.2.2.2.2.2.2.2.1 z hz hs m η).2.1
  have hfg : f ∘ g =ᶠ[𝓝 θ] (id : ℝ → ℝ) := Eventually.of_forall hright
  have hL : (fderiv ℝ g θ).comp (fderiv ℝ f (g θ)) =
      ContinuousLinearMap.id ℝ ℝ := by
    have he : g ∘ f = id := funext hleft
    calc
      _ = (fderiv ℝ g (f (g θ))).comp (fderiv ℝ f (g θ)) := by rw [hright θ]
      _ = fderiv ℝ (g ∘ f) (g θ) :=
        (fderiv_comp (g θ) (hg.differentiable (by simp) _)
          (hf.differentiable (by simp) _)).symm
      _ = _ := by rw [he, fderiv_id]
  have hfirst : ‖fderiv ℝ g θ‖ ≤ 2 := by
    have hJ := (canonicalReturnJacobianBounds_of_n01 hN hflow z hz hs m θ).1
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_one, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [hJ.1], hJ.2⟩
  have hfirst' : ‖fderiv ℝ g θ‖ ≤ Q 0 * (1 : ℝ) ^ (Q 0) *
      (1 + pairGrading (stateGrading S) realGrading (base + loss + 1)
        (z - (C.referenceState, 0))) := by
    simp only [Real.one_rpow, mul_one, Q, Nat.zero_add]
    nlinarith only [hfirst, hA 1, apply_nonneg
      (pairGrading (stateGrading S) realGrading (base + loss + 1))
        (z - (C.referenceState, 0))]
  have hraw (j : ℕ) (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) f (g θ)‖ ≤ Q j * (1 : ℝ) ^ (Q j) *
        (1 + pairGrading (stateGrading S) realGrading (j + (base + loss) + 1)
          (z - (C.referenceState, 0))) := by
    have hb := hforward z hz hs m (j + 1) (by omega) (g θ)
    have horder : (j + 1) + (base + loss) = j + (base + loss) + 1 := by omega
    rw [horder] at hb
    simp only [Real.one_rpow, mul_one, Q]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
      (add_nonneg zero_le_one (apply_nonneg _ _)))
  simpa only [Real.one_rpow, mul_one] using
    hbound (z - (C.referenceState, 0)) hlow 1 le_rfl ℝ ℝ f g θ
      hf.contDiffAt hg.contDiffAt hfg (fderiv ℝ g θ) hL hfirst' hraw n hn

end ContinuousFlexibility.Analysis
