module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootInversePrefix
public import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelFieldPrefix
public import ContinuousFlexibility.Analysis.N04NegativeChartParameterCompositionBounds
public import ContinuousFlexibility.Analysis.N04NegativeChartDisplacementComposition

/-! The full root displacement uses the supplied inverse and label.
The raw coefficient and label prefixes determine its bounds uniformly
over all representatives. No estimate of a state variation is an input. -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

structure NegativeChartRootCompositionInput (P : Type) [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (N K shift : ℕ) (RH : ℝ)
    extends NegativeChartRootInverseInput P N K shift RH where
  h : P × ℝ → ℝ
  hh : ContDiff ℝ ∞ h
  label_raw : ∀ k, k ≤ N → ∀ v : Fin k → P,
    (∀ a, p₀ (v a) ≤ 1) → (∀ a, p₁ (v a) ≤ R) →
    ∀ j, j ≤ K + N + 1 → ∀ θ,
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootLabelField h) k (0, y.1)
          (fun a => (v a, (0 : PolarPoint))) (1, y.2)) (q.1, θ)‖ ≤
        M * parameterHeightWeight H k * ρ ^ (j - 1 + shift * k)

namespace NegativeChartRootCompositionInput

variable {N K shift : ℕ} {RH : ℝ} (i : NegativeChartRootCompositionInput P N K shift RH)

def fullField : (P × PolarPoint) × PolarPoint → ℝ :=
  fun z => i.h (z.1.1, i.toNegativeChartRootInverseInput.trajectory z) - z.2.2

theorem fullField_smooth : ContDiff ℝ ∞ i.fullField :=
  (i.hh.comp (contDiff_fst.fst.prodMk
    i.toNegativeChartRootInverseInput.trajectory_smooth)).sub contDiff_snd.snd

/-- These are exactly the ordinary parameter jets of the supplied
endpoint, with the original state slots and fixed root coordinates. -/
theorem fullField_parameterJet (k : ℕ) (v : Fin k → P) (q : N04FlowPoint) :
    flowParameterField i.fullField k (0, q.1)
      (fun a => (v a, (0 : PolarPoint))) (1, q.2) =
        iteratedFDeriv ℝ k
          (fun y => i.h (y, i.flow.inverse y q.1 1 q.2) - q.2) 0 v := by
  let f : P × PolarPoint → ℝ := fun z => i.fullField (z, (1, q.2))
  have hf : ContDiff ℝ ∞ f := i.fullField_smooth.comp
    (contDiff_id.prodMk contDiff_const)
  have he := (flowParameterField_eq_joint hf k 0 v q.1).symm
  simpa only [flowParameterField, f, fullField, NegativeChartRootInverseInput.trajectory,
    negativeChartRootPlotTimeChange, compactScalarFlowTime_one] using he

end NegativeChartRootCompositionInput

private theorem positive_fullField_split
    {Θ : (P × PolarPoint) × PolarPoint → ℝ} (hΘ : ContDiff ℝ ∞ Θ)
    {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {n : ℕ} (hn : 0 < n)
    (x : P × PolarPoint) (v : Fin n → P × PolarPoint) (p : PolarPoint) :
    flowParameterField (fun z => h (z.1.1, Θ z) - z.2.2) n x v p =
      flowParameterField (fun z => negativeChartRootLabelField h
        (z.1, (z.2.1, Θ z))) n x v p + flowParameterField Θ n x v p := by
  let f : P × PolarPoint → ℝ := fun y =>
    negativeChartRootLabelField h (y, (p.1, Θ (y, p)))
  let g : P × PolarPoint → ℝ := fun y => Θ (y, p)
  have hg : ContDiff ℝ ∞ g := hΘ.comp (contDiff_id.prodMk contDiff_const)
  have hf : ContDiff ℝ ∞ f :=
    (hh.comp (contDiff_fst.prodMk hg)).sub hg
  have he : (fun y : P × PolarPoint => h (y.1, Θ (y, p)) - p.2) =
      (f + g) - fun _ => p.2 := by funext y; dsimp [f, g, negativeChartRootLabelField]; ring
  unfold flowParameterField
  rw [he, iteratedFDeriv_sub_apply (f := f + g) (g := fun _ => p.2)
    ((hf.add hg).contDiffAt.of_le (by simp)) contDiffAt_const,
    iteratedFDeriv_add_apply (f := f) (g := g) (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  cases n with
  | zero => omega
  | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero,
      ContinuousMultilinearMap.add_apply, f, g]

private theorem displacement_prefix
    {Θ : N04FlowPoint → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (K : ℕ) (q : N04FlowPoint)
    {M B ρ : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (hvalue : |Θ q - q.2| ≤ M)
    (hflow : ∀ j, 1 ≤ j → j ≤ K → ‖iteratedFDeriv ℝ j Θ q‖ ≤ B * ρ ^ (j - 1)) :
    ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y => Θ y - y.2) q‖ ≤
      (M + 2 * B) * ρ ^ (j - 1) := by
  intro j hj
  by_cases hzero : j = 0
  · subst j
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_sub,
      pow_zero, mul_one] using hvalue.trans (le_add_of_nonneg_right (by positivity))
  have hpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hzero
  have hangle : ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => y.2) q‖ ≤ 1 :=
    (flowJet_norm_iteratedFDeriv_clm_le
      (ContinuousLinearMap.snd ℝ PolarPoint ℝ) hpos q).trans
        (ContinuousLinearMap.norm_snd_le ℝ PolarPoint ℝ)
  have hpower : 1 ≤ B * ρ ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hρ)
  change ‖iteratedFDeriv ℝ j (Θ - fun y : N04FlowPoint => y.2) q‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hΘ.contDiffAt.of_le (by simp)) contDiffAt_snd]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j Θ q‖ + ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => y.2) q‖ :=
      norm_sub_le _ _
    _ ≤ B * ρ ^ (j - 1) + B * ρ ^ (j - 1) :=
      add_le_add (hflow j hpos hj) (hangle.trans hpower)
    _ ≤ _ := by nlinarith [pow_nonneg (zero_le_one.trans hρ) (j - 1)]

private theorem graph_prefix
    {Θ : N04FlowPoint → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (K : ℕ) (q : N04FlowPoint)
    {B ρ : ℝ} (hB : 1 ≤ B) (hρ : 1 ≤ ρ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ‖iteratedFDeriv ℝ j Θ q‖ ≤ B * ρ ^ (j - 1)) :
    ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint => (y.1, Θ y)) q‖ ≤ B * ρ ^ (j - 1) := by
  intro j hj hjK
  rw [iteratedFDeriv_prodMk contDiffAt_fst hΘ.contDiffAt (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le _ (hb j hj hjK)
  exact ((flowJet_norm_iteratedFDeriv_clm_le
    (ContinuousLinearMap.fst ℝ PolarPoint ℝ) hj q).trans
      (ContinuousLinearMap.norm_fst_le ℝ PolarPoint ℝ)).trans
        (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hρ))

namespace NegativeChartRootCompositionInput

variable {N K shift : ℕ} {RH : ℝ} (i : NegativeChartRootCompositionInput P N K shift RH)

theorem zero_prefix {B : ℝ} (hB : 1 ≤ B)
    (hflow : ∀ j, 1 ≤ j → j ≤ K →
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        i.toNegativeChartRootInverseInput.trajectory ((0, y.1), (1, y.2))) i.q‖ ≤
          B * i.ρ ^ (j - 1)) :
    ∀ j, j ≤ K → ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      i.fullField ((0, y.1), (1, y.2))) i.q‖ ≤
        ((K.factorial : ℝ) * i.M * B ^ K + i.M + 2 * B) * i.ρ ^ (j - 1) := by
  let Θ : N04FlowPoint → ℝ := fun y =>
    i.toNegativeChartRootInverseInput.trajectory ((0, y.1), (1, y.2))
  have hΘ : ContDiff ℝ ∞ Θ := i.toNegativeChartRootInverseInput.trajectory_smooth.comp
    ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  let g : N04FlowPoint → ℝ := fun y => i.h (0, y.2) - y.2
  have hg : ContDiff ℝ ∞ g := (i.hh.comp (contDiff_const.prodMk contDiff_snd)).sub contDiff_snd
  let Ψ : N04FlowPoint → N04FlowPoint := fun y => (y.1, Θ y)
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_fst.prodMk hΘ
  have houter (j : ℕ) (hj : j ≤ K) :
      ‖iteratedFDeriv ℝ j g (Ψ i.q)‖ ≤ i.M * i.ρ ^ (j - 1) := by
    simpa only [flowParameterField, iteratedFDeriv_zero_apply,
      negativeChartRootLabelField, parameterHeightWeight, ↓reduceIte, mul_one,
      Nat.mul_zero, Nat.add_zero, g, Ψ] using
        i.label_raw 0 (Nat.zero_le N) Fin.elim0 (fun a => a.elim0) (fun a => a.elim0)
          j (by omega) (Θ i.q)
  have hc := n04NegativeChart_displacementComposition_prefix hΨ hg K i.q
    (zero_le_one.trans i.hM) hB i.hρ houter (graph_prefix hΘ K i.q hB i.hρ hflow)
  have hv : |Θ i.q - i.q.2| ≤ i.M := by
    simpa only [Θ, NegativeChartRootInverseInput.trajectory,
      negativeChartRootPlotTimeChange, compactScalarFlowTime_one] using
        i.toNegativeChartRootInverseInput.displacement
  have hd := displacement_prefix hΘ K i.q (zero_le_one.trans i.hM) hB i.hρ hv hflow
  have he : (fun y : N04FlowPoint => i.fullField ((0, y.1), (1, y.2))) =
      (g ∘ Ψ) + fun y => Θ y - y.2 := by
    funext y
    dsimp [fullField, g, Ψ, Θ]
    ring
  intro j hj
  rw [he, iteratedFDeriv_add_apply ((hg.comp hΨ).contDiffAt.of_le (by simp))
    ((hΘ.sub contDiff_snd).contDiffAt.of_le (by simp))]
  exact ((norm_add_le _ _).trans (add_le_add (hc j hj) (hd j hj))).trans_eq (by ring)

end NegativeChartRootCompositionInput

/-- A single state degree precedes every spatial prefix and every
coefficient, label and inverse-flow representative. -/
theorem n04NegativeChart_rootComposition_prefix (N shift : ℕ)
    (RH : ℝ) (hRH : 1 ≤ RH) :
    ∃ D : ℕ, shift + 3 ≤ D ∧ ∀ K : ℕ, ∃ C : ℝ, ∃ e : ℕ, 1 ≤ C ∧
      ∀ i : NegativeChartRootCompositionInput P N K shift RH,
      ∀ k, k ≤ N → ∀ v : Fin k → P,
      (∀ a, i.p₀ (v a) ≤ 1) → (∀ a, i.p₁ (v a) ≤ i.R) →
      ∀ j, j ≤ K →
        ‖iteratedFDeriv ℝ j (fun q : N04FlowPoint =>
          iteratedFDeriv ℝ k
            (fun y => i.h (y, i.flow.inverse y q.1 1 q.2) - q.2) 0 v) i.q‖ ≤
          C * i.M ^ e * parameterHeightWeight i.H k * i.ρ ^ (j - 1 + D * k) := by
  classical
  obtain ⟨Di, hDi, hinverse⟩ :=
    n04NegativeChart_rootInverse_positive_prefix (P := P) N shift RH hRH
  let D₀ := (shift + 1 + Di) * N
  let D := D₀ * (N + 1) + shift + 3
  refine ⟨D, by dsimp only [D]; omega, fun K => ?_⟩
  obtain ⟨Cf, ef, hCf, hfree⟩ :=
    n04NegativeChart_rootInverse_stateFree_prefix (P := P) N K shift RH
  obtain ⟨Ci, ei, hCi, hpositive⟩ := hinverse K
  have hcomp := fun k : Fin N => n04NegativeChart_parameterComposition_positive_prefix
    (E := P × PolarPoint) (Q := N04FlowPoint) (k.val + 1) K (Nat.succ_pos _)
  choose Cc hCc hcomposition using hcomp
  let Cs : ℝ := 4 + ∑ k : Fin N, Cc k
  have hCs : 4 ≤ Cs := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun k _ => zero_le_one.trans (hCc k)))
  let Ch : ℝ := (K.factorial : ℝ) * Cf ^ K
  let eh := ef * K + 1
  have hCh : 1 ≤ Ch := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos K)) (one_le_pow₀ hCf)
  let A : ℝ := 1 + Cf + Ci + Ch
  let e := 1 + ef + ei + eh
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hCf, hCi, hCh]
  have hCfA : Cf ≤ A := by dsimp only [A]; linarith only [hCi, hCh]
  have hCiA : Ci ≤ A := by dsimp only [A]; linarith only [hCf, hCh]
  have hChA : Ch ≤ A := by dsimp only [A]; linarith only [hCf, hCi]
  have hCt : 1 ≤ Cs * (A * RH) ^ (N + 1) :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hCs])
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hA hRH))
  refine ⟨Cs * (A * RH) ^ (N + 1), e * (N + 1), hCt, ?_⟩
  intro i k hkN v hv₀ hv₁ j hj
  let B : ℝ := Cf * i.M ^ ef
  let M : ℝ := A * i.M ^ e
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCf (one_le_pow₀ i.hM)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ i.hM)
  have hBM : B ≤ M := mul_le_mul hCfA (pow_le_pow_right₀ i.hM (by dsimp [e]; omega))
    (pow_nonneg (zero_le_one.trans i.hM) _) (zero_le_one.trans hA)
  have hiM : Ci * i.M ^ ei ≤ M :=
    mul_le_mul hCiA (pow_le_pow_right₀ i.hM (by dsimp [e]; omega))
      (pow_nonneg (zero_le_one.trans i.hM) _) (zero_le_one.trans hA)
  have hhM : Ch * i.M ^ eh ≤ M :=
    mul_le_mul hChA (pow_le_pow_right₀ i.hM (by dsimp [e]; omega))
      (pow_nonneg (zero_le_one.trans i.hM) _) (zero_le_one.trans hA)
  have hmM : i.M ≤ M := (show i.M ≤ i.M ^ e from
    by simpa only [pow_one] using pow_le_pow_right₀ i.hM (show 1 ≤ e by dsimp [e]; omega)).trans
      (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans i.hM) _) hA)
  have hpoly : (K.factorial : ℝ) * i.M * B ^ K = Ch * i.M ^ eh := by
    dsimp only [B, Ch, eh]; rw [mul_pow, ← pow_mul, pow_succ]; ring
  let Z : ℝ := (M * RH) ^ (N + 1)
  have hMZ : M ≤ Z := (le_mul_of_one_le_right (zero_le_one.trans hM) hRH).trans
    (by simpa only [pow_one] using pow_le_pow_right₀
          (one_le_mul_of_one_le_of_one_le hM hRH) (show 1 ≤ N + 1 by omega))
  have hZ : 0 ≤ Z := pow_nonneg
    (mul_nonneg (zero_le_one.trans hM) (zero_le_one.trans hRH)) _
  have hpack : Cs * Z = Cs * (A * RH) ^ (N + 1) * i.M ^ (e * (N + 1)) := by
    dsimp only [Z, M]
    rw [mul_pow, mul_pow, pow_mul]
    ring
  have hfree' (a : ℕ) (ha : 1 ≤ a) (haK : a ≤ K) :
      ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint =>
        i.toNegativeChartRootInverseInput.trajectory ((0, y.1), (1, y.2))) i.q‖ ≤
          B * i.ρ ^ (a - 1) :=
    hfree i.toNegativeChartRootInverseInput a ha haK 1 ⟨zero_le_one, le_rfl⟩
  rw [← funext (i.fullField_parameterJet k v)]
  by_cases hk : k = 0
  · subst k
    have hz := i.zero_prefix hB hfree' j hj
    have ham : (K.factorial : ℝ) * i.M * B ^ K + i.M + 2 * B ≤ Cs * Z := by
      rw [hpoly]
      nlinarith only [hhM, hmM, hBM, hMZ, hCs, hZ]
    have hz' := hz.trans (mul_le_mul_of_nonneg_right ham
      (pow_nonneg (zero_le_one.trans i.hρ) _))
    simpa only [flowParameterField, iteratedFDeriv_zero_apply, parameterHeightWeight,
      ↓reduceIte, Nat.mul_zero, Nat.add_zero, mul_one, hpack] using hz'
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let G := negativeChartRootLabelField i.h
  let Θ := i.toNegativeChartRootInverseInput.trajectory
  have hG : ContDiff ℝ ∞ G := negativeChartRootLabelField_contDiff i.hh
  have hΘ : ContDiff ℝ ∞ Θ := i.toNegativeChartRootInverseInput.trajectory_smooth
  let J := continuousTimeSpeedTowerOfContDiff hG
  have hκ : ∀ a, a ≤ K → ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint =>
      flowVariationCoefficient G Θ (0, y.1) (1, y.2)) i.q‖ ≤ M * i.ρ ^ a := by
    let F : ℝ × N04FlowPoint → ℝ := fun z => G ((0, z.2.1), (z.1, z.2.2))
    have hF : ContDiff ℝ ∞ F := hG.comp
      ((contDiff_const.prodMk contDiff_snd.fst).prodMk (contDiff_fst.prodMk contDiff_snd.snd))
    have ht : ContDiff ℝ ∞ (fun y : N04FlowPoint => Θ ((0, y.1), (1, y.2))) :=
      hΘ.comp ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
    have hr (a : ℕ) (ha : a ≤ K) (θ : ℝ) :
        ‖iteratedFDeriv ℝ (a + 1) (fun y => F (1, y)) (i.q.1, θ)‖ ≤ i.M * i.ρ ^ a := by
      simpa only [flowParameterField, iteratedFDeriv_zero_apply, parameterHeightWeight,
        ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.add_sub_cancel, mul_one] using
          i.label_raw 0 (Nat.zero_le N) Fin.elim0 (fun b => b.elim0) (fun b => b.elim0)
            (a + 1) (by omega) θ
    have he : (fun y : N04FlowPoint => flowVariationCoefficient G Θ (0, y.1) (1, y.2)) =
        fun y => deriv (fun θ => F (1, (y.1, θ))) (Θ ((0, y.1), (1, y.2))) :=
      funext (fun y => flowVariationCoefficient_eq_deriv hG (0, y.1) (1, y.2))
    rw [he]
    intro a ha
    have hb := n04NegativeChart_angleComposition_point_prefix hF ht K 1 i.q
      (zero_le_one.trans i.hM) hB i.hρ hr hfree' a ha
    exact hb.trans (mul_le_mul_of_nonneg_right (hpoly.trans_le hhM)
      (pow_nonneg (zero_le_one.trans i.hρ) _))
  have hhead : ∀ d : FlowForcingChoice k, ∀ a, a ≤ K →
      ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint => canonicalFlowForcingFactors J hΘ
        (0, y.1) (fun b => (v b, (0 : PolarPoint))) 1 d 0 y.2) i.q‖ ≤
          parameterHeightWeight i.H d.2.card * M * i.ρ ^ (D₀ + a) := by
    intro d a ha
    have hb := negativeChart_actual_forcing_head_prefix hG J hΘ k K shift v i.p₀ i.p₁
      i.hR (zero_le_one.trans i.hM) hB i.hH i.hρ hv₀ hv₁ 1 i.q
      (fun b hb u hu₀ hu₁ l hl θ => i.label_raw b (hb.trans hkN) u hu₀ hu₁ l (by omega) θ)
      hfree' d a ha
    have hd : (shift + 1) * k ≤ D₀ :=
      (Nat.mul_le_mul_left _ hkN).trans (Nat.mul_le_mul_right N (by omega))
    apply hb.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hpoly.trans_le hhM)
      (parameterHeightWeight_nonneg i.hH _))
      (pow_le_pow_right₀ i.hρ (Nat.add_le_add_right hd a))
      (pow_nonneg (zero_le_one.trans i.hρ) _)
      (mul_nonneg (parameterHeightWeight_nonneg i.hH _) (zero_le_one.trans hM))
  have hlower : ∀ b, 0 < b → b ≤ k → ∀ f : Fin b → Fin k, ∀ a, a ≤ K →
      ‖iteratedFDeriv ℝ a (fun y : N04FlowPoint => flowParameterField Θ b (0, y.1)
        ((fun c => (v c, (0 : PolarPoint))) ∘ f) (1, y.2)) i.q‖ ≤
          i.H * M * i.ρ ^ (D₀ + a) := by
    intro b hb hbk f a ha
    have hp := hpositive i.toNegativeChartRootInverseInput b hb (hbk.trans hkN) (v ∘ f)
      (fun c => hv₀ (f c)) (fun c => hv₁ (f c)) a ha
    rw [← i.flow.inverse_endpoint_spatialJet b a (v ∘ f) i.q] at hp
    have hd : Di * b ≤ D₀ :=
      (Nat.mul_le_mul_left _ (hbk.trans hkN)).trans
        (Nat.mul_le_mul_right N (by omega))
    apply hp.trans
    have hm : Ci * i.H * i.M ^ ei ≤ i.H * M := by nlinarith only [hiM, i.hH]
    exact mul_le_mul hm (pow_le_pow_right₀ i.hρ (by omega))
      (pow_nonneg (zero_le_one.trans i.hρ) _)
      (mul_nonneg i.hH (zero_le_one.trans hM))
  let a : Fin N := ⟨k - 1, by omega⟩
  have hca : Cc a + 1 ≤ Cs := by
    have hc := Finset.single_le_sum
      (fun b (_ : b ∈ (Finset.univ : Finset (Fin N))) => zero_le_one.trans (hCc b))
      (Finset.mem_univ a)
    dsimp only [Cs]
    linarith only [hc]
  have hc := hcomposition a hG J hΘ
    (fun y : N04FlowPoint => ((0 : P), y.1)) (fun y => y.2)
    (contDiff_const.prodMk contDiff_fst) contDiff_snd
  have hka : a.val + 1 = k := by dsimp only [a]; omega
  rw [hka] at hc
  have hb := hc (fun b => (v b, (0 : PolarPoint))) 1 i.q D₀ i.hH i.hHR hM hRH i.hρ
    hκ hhead hlower j hj
  have hi := hlower k hkpos le_rfl id j hj
  have hd : D₀ * (k + 1) + j ≤ j - 1 + D * k := by
    have h₁ := Nat.mul_le_mul_left D₀ (show k + 1 ≤ N + 1 by omega)
    have h₂ := Nat.mul_le_mul_left D hkpos
    simp only [Nat.mul_one] at h₂
    change D₀ * (N + 1) + shift + 3 ≤ D * k at h₂
    omega
  have hd' : D₀ + j ≤ j - 1 + D * k := by
    have hh := Nat.mul_le_mul_left D₀ (show 1 ≤ k + 1 by omega)
    simp only [Nat.mul_one] at hh
    omega
  have hp : (M * RH) ^ (k + 1) ≤ Z :=
    pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hM hRH) (by omega)
  have hb' := hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hp (mul_nonneg (zero_le_one.trans (hCc a)) i.hH))
    (pow_le_pow_right₀ i.hρ hd) (pow_nonneg (zero_le_one.trans i.hρ) _)
    (mul_nonneg (mul_nonneg (zero_le_one.trans (hCc a)) i.hH) hZ))
  have hi' := hi.trans (mul_le_mul (mul_le_mul_of_nonneg_left hMZ i.hH)
    (pow_le_pow_right₀ i.hρ hd') (pow_nonneg (zero_le_one.trans i.hρ) _)
    (mul_nonneg i.hH hZ))
  have hs : (fun y : N04FlowPoint => flowParameterField i.fullField k (0, y.1)
      (fun b => (v b, (0 : PolarPoint))) (1, y.2)) =
      (fun y => flowParameterField (fun z => G (z.1, (z.2.1, Θ z))) k (0, y.1)
        (fun b => (v b, (0 : PolarPoint))) (1, y.2)) +
      fun y => flowParameterField Θ k (0, y.1)
        (fun b => (v b, (0 : PolarPoint))) (1, y.2) :=
    funext (fun y => positive_fullField_split hΘ i.hh hkpos (0, y.1) _ (1, y.2))
  have hgs : ContDiff ℝ ∞ (fun z => G (z.1, (z.2.1, Θ z))) :=
    hG.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk hΘ))
  have hslice (F : (P × PolarPoint) × PolarPoint → ℝ) (hF : ContDiff ℝ ∞ F) :
      ContDiff ℝ ∞ (fun y : N04FlowPoint => flowParameterField F k (0, y.1)
        (fun b => (v b, (0 : PolarPoint))) (1, y.2)) :=
    (n04NegativeChart_flowParameterField_joint_contDiff hF k _).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk (contDiff_const.prodMk contDiff_snd))
  rw [hs, iteratedFDeriv_add_apply ((hslice _ hgs).contDiffAt.of_le (by simp))
    ((hslice Θ hΘ).contDiffAt.of_le (by simp))]
  have hf := ((norm_add_le _ _).trans (add_le_add hb' hi')).trans_eq
    (show Cc a * i.H * Z * i.ρ ^ (j - 1 + D * k) +
      i.H * Z * i.ρ ^ (j - 1 + D * k) =
      (Cc a + 1) * Z * i.H * i.ρ ^ (j - 1 + D * k) by ring)
  have hf' := hf.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hca hZ) i.hH)
    (pow_nonneg (zero_le_one.trans i.hρ) _))
  simpa only [parameterHeightWeight, if_neg hk, hpack, Function.comp_id] using hf'

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootComposition_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootComposition_prefix
