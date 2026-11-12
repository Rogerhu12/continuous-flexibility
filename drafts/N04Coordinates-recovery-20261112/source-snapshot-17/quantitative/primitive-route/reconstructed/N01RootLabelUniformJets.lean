import ContinuousFlexibility.Analysis.N01ReturnUniformPositiveJets
import ContinuousFlexibility.Analysis.N01RootLabels
import Mathlib.Algebra.Field.Periodic

/-!
# Uniform jets of the actual normalized root labels

The actual odd degree-one labels have displacement at most pi. Higher
orders use the genuine left label and stored return inverse, with one
fixed composition loss. All numerical constants precede the component.
The reference return translation never enters a zeroth-order majorant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_rootLabel_displacement_le_pi
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    |n01RootLabel S C z m side θ - θ| ≤ Real.pi := by
  let f : ℝ → ℝ := n01RootLabel S C z m side
  have hder (η : ℝ) : 0 < deriv f η :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (n01RootLabel_deriv_mem_quarter_four hN hflow hz hs m side η).1
  have hmono : Monotone f := (strictMono_of_deriv_pos hder).monotone
  have hlift (η : ℝ) : f (η + Real.pi) = f η + Real.pi :=
    n01RootLabel_period_add hN hz hs m side η
  have hzero : f 0 = 0 := by
    have he : f (-0) = -f 0 := n01RootLabel_odd hN hz hs m side 0
    simp only [neg_zero] at he
    linarith only [he]
  have hperiod : Function.Periodic (fun η => f η - η) Real.pi := by
    intro η
    change f (η + Real.pi) - (η + Real.pi) = f η - η
    rw [hlift η]
    ring
  obtain ⟨η, hη, he⟩ := hperiod.exists_mem_Ico₀ Real.pi_pos θ
  have hpi : f Real.pi = Real.pi := by
    simpa only [zero_add, hzero] using hlift 0
  have hlo : 0 ≤ f η := by simpa only [hzero] using hmono hη.1
  have hhi : f η ≤ Real.pi := by simpa only [hpi] using hmono hη.2.le
  change |f θ - θ| ≤ Real.pi
  rw [he, abs_le]
  constructor <;> linarith only [hη.1, hη.2, hlo, hhi]

theorem n01_rootLabels_displacement_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) :
    ∃ low outLoss : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ m : ℕ, N01RootLabelJetBound S C base low outLoss ε m B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨lowI, lossI, BI, hBI, hinverse⟩ :=
    n01_returnInverse_positiveJets_uniform hS hT hN hflow
  obtain ⟨L, hL, hleft⟩ := n01_stateLeftChart_pairJets hS hT hN
  let inputLoss := max 1 lossI
  obtain ⟨lowC, lossC, htarget⟩ :=
    coordinateComposition_fixed_loss_material_bound (X := ℝ) (Y := ℝ) (Z := ℝ)
      hp hI inputLoss
  let A : ℕ → ℝ := fun k => 1 + L + BI k
  have hA (k : ℕ) : 1 ≤ A k := by
    dsimp only [A]
    linarith only [hL, hBI k]
  obtain ⟨BC, hBC, hcompose⟩ := htarget A hA
  let outLoss := max inputLoss lossC
  let B : ℕ → ℝ := fun n => Real.pi + L + BC (n - 1) + BI n + 2
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith only [Real.pi_pos, hL, hBC (n - 1), hBI n]
  refine ⟨max lowI lowC, outLoss, B, hB, ?_⟩
  intro m z hz hs hlow side n θ
  have hlowI := (hp (le_max_left lowI lowC) _).trans hlow
  have hlowC := (hp (le_max_right lowI lowC) _).trans hlow
  have hgrade (k : ℕ) {j : ℕ} (hj : j ≤ outLoss) :
      1 + pairGrading (stateGrading S) realGrading (k + j) (z - (C.referenceState, 0)) ≤
        1 + pairGrading (stateGrading S) realGrading (k + outLoss)
          (z - (C.referenceState, 0)) :=
    add_le_add_left (hp (Nat.add_le_add_left hj k) _) 1
  by_cases hn0 : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    apply (n01_rootLabel_displacement_le_pi hN hflow hz hs m side θ).trans
    have hpB : Real.pi ≤ B 0 := by
      dsimp only [B]
      linarith only [hL, hBC (0 - 1), hBI 0]
    exact hpB.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (apply_nonneg
          (pairGrading (stateGrading S) realGrading (0 + outLoss)) _)) (hB 0).le)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  cases side with
  | false =>
      have hLB : L ≤ B n := by
        dsimp only [B]
        linarith only [Real.pi_pos, hBC (n - 1), hBI n]
      exact (hleft n m z θ).trans (mul_le_mul hLB
        (hgrade n ((le_max_left 1 lossI).trans (le_max_left inputLoss lossC)))
        (add_nonneg zero_le_one (apply_nonneg _ _)) (hB n).le)
  | true =>
      let l : ℝ → ℝ := stateLeftChart S z.1 m
      let g : ℝ → ℝ := C.minusReturnInverse z m
      let u : ℝ → ℝ := fun η => l η - η
      have hl : ContDiff ℝ ∞ l := contDiff_stateLeftChart hS z.1 m
      have hg : ContDiff ℝ ∞ g := n01_minusReturnInverse_contDiff hS hT hN hz hs m
      have hu : ContDiff ℝ ∞ u := hl.sub contDiff_id
      change ‖iteratedFDeriv ℝ n
        (fun η => oddPart (fun ξ => l (g ξ) - C.travel m) η - η) θ‖ ≤ _
      apply oddPart_lift_displacement_jet_le (hl.comp hg) (T := C.travel m)
      intro η
      have houter (k : ℕ) (_ : 1 ≤ k) : ‖iteratedFDeriv ℝ k u (g η)‖ ≤
          A k * (1 : ℝ) ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
            (k + inputLoss) (z - (C.referenceState, 0))) := by
        simp only [Real.one_rpow, mul_one]
        exact (hleft k m z (g η)).trans (mul_le_mul
          (by dsimp only [A]; linarith only [hBI k])
          (add_le_add_left (hp (Nat.add_le_add_left (le_max_left 1 lossI) k) _) 1)
          (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA k)))
      have hinner (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k g η‖ ≤
          A k * (1 : ℝ) ^ (A k) * (1 + pairGrading (stateGrading S) realGrading
            (k + inputLoss) (z - (C.referenceState, 0))) := by
        simp only [Real.one_rpow, mul_one]
        exact (hinverse z hz hs hlowI m k hk η).trans (mul_le_mul
          (by dsimp only [A]; linarith only [hL])
          (add_le_add_left (hp (Nat.add_le_add_left (le_max_right 1 lossI) k) _) 1)
          (add_nonneg zero_le_one (apply_nonneg _ _)) (zero_le_one.trans (hA k)))
      have hc : ‖iteratedFDeriv ℝ n (u ∘ g) η‖ ≤ BC (n - 1) *
          (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
            (z - (C.referenceState, 0))) := by
        have hb := hcompose (z - (C.referenceState, 0)) hlowC 1 le_rfl
          u g η hu.contDiffAt hg.contDiffAt houter hinner (n - 1)
        simp only [Real.one_rpow, mul_one, Nat.sub_add_cancel hn] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left
          (hgrade n (le_max_right inputLoss lossC)) (hBC (n - 1)).le)
      have hi := (hinverse z hz hs hlowI m n hn η).trans
        (mul_le_mul_of_nonneg_left
          (hgrade n ((le_max_right 1 lossI).trans (le_max_left inputLoss lossC))) (hBI n).le)
      have hid : ‖iteratedFDeriv ℝ n (id : ℝ → ℝ) η‖ ≤ 1 :=
        (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℝ) hn η).trans
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
      have hdisp : ‖iteratedFDeriv ℝ n (g - id) η‖ ≤ BI n *
          (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
            (z - (C.referenceState, 0))) + 1 := by
        rw [iteratedFDeriv_sub_apply
          (hg.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
          (contDiffAt_id.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
        exact (norm_sub_le _ _).trans (add_le_add hi hid)
      have he : (fun ξ => l (g ξ) - ξ) = (u ∘ g) + (g - id) := by
        funext ξ
        simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, id_eq, u]
        ring
      rw [he, iteratedFDeriv_add_apply
        ((hu.comp hg).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
        ((hg.sub contDiff_id).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
      apply (norm_add_le _ _).trans
      apply (add_le_add hc hdisp).trans
      have hw := apply_nonneg (pairGrading (stateGrading S) realGrading
        (n + outLoss)) (z - (C.referenceState, 0))
      have hcoef : BC (n - 1) + BI n + 1 ≤ B n := by
        dsimp only [B]
        linarith only [Real.pi_pos, hL]
      calc
        _ ≤ (BC (n - 1) + BI n + 1) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by nlinarith only [hw]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (add_nonneg zero_le_one hw)

end ContinuousFlexibility.Analysis
