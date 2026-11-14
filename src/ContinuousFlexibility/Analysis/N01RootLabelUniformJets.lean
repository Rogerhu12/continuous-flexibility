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

private theorem rootLabel_zero_jet_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) {B t : ℝ}
    (hB : Real.pi ≤ B) (ht : 0 ≤ t) :
    ‖iteratedFDeriv ℝ 0 (fun η => n01RootLabel S C z m side η - η) θ‖ ≤ B * (1 + t) := by
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have h := n01_rootLabel_displacement_le_pi hN hflow hz hs m side θ
  have hBt := mul_nonneg (Real.pi_pos.le.trans hB) ht
  nlinarith only [h, hB, hBt]

/-- Real bookkeeping for a label equal to a displaced chart with a known bound. -/
private theorem label_jet_le_of_eq {h l : ℝ → ℝ} (hhl : ∀ η, h η = l η) {n : ℕ}
    {θ L B s t : ℝ}
    (hy : ‖iteratedFDeriv ℝ n (fun η => l η - η) θ‖ ≤ L * (1 + s)) (hLB : L ≤ B)
    (hst : s ≤ t) (hs : 0 ≤ s) (hB : 0 ≤ B) :
    ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤ B * (1 + t) := by
  have hfun : (fun η => h η - η) = (fun η => l η - η) := funext fun η => by rw [hhl η]
  rw [hfun]
  exact hy.trans (mul_le_mul hLB (add_le_add le_rfl hst) (add_nonneg zero_le_one hs) hB)

/-- The right label, for an arbitrary graded state space. All grading
manipulations happen here, away from the actual state spaces. -/
private theorem rightLabel_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E)
    {l g h : ℝ → ℝ} (hl : ContDiff ℝ ∞ l) (hg : ContDiff ℝ ∞ g) (T : ℝ)
    (hh : ∀ η, h η = oddPart (fun ξ => l (g ξ) - T) η)
    {L : ℝ} {A BI BC : ℕ → ℝ} {inputLoss lossI lossC outLoss n : ℕ}
    (hA : ∀ k, 1 ≤ A k) (hLA : ∀ k, L ≤ A k) (hBIA : ∀ k, BI k ≤ A k)
    (hBI : ∀ k, 0 < BI k) (hBC : ∀ k, 0 < BC k)
    (hIin : lossI ≤ inputLoss) (h1in : 1 ≤ inputLoss)
    (hinout : inputLoss ≤ outLoss) (hCout : lossC ≤ outLoss) (hn : 1 ≤ n)
    (hleft : ∀ k η, ‖iteratedFDeriv ℝ k (fun η => l η - η) η‖ ≤ L * (1 + p (k + 1) x))
    (hinv : ∀ k, 1 ≤ k → ∀ η, ‖iteratedFDeriv ℝ k g η‖ ≤ BI k * (1 + p (k + lossI) x))
    (hcomp : ∀ (f k : ℝ → ℝ) (η : ℝ), ContDiffAt ℝ ∞ f (k η) → ContDiffAt ℝ ∞ k η →
      (∀ j : ℕ, 1 ≤ j → ‖iteratedFDeriv ℝ j f (k η)‖ ≤
        A j * (1 : ℝ) ^ (A j) * (1 + p (j + inputLoss) x)) →
      (∀ j : ℕ, 1 ≤ j → ‖iteratedFDeriv ℝ j k η‖ ≤
        A j * (1 : ℝ) ^ (A j) * (1 + p (j + inputLoss) x)) →
      ∀ j : ℕ, ‖iteratedFDeriv ℝ (j + 1) (f ∘ k) η‖ ≤
        BC j * (1 : ℝ) ^ (BC j) * (1 + p ((j + 1) + lossC) x))
    {B : ℝ} (hB : BC (n - 1) + BI n + 1 ≤ B) (θ : ℝ) :
    ‖iteratedFDeriv ℝ n (fun η => h η - η) θ‖ ≤ B * (1 + p (n + outLoss) x) := by
  have hfun : (fun η => h η - η) = (fun η => oddPart (fun ξ => (l ∘ g) ξ - T) η - η) :=
    funext fun η => by rw [hh η]; rfl
  rw [hfun]
  apply oddPart_lift_displacement_jet_le (hl.comp hg) (T := T)
  intro η
  let u : ℝ → ℝ := fun η => l η - η
  have hu : ContDiff ℝ ∞ u := hl.sub contDiff_id
  have hgrade {i j : ℕ} (hij : i ≤ j) : 1 + p i x ≤ 1 + p j x :=
    add_le_add le_rfl (hp hij x)
  have hw (i : ℕ) : 0 ≤ p i x := apply_nonneg _ _
  have houter (k : ℕ) (_ : 1 ≤ k) : ‖iteratedFDeriv ℝ k u (g η)‖ ≤
      A k * (1 : ℝ) ^ (A k) * (1 + p (k + inputLoss) x) := by
    rw [Real.one_rpow, mul_one]
    exact (hleft k (g η)).trans (mul_le_mul (hLA k)
      (hgrade (Nat.add_le_add_left h1in k)) (add_nonneg zero_le_one (hw _))
      (zero_le_one.trans (hA k)))
  have hinner (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k g η‖ ≤
      A k * (1 : ℝ) ^ (A k) * (1 + p (k + inputLoss) x) := by
    rw [Real.one_rpow, mul_one]
    exact (hinv k hk η).trans (mul_le_mul (hBIA k)
      (hgrade (Nat.add_le_add_left hIin k)) (add_nonneg zero_le_one (hw _))
      (zero_le_one.trans (hA k)))
  have hc : ‖iteratedFDeriv ℝ n (u ∘ g) η‖ ≤ BC (n - 1) * (1 + p (n + outLoss) x) := by
    have hb := hcomp u g η hu.contDiffAt hg.contDiffAt houter hinner (n - 1)
    rw [Real.one_rpow, mul_one, Nat.sub_add_cancel hn] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (hgrade (Nat.add_le_add_left hCout n)) (hBC (n - 1)).le)
  have hi : ‖iteratedFDeriv ℝ n g η‖ ≤ BI n * (1 + p (n + outLoss) x) :=
    (hinv n hn η).trans (mul_le_mul_of_nonneg_left
      (hgrade (Nat.add_le_add_left (hIin.trans hinout) n)) (hBI n).le)
  have hid : ‖iteratedFDeriv ℝ n (id : ℝ → ℝ) η‖ ≤ 1 :=
    (flowJet_norm_iteratedFDeriv_clm_le (ContinuousLinearMap.id ℝ ℝ) hn η).trans
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
  have hdisp : ‖iteratedFDeriv ℝ n (g - id) η‖ ≤
      BI n * (1 + p (n + outLoss) x) + 1 := by
    rw [iteratedFDeriv_sub_apply
      (hg.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (contDiffAt_id.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
    exact (norm_sub_le _ _).trans (add_le_add hi hid)
  have he : (fun ξ => (l ∘ g) ξ - ξ) = (u ∘ g) + (g - id) := by
    funext ξ
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, id_eq, u]
    ring
  rw [he, iteratedFDeriv_add_apply (f := u ∘ g) (g := g - id)
    ((hu.comp hg).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    ((hg.sub contDiff_id).contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  have hw' := hw (n + outLoss)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (u ∘ g) η‖ + ‖iteratedFDeriv ℝ n (g - id) η‖ := norm_add_le _ _
    _ ≤ BC (n - 1) * (1 + p (n + outLoss) x) + (BI n * (1 + p (n + outLoss) x) + 1) :=
      add_le_add hc hdisp
    _ ≤ (BC (n - 1) + BI n + 1) * (1 + p (n + outLoss) x) := by nlinarith only [hw']
    _ ≤ B * (1 + p (n + outLoss) x) :=
      mul_le_mul_of_nonneg_right hB (add_nonneg zero_le_one hw')

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
  refine (n01_returnInverse_positiveJets_uniform hS hT hN hflow).elim ?_
  intro lowI hI1
  refine hI1.elim ?_
  intro lossI hI2
  refine hI2.elim ?_
  intro BI hI3
  have hBI := hI3.1
  have hinverse := hI3.2
  refine (n01_stateLeftChart_pairJets hS hT hN).elim ?_
  intro L hLleft
  have hL := hLleft.1
  have hleft := hLleft.2
  let inputLoss := max 1 lossI
  refine (coordinateComposition_fixed_loss_material_bound (X := ℝ) (Y := ℝ) (Z := ℝ)
    hp hI inputLoss).elim ?_
  intro lowC hC1
  refine hC1.elim ?_
  intro lossC htarget
  let A : ℕ → ℝ := fun k => 1 + L + BI k
  have hA (k : ℕ) : 1 ≤ A k := by
    dsimp only [A]
    linarith only [hL, hBI k]
  have hLA (k : ℕ) : L ≤ A k := by
    dsimp only [A]
    linarith only [hBI k]
  have hBIA (k : ℕ) : BI k ≤ A k := by
    dsimp only [A]
    linarith only [hL]
  refine (htarget A hA).elim ?_
  intro BC hC2
  have hBC := hC2.1
  have hcompose := hC2.2
  let outLoss := max inputLoss lossC
  let B : ℕ → ℝ := fun n => Real.pi + L + BC (n - 1) + BI n + 2
  have hB (n : ℕ) : 0 < B n := by
    dsimp only [B]
    linarith only [Real.pi_pos, hL, hBC (n - 1), hBI n]
  refine ⟨max lowI lowC, outLoss, B, hB, ?_⟩
  intro m z hz hs hlow side n θ
  have hlowI := (hp (le_max_left lowI lowC) _).trans hlow
  have hlowC := (hp (le_max_right lowI lowC) _).trans hlow
  by_cases hn0 : n = 0
  · subst n
    have hpB : Real.pi ≤ B 0 := by
      dsimp only [B]
      linarith only [hL, hBC (0 - 1), hBI 0]
    exact rootLabel_zero_jet_le hN hflow hz hs m side θ hpB (apply_nonneg _ _)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  cases side with
  | false =>
      have hLB : L ≤ B n := by
        dsimp only [B]
        linarith only [Real.pi_pos, hBC (n - 1), hBI n]
      have hlabel (η : ℝ) : n01RootLabel S C z m false η = stateLeftChart S z.1 m η := by
        unfold n01RootLabel
        rw [if_neg Bool.false_ne_true]
      exact label_jet_le_of_eq hlabel (hleft n m z θ) hLB
        (hp (Nat.add_le_add_left
          ((le_max_left 1 lossI).trans (le_max_left inputLoss lossC)) n) _)
        (apply_nonneg _ _) (hB n).le
  | true =>
      have hcoef : BC (n - 1) + BI n + 1 ≤ B n := by
        dsimp only [B]
        linarith only [Real.pi_pos, hL]
      have hlabel (η : ℝ) : n01RootLabel S C z m true η =
          oddPart (fun ξ => stateLeftChart S z.1 m (C.minusReturnInverse z m ξ) -
            C.travel m) η := by
        unfold n01RootLabel rightChartCandidate
        rw [if_pos rfl]
      exact rightLabel_jet_bound_generic hp (z - (C.referenceState, 0))
        (contDiff_stateLeftChart hS z.1 m) (n01_minusReturnInverse_contDiff hS hT hN hz hs m)
        (C.travel m) hlabel hA hLA hBIA hBI hBC (le_max_right 1 lossI) (le_max_left 1 lossI)
        (le_max_left inputLoss lossC) (le_max_right inputLoss lossC) hn
        (fun k η => hleft k m z η) (fun k hk η => hinverse z hz hs hlowI m k hk η)
        (hcompose (z - (C.referenceState, 0)) hlowC 1 le_rfl) hcoef θ

end ContinuousFlexibility.Analysis
