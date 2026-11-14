import ContinuousFlexibility.Analysis.N01RootFactorJetBounds
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets

/-!
# Actual divided-discriminant jets in the same normalized root variable

The already proved mixed bounds for the genuine divided discriminant
give all ordinary Fréchet jets. A fixed radial linear pullback adds only
an order-dependent numerical constant. No new state loss is introduced,
and neither the root scale nor the selected flow is changed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def rootScaledDividedDiscriminant
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (g : ℝ → ℝ) (r σ δ : ℝ) (q : PolarPoint) : ℝ :=
  rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ (δ * q.1, q.2)

private theorem exists_scaledFactor_frechet_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (C : ℕ → ℕ → ℝ)
    (hC : ∀ a b, 0 < C a b) (δ : ℝ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, ∀ U : Set PolarPoint, IsOpen U → ∀ f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ f U →
      (∀ a b : ℕ, ∀ q ∈ U, |mixedDerivative a b f q| ≤
        C a b * (1 + p (a + b + loss) z)) →
      ∀ q : PolarPoint, (δ * q.1, q.2) ∈ U →
      ContDiffAt ℝ ∞ (fun y => f (δ * y.1, y.2)) q ∧
        PointwiseMaterialJetBound p loss B z (fun y => f (δ * y.1, y.2)) q := by
  let L : PolarPoint →L[ℝ] PolarPoint :=
    (δ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL (q : PolarPoint) : L q = (δ * q.1, q.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  let A : ℕ → ℝ := fun n => 1 + ∑ i : Fin (n + 1), C i (n - i)
  have hA (n : ℕ) : 0 < A n := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hC i (n - i)).le))
  have hCA (a b : ℕ) : C a b ≤ A (a + b) := by
    have hi : a < a + b + 1 := by omega
    have ht := Finset.single_le_sum
      (f := fun i : Fin (a + b + 1) => C i (a + b - i))
      (fun i _ => (hC i (a + b - i)).le)
      (Finset.mem_univ (⟨a, hi⟩ : Fin (a + b + 1)))
    have ht' : C a b ≤ ∑ i : Fin (a + b + 1), C i (a + b - i) := by
      simpa only [show a + b - a = b by omega] using ht
    exact ht'.trans (le_add_of_nonneg_left zero_le_one)
  let B : ℕ → ℝ := fun n => (1 + ‖L‖ ^ n) * ((2 : ℝ) ^ n * A n)
  have hB (n : ℕ) : 0 < B n :=
    mul_pos (add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg (norm_nonneg L) n))
      (mul_pos (pow_pos (by norm_num) n) (hA n))
  refine ⟨B, hB, ?_⟩
  intro z U hU f hf hjet q hq
  have hqL : L q ∈ U := by rw [hL]; exact hq
  have hfL : ContDiffAt ℝ ∞ f (L q) := hf.contDiffAt (hU.mem_nhds hqL)
  have he : f ∘ L = (fun y => f (δ * y.1, y.2)) := by
    funext y
    rw [Function.comp_apply, hL]
  have hregular := hfL.comp q L.contDiff.contDiffAt
  rw [he] at hregular
  refine ⟨hregular, ?_⟩
  intro n
  have hM : 0 ≤ A n * (1 + p (n + loss) z) :=
    mul_nonneg (hA n).le (add_nonneg zero_le_one (apply_nonneg _ _))
  have hnorm : ‖iteratedFDeriv ℝ n f (L q)‖ ≤
      (2 : ℝ) ^ n * (A n * (1 + p (n + loss) z)) := by
    apply norm_iteratedFDeriv_le_of_mixedDerivative hU hf n hqL hM
    intro a b hab
    simpa only [Real.norm_eq_abs, hab] using (hjet a b (L q) hqL).trans
      (mul_le_mul_of_nonneg_right (hCA a b)
        (add_nonneg zero_le_one (apply_nonneg _ _)))
  have hcomp := norm_iteratedFDeriv_comp_linear_le_at L hfL n
  rw [he] at hcomp
  have hcoeff : ‖L‖ ^ n * ((2 : ℝ) ^ n * A n) ≤ B n :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) (hA n).le)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (L q)‖ * ‖L‖ ^ n := hcomp
    _ ≤ ((2 : ℝ) ^ n * (A n * (1 + p (n + loss) z))) * ‖L‖ ^ n :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg (norm_nonneg L) n)
    _ = (‖L‖ ^ n * ((2 : ℝ) ^ n * A n)) * (1 + p (n + loss) z) := by ring
    _ ≤ B n * (1 + p (n + loss) z) :=
      mul_le_mul_of_nonneg_right hcoeff (add_nonneg zero_le_one (apply_nonneg _ _))

def N01ScaledDividedFactorJetBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base low loss : ℕ) (ε r σ : ℝ) (g : ℝ → ℝ) (R δ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ q : PolarPoint, δ * q.1 ∈ Ioo (-R) R →
      ContDiffAt ℝ ∞ (rootScaledDividedDiscriminant D S C z g r σ δ) q ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
          (z - (C.referenceState, 0)) (rootScaledDividedDiscriminant D S C z g r σ δ) q

private theorem n01_scaledDividedFactor_bound_of_mixed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss low outLoss : ℕ} {ε r σ R δ : ℝ}
    {g : ℝ → ℝ} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : 0 < R) (hg : ContDiff ℝ ∞ g)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ R)
    (A : ℕ → ℕ → ℝ) (hA : ∀ a b, 0 < A a b)
    (hbound : ∀ a b, N01RootCoefficientRadialFactorBoundAtOrder
      D S C base low outLoss ε r σ g R a b (A a b)) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01ScaledDividedFactorJetBound D S C base low outLoss ε r σ g R δ B := by
  obtain ⟨B, hB, hgeneric⟩ := exists_scaledFactor_frechet_bound
    (pairGrading (stateGrading S) realGrading) outLoss A hA δ
  refine ⟨B, hB, ?_⟩
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  intro z hz hs hlow q hq
  have hf : ContDiffOn ℝ ∞ (rootCoefficientRadialFactor D.w g
      (stateProfile D S C z.1) (stateHeight D S C z) r σ)
      (Ioo (-R) R ×ˢ (univ : Set ℝ)) := by
    intro y hy
    have houter : y ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hy.1.1, hy.1.2]
    obtain ⟨hr, hw, hgy, hDy, hQy, _, _⟩ := hstrip z hz hs y houter
    exact (contDiffAt_rootCoefficientRadialFactor hwref hg
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z) hr hw hgy hDy hQy).contDiffWithinAt
  exact hgeneric (z - (C.referenceState, 0)) _ (isOpen_Ioo.prod isOpen_univ) _ hf
    (fun a b y hy => hbound a b z hz hs hlow y hy) q ⟨hq, mem_univ _⟩

/-- The same loss as true radial division controls all ordinary jets
after any fixed normalized radial scale. -/
theorem n01_scaledDividedFactor_fixed_loss_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ low outLoss : ℕ, ∀ r σ : ℝ, ∀ g : ℝ → ℝ, ∀ R : ℝ,
      (σ = 1 ∨ σ = -1) → 0 < R → ContDiff ℝ ∞ g →
      Ioo ((r - R) - R) ((r + R) + R) ⊆ Ioo D.a D.b →
      ∀ m : ℕ, Ioo (r - R) (r + R) ⊆ D.cells m →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) r σ R) →
      ∀ δ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        N01ScaledDividedFactorJetBound D S C base low outLoss ε r σ g R δ B := by
  obtain ⟨low, outLoss, hfactor⟩ := n01_rootCoefficientRadialFactor_fixed_loss_bound hS hT hN
  refine ⟨low, outLoss, ?_⟩
  intro r σ g R hσ hR hg hphysical m hcell hstrip δ
  choose A hA hbound using
    (fun a b => hfactor r σ g R hσ hR hg hphysical m hcell hstrip a b)
  exact n01_scaledDividedFactor_bound_of_mixed hS hT hN hR hg hstrip A hA hbound

end ContinuousFlexibility.Analysis
