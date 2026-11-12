import ContinuousFlexibility.Analysis.N07aPhysicalJetTowers
import ContinuousFlexibility.Analysis.N07aSobolevCoordinates
import ContinuousFlexibility.Analysis.N07aSobolevTowers
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Lifting a genuine physical parameter family with its one-high estimate

The inputs are the actual decoded family, its genuine ordinary spatial-jet
towers, and their uniform physical decay estimate. Closed weak graphs
produce the original Sobolev-valued tower. The same one-high estimate then
holds in the frozen grading, with the original fixed base and loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped Topology ContDiff BigOperators
open ContinuousFlexibility.Statements

section Weights

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {p : ℕ → Seminorm ℝ E}

theorem n07a_oneHighVariationWeight_continuous
    (hp : WithSeminorms p) (b s k : ℕ) (x₀ : E) :
    Continuous (fun z : E × (Fin k → E) => oneHighVariationWeight p b s (z.1 - x₀) z.2) := by
  let : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  unfold oneHighVariationWeight
  apply Continuous.add
  · exact (continuous_const.add ((hp.continuous_seminorm s).comp
        (continuous_fst.sub continuous_const))).mul
      (continuous_finsetProd _ fun i _ => (hp.continuous_seminorm b).comp
        ((continuous_apply i).comp continuous_snd))
  · apply continuous_finsetSum
    intro i _
    exact ((hp.continuous_seminorm s).comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetProd _ fun j _ => (hp.continuous_seminorm b).comp
        ((continuous_apply j).comp continuous_snd))

theorem n07a_oneHighVariationWeight_mono
    (hp : Monotone p) (b : ℕ) {s t : ℕ} (hst : s ≤ t)
    (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p b s x v ≤ oneHighVariationWeight p b t x v := by
  simpa only [tameJetSize, oneHighVariationWeight, zero_add] using
    tameJetSize_mono hp (base := b) (base' := b) hst le_rfl k 0 x v

theorem n07a_oneHighVariationWeight_translate_le
    (p : ℕ → Seminorm ℝ E) (b s : ℕ) (x x₀ : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p b s (x - x₀) v ≤
      (1 + p s x₀) * oneHighVariationWeight p b s x v := by
  have hfirst : 1 + p s (x - x₀) ≤ (1 + p s x₀) * (1 + p s x) := by
    have h := map_sub_le_add (p s) x x₀
    have hx := apply_nonneg (p s) x
    have hx₀ := apply_nonneg (p s) x₀
    nlinarith only [h, hx, hx₀, mul_nonneg hx hx₀]
  have hsum : 0 ≤ ∑ i : Fin k, p s (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j) := by
    positivity
  unfold oneHighVariationWeight
  rw [mul_add]
  apply add_le_add
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hfirst (Finset.prod_nonneg fun i _ => apply_nonneg (p b) (v i))
  · exact le_mul_of_one_le_left hsum (le_add_of_nonneg_right (apply_nonneg (p s) x₀))

end Weights

section Family

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {A : SobolevModelData} {γ δ : ℝ}
  {U : Set E} {p : ℕ → Seminorm ℝ E} {base loss : ℕ} {x₀ : E}
  {f : E → PolarPoint → ℝ} {g : E → A.Space}
  (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
  (hp : WithSeminorms p) (hg : ∀ x ∈ U, A.decode (g x) = f x)
  (J : ∀ a b (q : annularOpen D), SmoothDirections U (fun x => mixedDerivative a b (f x) q.val))

include hA hg in
private theorem n07aHeightFamily_spatial (x : E) (hx : x ∈ U) :
    ContDiffOn ℝ ∞ (f x) (annularOpen D) := by
  rw [← hg x hx]
  exact (hA.2.2.2.1 (g x)).1

include hp

def n07aHeightFamilyWeightedTower (a b c : ℕ) (q : PolarPoint) :
    SmoothDirections U (fun x => weightedPhysicalJet T γ a b c (f x) q) :=
  n07aWeightedJetTower hT hU (n07aHeightFamily_spatial hA hg) J γ a b c q

variable (hJ : ∀ k s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
  ∀ (a b : ℕ) (q : annularOpen D), a + b ≤ s →
    ∀ x ∈ U, ∀ v : Fin k → E,
      |(J a b q).D k x v| ≤ B * T.H q.val.1 ^ δ *
        oneHighVariationWeight p base (s + loss) (x - x₀) v)

include hJ in
private theorem n07aHeightFamily_weighted_bound_exists (a b k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℕ) x, x ∈ U → ∀ (v : Fin k → E) (q : PolarPoint),
      |(n07aHeightFamilyWeightedTower hT hA hU hg J a b c q).D k x v| ≤
        B * oneHighVariationWeight p base (a + b + loss) (x - x₀) v *
          n07aMaterialJetMajorant T γ δ c q := by
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := hp.continuousSMul
  obtain ⟨K, hK, hKb⟩ := n07aWeightedJetTower_decay_bound hT hU
    (n07aHeightFamily_spatial hA hg) J γ δ a
  obtain ⟨B, hB, hBb⟩ := hJ k (a + b)
  refine ⟨K * B, mul_nonneg hK hB, fun c x hx v q => ?_⟩
  have h := hKb b c k x v B (oneHighVariationWeight p base (a + b + loss) (x - x₀) v)
    hB (by unfold oneHighVariationWeight; positivity)
    (fun j hj q => hBb j b q (Nat.add_le_add_right hj b) x hx v) q
  exact h.trans_eq (by dsimp only [n07aMaterialJetMajorant]; ring)

def n07aHeightFamilyJetConstant (a b k : ℕ) : ℝ :=
  (n07aHeightFamily_weighted_bound_exists hT hA hU hp hg J hJ a b k).choose

theorem n07aHeightFamilyJetConstant_nonneg (a b k : ℕ) :
    0 ≤ n07aHeightFamilyJetConstant hT hA hU hp hg J hJ a b k :=
  (n07aHeightFamily_weighted_bound_exists hT hA hU hp hg J hJ a b k).choose_spec.1

def n07aHeightFamilyJetCost (a b k : ℕ) (z : E × (Fin k → E)) : ℝ :=
  n07aHeightFamilyJetConstant hT hA hU hp hg J hJ a b k *
    oneHighVariationWeight p base (a + b + loss) (z.1 - x₀) z.2

theorem n07aHeightFamilyJetCost_continuous (a b k : ℕ) :
    Continuous (n07aHeightFamilyJetCost hT hA hU hp hg J hJ a b k) :=
  continuous_const.mul (n07a_oneHighVariationWeight_continuous hp base (a + b + loss) k x₀)

theorem n07aHeightFamilyJetCost_nonneg (a b k : ℕ) (z : E × (Fin k → E)) :
    0 ≤ n07aHeightFamilyJetCost hT hA hU hp hg J hJ a b k z :=
  mul_nonneg (n07aHeightFamilyJetConstant_nonneg hT hA hU hp hg J hJ a b k)
    (by unfold oneHighVariationWeight; positivity)

theorem n07aHeightFamilyJetCost_bound (a b c k : ℕ) (x : E) (hx : x ∈ U)
    (v : Fin k → E) (q : PolarPoint) :
    |(n07aHeightFamilyWeightedTower hT hA hU hg J a b c q).D k x v| ≤
      n07aHeightFamilyJetCost hT hA hU hp hg J hJ a b k (x, v) *
        n07aMaterialJetMajorant T γ δ c q :=
  (n07aHeightFamily_weighted_bound_exists hT hA hU hp hg J hJ a b k).choose_spec.2 c x hx v q

variable (hγδ : γ < δ)

/-- L² parameter derivatives keep the exact coordinates of the chosen
actual Sobolev element. -/
def n07aHeightFamilyCoordinateTower (s : ℕ) (j : JetIndex s) :
    SmoothDirections U (fun x => ((g x).val s).val j) := by
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := hp.continuousSMul
  letI : FirstCountableTopology E := hp.firstCountableTopology
  let hf := n07aHeightFamily_spatial hA hg
  let G := n07aHeightFamilyJetCost hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val
  let hG := n07aHeightFamilyJetCost_continuous hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val
  let hb := fun k x hx v q => n07aHeightFamilyJetCost_bound hT hA hU hp hg J hJ
    (j.val 0).val (j.val 1).val (j.val 2).val k x hx v q
  let K := n07aWeightedJetLpTower hT hU hf J hγδ
    (j.val 0).val (j.val 1).val (j.val 2).val G hG hb
  apply K.congr
  intro x hx
  rw [← K.zero x hx]
  apply Lp.ext
  have hcoord := n07a_sobolev_coordinate_ae hT hA (g x) s j
  rw [hg x hx] at hcoord
  filter_upwards [n07aWeightedJetLpTower_D_ae hT hU hf J hγδ
      (j.val 0).val (j.val 1).val (j.val 2).val G hG hb 0 hx Fin.elim0,
    hcoord] with q hq hr
  rw [hq, (n07aWeightedJetTower hT hU hf J γ
    (j.val 0).val (j.val 1).val (j.val 2).val q).zero x hx, hr]

theorem n07aHeightFamilyCoordinateTower_D_norm_le
    (s : ℕ) (j : JetIndex s) (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    ‖(n07aHeightFamilyCoordinateTower hT hA hU hp hg J hJ hγδ s j).D k x v‖ ≤
      n07aHeightFamilyJetCost hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val k (x, v) *
        ‖(n07aMaterialJetMajorant_memLp hT hγδ (j.val 2).val).toLp
          (n07aMaterialJetMajorant T γ δ (j.val 2).val)‖ := by
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := hp.continuousSMul
  letI : FirstCountableTopology E := hp.firstCountableTopology
  exact n07aWeightedJetLpTower_D_norm_le hT hU (n07aHeightFamily_spatial hA hg) J hγδ
    (j.val 0).val (j.val 1).val (j.val 2).val
    (n07aHeightFamilyJetCost hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val)
    (n07aHeightFamilyJetCost_continuous hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val)
    (fun k x hx v q => n07aHeightFamilyJetCost_bound hT hA hU hp hg J hJ
      (j.val 0).val (j.val 1).val (j.val 2).val k x hx v q)
    k hx v (n07aHeightFamilyJetCost_nonneg hT hA hU hp hg J hJ _ _ _ _)

/-- The genuine tower lies in the original closed Sobolev realization. -/
def n07aHeightFamilyTower : SmoothDirections U g := by
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := hp.continuousSMul
  exact n07aSobolevParameterTower hA hU
    (n07aHeightFamilyCoordinateTower hT hA hU hp hg J hJ hγδ)

omit hp

include hA in
/-- The fixed finite-product norm contributes only a constant at each
output order. The level is the actual frozen Sobolev level. -/
theorem n07a_sobolevGrading_le_coordinate_bound (u : A.Space) (s : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hcoord : ∀ j : JetIndex s, ‖(u.val s).val j‖ ≤ R) :
    A.grading s u ≤
      ‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap‖ * R := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap
  have he : L (fun j : JetIndex s => (u.val s).val j) = (u.val s).val :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : JetIndex s => CylinderL2)).symm_apply_apply _
  rw [sobolevGrading_eq_physicalNorm hA u s, ← hA.2.2.2.2.2.2.2 u s]
  change ‖(u.val s).val‖ ≤ ‖L‖ * R
  rw [← he]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg hR).mpr hcoord) (norm_nonneg L))

include hp

/-- The original N01-style estimate passes to the complete actual model
with exactly its fixed base and loss. -/
theorem n07aHeightFamilyTower_uniform (hmono : Monotone p) :
    UniformScalarTowerEstimate p A.grading U base loss g
      (n07aHeightFamilyTower hT hA hU hp hg J hJ hγδ) := by
  classical
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ E := hp.continuousSMul
  letI : FirstCountableTopology E := hp.firstCountableTopology
  intro k s _hs
  let L := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap
  let B : JetIndex s → ℝ := fun j =>
    n07aHeightFamilyJetConstant hT hA hU hp hg J hJ (j.val 0).val (j.val 1).val k *
      ‖(n07aMaterialJetMajorant_memLp hT hγδ (j.val 2).val).toLp
        (n07aMaterialJetMajorant T γ δ (j.val 2).val)‖
  have hB (j : JetIndex s) : 0 ≤ B j :=
    mul_nonneg (n07aHeightFamilyJetConstant_nonneg hT hA hU hp hg J hJ _ _ _) (norm_nonneg _)
  let C : ℝ := ‖L‖ * (∑ j, B j) * (1 + p (s + loss) x₀)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ => hB j))
    (add_nonneg zero_le_one (apply_nonneg _ _))
  refine ⟨C, hC, fun x hx v => ?_⟩
  let V : ℝ := oneHighVariationWeight p base (s + loss) (x - x₀) v
  have hV : 0 ≤ V := by dsimp only [V]; unfold oneHighVariationWeight; positivity
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hB j
  have hcoord (j : JetIndex s) :
      ‖(((n07aHeightFamilyTower hT hA hU hp hg J hJ hγδ).D k x v).val s).val j‖ ≤
        (∑ j, B j) * V := by
    rw [n07aHeightFamilyTower,
      n07aSobolevParameterTower_D_coordinate hA hU _ k hx v s j]
    have hj := n07aHeightFamilyCoordinateTower_D_norm_le hT hA hU hp hg J hJ hγδ s j k hx v
    have hord : (j.val 0).val + (j.val 1).val + loss ≤ s + loss :=
      Nat.add_le_add_right ((Nat.le_add_right _ _).trans j.property) loss
    have hw := n07a_oneHighVariationWeight_mono hmono base hord (x - x₀) v
    calc
      _ ≤ n07aHeightFamilyJetCost hT hA hU hp hg J hJ
          (j.val 0).val (j.val 1).val k (x, v) *
          ‖(n07aMaterialJetMajorant_memLp hT hγδ (j.val 2).val).toLp
            (n07aMaterialJetMajorant T γ δ (j.val 2).val)‖ := hj
      _ = B j * oneHighVariationWeight p base
          ((j.val 0).val + (j.val 1).val + loss) (x - x₀) v := by
        dsimp only [B, n07aHeightFamilyJetCost]
        ring
      _ ≤ B j * V := mul_le_mul_of_nonneg_left hw (hB j)
      _ ≤ (∑ j, B j) * V :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ j)) hV
  have h := n07a_sobolevGrading_le_coordinate_bound hA
    ((n07aHeightFamilyTower hT hA hU hp hg J hJ hγδ).D k x v) s
    (mul_nonneg hsum hV) hcoord
  change A.grading s ((n07aHeightFamilyTower hT hA hU hp hg J hJ hγδ).D k x v) ≤
    C * oneHighVariationWeight p base (s + loss) x v
  apply h.trans
  calc
    _ = (‖L‖ * (∑ j, B j)) * V := by ring
    _ ≤ (‖L‖ * (∑ j, B j)) *
        ((1 + p (s + loss) x₀) * oneHighVariationWeight p base (s + loss) x v) :=
      mul_le_mul_of_nonneg_left
        (n07a_oneHighVariationWeight_translate_le p base (s + loss) x x₀ v)
        (mul_nonneg (norm_nonneg _) hsum)
    _ = C * oneHighVariationWeight p base (s + loss) x v := by dsimp only [C]; ring

include hT hA hU hg J hJ hγδ in
/-- No additional smoothness or estimate premise is introduced after the
actual ordinary jet bounds have been supplied. -/
theorem n07a_heightFamily_fixedNeighborhoodSmoothTame (hmono : Monotone p) :
    FixedNeighborhoodSmoothTame p A.grading U base loss g :=
  fixedNeighborhoodSmoothTame_of_uniform
    (n07aHeightFamilyTower hT hA hU hp hg J hJ hγδ)
    (n07aHeightFamilyTower_uniform hT hA hU hp hg J hJ hγδ hmono)

end Family

end ContinuousFlexibility.Analysis
