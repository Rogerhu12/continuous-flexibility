module

public import ContinuousFlexibility.Analysis.N07aSampleMaterialAbsorption
public import ContinuousFlexibility.Analysis.N07aActualPieceCover
public import ContinuousFlexibility.Analysis.N07aStateSampleLinearJets
public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
public import ContinuousFlexibility.Analysis.N07aMaterialJetFunctional

/-!
# The actual weighted physical jets from the piece estimates

Every finite ordinary jet entering the true material formula is bounded
at the same point. The complete coefficient envelope costs two material
orders, and continuity extends the resulting bound across interfaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base geometryLoss : ℕ} {ε γ : ℝ}
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {low loss : ℕ} {f : E → F → PolarPoint → ℝ}

theorem n07a_sampleLinearJets_weighted_physical_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (hrefState : referenceStateConditions D S C)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (ζ : E → CanonicalGeometry.Parameter S)
    (hζ : MapsTo ζ U (sectorNeighborhood S base ε ε))
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp : Monotone p) (hq : Monotone q)
    (hf : N07aStateSampleLinearJetBounds T K p q U
      (fun z m => physicalPieceOpen S K (liftSectorParameter S C (ζ z)) m)
      (fun c m => T.H (T.sample (K.cell m)) ^ γ * (T.M (T.sample (K.cell m)) ^ c)⁻¹)
      low loss (fun z u _ => f z u))
    (hfs : ∀ z ∈ U, ∀ u, ContDiffOn ℝ ∞ (f z u) (annularOpen D))
    (a b c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ U, ∀ u x,
      |weightedPhysicalJet T γ a b c (f z u) x| ≤ A * (T.M (T.radius x.1))⁻¹ *
        (q (a + b + c + (loss + 2)) u +
          (1 + p (a + b + c + (loss + 2)) z) * q low u) := by
  classical
  choose e he he0 heb using fun j : Fin (a + 1) => hf j.val b (c + 2)
  obtain ⟨K₀, hK₀, hKb⟩ := n07aMaterialJetFunctional_bound hT γ a
  let e₀ : ℕ → ℝ := fun m => ∑ j : Fin (a + 1), e j m
  have he₀ : N07aSampleSubpower T K e₀ :=
    N07aSampleSubpower.finset_sum hD hT Finset.univ e (fun j _ => he j)
  have he₀0 (m : ℕ) : 0 ≤ e₀ m := Finset.sum_nonneg (fun j _ => he0 j m)
  have hfull := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT K₀) he₀
  obtain ⟨A, hA, hAb⟩ := n07a_sampleMaterial_absorb_actual hD hT hrefState h04.1 hRatio hγ hγ1
    hfull (fun m => mul_nonneg hK₀ (he₀0 m)) c
  refine ⟨A, hA, fun z hz u x => ?_⟩
  let B := q (a + b + c + (loss + 2)) u +
    (1 + p (a + b + c + (loss + 2)) z) * q low u
  have hB : 0 ≤ B := add_nonneg (apply_nonneg _ _)
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  have hpiece (m : ℕ) (y : PolarPoint) (hy : y ∈ physicalPieceOpen S K (liftSectorParameter S C (ζ z)) m) :
      |weightedPhysicalJet T γ a b c (f z u) (T.rho y.1, y.2)| ≤
        A * (T.M y.1)⁻¹ * B := by
    have hyD := ((h04.1.domains _
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hζ hz) le_rfl)
      (hrefState.liftSectorParameter_sector (ζ z)) m).2.2.1 hy).1
    have hsample := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    let w := T.H (T.sample (K.cell m)) ^ γ *
      (T.M (T.sample (K.cell m)) ^ (c + 2))⁻¹
    have hw : 0 ≤ w := mul_nonneg (Real.rpow_nonneg hsample.2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hsample.2.2.2) _))
    have hv (j : Fin (a + 1)) :
        |mixedDerivative j.val b (f z u) y| ≤ e₀ m * w * B := by
      have hj : c + 2 + (j.val + b) + loss ≤ a + b + c + (loss + 2) := by
        have hj := j.isLt
        omega
      calc
        _ ≤ e j m * w *
            (q (c + 2 + (j.val + b) + loss) u +
              (1 + p (c + 2 + (j.val + b) + loss) z) * q low u) :=
          heb j z hz u m y hy
        _ ≤ e j m * w * B := mul_le_mul_of_nonneg_left
          (add_le_add (hq hj u)
            (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hp hj z)) (apply_nonneg _ _)))
          (mul_nonneg (he0 j m) hw)
        _ ≤ e₀ m * w * B := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun j _ => he0 j m) (Finset.mem_univ j)) hw) hB
    have hinv : T.radius (T.rho y.1) = y.1 := hT.2.2.2.2.2.2.2.2.1 y.1 hyD
    have hval : ∀ j : Fin (a + 1),
        |mixedDerivative j.val b (f z u) (T.radius (T.rho y.1), y.2)| ≤ e₀ m * w * B := by
      intro j
      simpa only [hinv, Prod.eta] using hv j
    have hmat := hKb c (T.rho y.1, y.2) (e₀ m * w * B)
      (mul_nonneg (mul_nonneg (he₀0 m) hw) hB)
      (fun j => mixedDerivative j.val b (f z u) (T.radius (T.rho y.1), y.2)) hval
    rw [n07aMaterialJetFunctional_mixedDerivative hT (hfs z hz u)] at hmat
    simp only [Prod.fst, hinv] at hmat
    calc
      _ ≤ K₀ * T.M y.1 ^ c * T.H y.1 ^ (-γ) * (e₀ m * w * B) := hmat
      _ = ((K₀ * e₀ m) * T.M y.1 ^ c * T.H y.1 ^ (-γ) * w) * B := by ring
      _ ≤ (A * (T.M y.1)⁻¹) * B := mul_le_mul_of_nonneg_right (hAb (ζ z) (hζ hz) m y hy) hB
  have hρ : ContinuousOn (fun y : PolarPoint => (T.rho y.1, y.2)) (annularOpen D) :=
    (((hT.1 T.rho (by simp)).continuousOn.comp continuous_fst.continuousOn
      (fun _ hy => hy.1)).prodMk continuous_snd.continuousOn)
  have hleft : ContinuousOn
      (fun y : PolarPoint => |weightedPhysicalJet T γ a b c (f z u) (T.rho y.1, y.2)|)
      (annularOpen D) :=
    ((contDiff_weightedPhysicalJet hT (hfs z hz u) a b c).continuous.comp_continuousOn hρ).abs
  have hM : ContinuousOn (fun y : PolarPoint => (T.M y.1)⁻¹) (annularOpen D) :=
    (((hT.1 T.M (by simp)).continuousOn.comp continuous_fst.continuousOn
      (fun _ hy => hy.1)).inv₀
      (fun y hy => (zero_lt_one.trans_le (hT.2.1 y.1 hy.1).2.2.2).ne'))
  have hall := n07a_actualPhysicalPiece_bound h04.1
    (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hζ hz) le_rfl)
    (hrefState.liftSectorParameter_sector (ζ z)) hleft
    ((continuousOn_const.mul hM).mul continuousOn_const) hpiece
    (T.radius x.1, x.2) ⟨(hT.2.2.2.2.2.2.2.1 x.1).1, mem_univ _⟩
  simpa only [Pi.mul_apply, Prod.fst, Prod.snd,
    (hT.2.2.2.2.2.2.2.1 x.1).2, Prod.eta] using hall

end ContinuousFlexibility.Analysis
