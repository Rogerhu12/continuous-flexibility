module

public import ContinuousFlexibility.Analysis.N06MaterialPotential
public import ContinuousFlexibility.Analysis.N06WeightedHeight

/-!
# The actual potential contribution on the fixed canonical source

The material-small multiplier is composed with N05's already selected
weighted height map. Its physical output is the coefficient times the
height of the same graph inverse, at the same fixed angular source order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency true

private theorem n06_potential_norm_comp
    {E W X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : E →L[ℝ] W) (M : W →L[ℝ] X) {Qmat Qheight δ : ℝ}
    (hQmat : 0 ≤ Qmat) (hδ : 0 ≤ δ)
    (hH : ‖H‖ ≤ Qheight) (hM : ‖M‖ ≤ Qmat * δ) :
    ‖M.comp H‖ ≤ (Qmat * Qheight) * δ := by
  calc
    ‖M.comp H‖ ≤ ‖M‖ * ‖H‖ := ContinuousLinearMap.opNorm_comp_le M H
    _ ≤ (Qmat * δ) * Qheight :=
      mul_le_mul hM hH (norm_nonneg H) (mul_nonneg hQmat hδ)
    _ = (Qmat * Qheight) * δ := by ring

private theorem n06_potential_field_comp
    {E W α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α)
    (source : E → ∀ m, Lp ℝ 2 (μ m)) (intermediate : W → ∀ m, Lp ℝ 2 (μ m))
    (height : E → ∀ m, Lp ℝ 2 (μ m)) (H : E → W) (M : W → E)
    (a : ℕ → α → ℝ) (hH : ∀ F, intermediate (H F) = height F)
    (hM : ∀ W m, (source (M W) m : α → ℝ) =ᵐ[μ m]
      fun p => a m p * intermediate W m p) :
    ∀ F m, (source (M (H F)) m : α → ℝ) =ᵐ[μ m]
      fun p => a m p * height F m p := by
  intro F m
  have he : intermediate (H F) m = height F m := congrFun (hH F) m
  filter_upwards [hM (H F) m] with p hp
  exact hp.trans (congrArg (fun f : Lp ℝ 2 (μ m) => a m p * f p) he)

private theorem n06_potential_family_comp
    {E W α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace α]
    (μ : ℕ → Measure α)
    (source : E → ∀ m, Lp ℝ 2 (μ m)) (intermediate : W → ∀ m, Lp ℝ 2 (μ m))
    (height : E → ∀ m, Lp ℝ 2 (μ m))
    (P₁ P₂ P₃ : (ℕ → α → ℝ) → Prop) (P₄ : ℝ → (ℕ → α → ℝ) → Prop)
    (H : E →L[ℝ] W) {Qmat Qheight : ℝ} (hQmat : 0 ≤ Qmat) (hQheight : 0 ≤ Qheight)
    (hHnorm : ‖H‖ ≤ Qheight) (hHfield : ∀ F, intermediate (H F) = height F)
    (hmat : ∀ δ : ℝ, 0 ≤ δ → ∀ a : ℕ → α → ℝ,
      P₁ a → P₂ a → P₃ a → P₄ δ a →
      ∃ M : W →L[ℝ] E, ‖M‖ ≤ Qmat * δ ∧
        ∀ U m, (source (M U) m : α → ℝ) =ᵐ[μ m]
          fun p => a m p * intermediate U m p) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ a : ℕ → α → ℝ,
      P₁ a → P₂ a → P₃ a → P₄ δ a →
      ∃ P : E →L[ℝ] E, ‖P‖ ≤ Q * δ ∧
        ∀ F m, (source (P F) m : α → ℝ) =ᵐ[μ m]
          fun p => a m p * height F m p := by
  refine ⟨Qmat * Qheight, mul_nonneg hQmat hQheight, ?_⟩
  intro δ hδ a h₁ h₂ h₃ h₄
  obtain ⟨M, hMnorm, hMfield⟩ := hmat δ hδ a h₁ h₂ h₃ h₄
  refine ⟨M.comp H, n06_potential_norm_comp H M hQmat hδ hHnorm hMnorm, ?_⟩
  exact n06_potential_field_comp μ source intermediate height H M a hHfield hMfield

/-- The potential channel is a bounded endomorphism of the original
source. Only genuine scalar coefficient-jet bounds are supplied as inputs. -/
theorem n06N05_potentialMultiplier
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {b : ℕ} {B : CanonicalDomainData S K V b}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hN05 : N05Properties D T S C K V b B) (A : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ a : ℕ → PolarPoint → ℝ,
      (∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m)) →
      (∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p) →
      (∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = a m p) →
      (∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 i (a m) p| ≤
          δ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (K.cell m)) ^ A) →
      ∃ P : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
        ‖P‖ ≤ Q * δ ∧
        ∀ F m, (V.forget (3 / 4 : ℝ) 0 b (P F) m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m]
            fun p => a m p * (B.inverse F).val.1.1 m p := by
  have hV : IsVolumeModel T S K V := hN05.2.1
  obtain ⟨Qmat, hQmat, hmat⟩ := n06Volume_materialPotentialMultiplier
    hD hT hV (3 / 4 : ℝ) A B.lossMaterial (by norm_num) b
  obtain ⟨Qheight, hQheight, H, hHnorm, _, hHgraph, _⟩ :=
    n06N05_exists_weightedHeight hN05
  have hheight (F : V.level (3 / 4 : ℝ) 0 b) :
      V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (H F) =
        fun m => (B.inverse F).val.1.1 m :=
    (hHgraph F).trans (funext (n06InverseCanonicalHeight_apply (B := B) F))
  exact n06_potential_family_comp (canonicalMeasure S K)
    (fun F : V.level (3 / 4 : ℝ) 0 b => V.forget (3 / 4 : ℝ) 0 b F)
    (fun W : V.level (3 / 4 : ℝ) (-B.lossMaterial) b =>
      V.forget (3 / 4 : ℝ) (-B.lossMaterial) b W)
    (fun F : V.level (3 / 4 : ℝ) 0 b => fun m => (B.inverse F).val.1.1 m)
    (fun a => ∀ m, ContDiffOn ℝ ∞ (a m) (canonicalOpen S K m))
    (fun a => ∀ m p, p ∈ canonicalOpen S K m → a m (p + (0, Real.pi)) = a m p)
    (fun a => ∀ m p, p ∈ canonicalOpen S K m → a m (p.1, Real.pi - p.2) = a m p)
    (fun δ a => ∀ m i, i ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 i (a m) p| ≤
        δ * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (K.cell m)) ^ A)
    H hQmat hQheight.le hHnorm hheight hmat

end ContinuousFlexibility.Statements
