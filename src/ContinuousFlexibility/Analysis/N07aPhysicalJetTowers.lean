module

public import ContinuousFlexibility.Analysis.N07aMaterialJetFunctional
public import ContinuousFlexibility.Analysis.N07aLpDirectionalTower
public import ContinuousFlexibility.Analysis.TameElementaryCalculus
public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
public import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Actual material-coordinate parameter towers

The finite material formula is applied to the genuine towers of ordinary
physical jets. The original output is identified with the actual weighted
jet. The same fixed linear formula then controls every parameter order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {U : Set E}
  {f : E → PolarPoint → ℝ}

/-- The genuine parameter tower of an actual weighted spatial jet. -/
def n07aWeightedJetTower
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    (γ : ℝ) (a b c : ℕ) (p : PolarPoint) :
    SmoothDirections U (fun x => weightedPhysicalJet T γ a b c (f x) p) :=
  (smoothDirectionsScalarPostcompose
    (smoothDirectionsScalarPi hU (fun j : Fin (a + 1) =>
      J j.val b ⟨(T.radius p.1, p.2),
        ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩⟩))
    (n07aMaterialJetFunctional T γ a c p)).congr
      (fun x hx => n07aMaterialJetFunctional_mixedDerivative hT (hf x hx) γ a b c p)

theorem n07aWeightedJetTower_D
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    (γ : ℝ) (a b c : ℕ) (p : PolarPoint) (k : ℕ) (x : E) (v : Fin k → E) :
    (n07aWeightedJetTower hT hU hf J γ a b c p).D k x v =
      n07aMaterialJetFunctional T γ a c p (fun j : Fin (a + 1) =>
        (J j.val b ⟨(T.radius p.1, p.2),
          ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩⟩).D k x v) := by
  unfold n07aWeightedJetTower SmoothDirections.congr
  rw [smoothDirectionsScalarPostcompose_apply]
  rfl

/-- All genuine parameter derivatives are measurable in the material
point. This follows from difference quotients, not a Schwarz premise. -/
theorem n07aWeightedJetTower_aestronglyMeasurable
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    (γ : ℝ) (a b c k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    AEStronglyMeasurable
      (fun p => (n07aWeightedJetTower hT hU hf J γ a b c p).D k x v)
      materialCylinderMeasure :=
  n07a_smoothDirections_aestronglyMeasurable hU
    (n07aWeightedJetTower hT hU hf J γ a b c)
    (fun x hx => (contDiff_weightedPhysicalJet hT (hf x hx) a b c).continuous.aestronglyMeasurable)
    k x hx v

/-- The original height decay survives the fixed change of coordinates
with the exact loss of the requested physical weight. -/
theorem n07aWeightedJetTower_decay_bound
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    (γ δ : ℝ) (a : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b c k : ℕ) (x : E) (v : Fin k → E)
      (B V : ℝ), 0 ≤ B → 0 ≤ V →
      (∀ (j : ℕ), j ≤ a → ∀ p : annularOpen D,
        |(J j b p).D k x v| ≤ B * T.H p.val.1 ^ δ * V) →
      ∀ p : PolarPoint,
        |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
          A * B * (T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (δ - γ)) * V := by
  obtain ⟨A, hA, hAb⟩ := n07aMaterialJetFunctional_bound hT γ a
  refine ⟨A, hA, fun b c k x v B V hB hV hbound p => ?_⟩
  have hH := (hT.2.1 _ (hT.2.2.2.2.2.2.2.1 p.1).1).2.1
  rw [n07aWeightedJetTower_D]
  have h := hAb c p (B * T.H (T.radius p.1) ^ δ * V)
    (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hH.le _)) hV)
    (fun j : Fin (a + 1) =>
      (J j.val b ⟨(T.radius p.1, p.2),
        ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩⟩).D k x v)
    (fun j => hbound j.val (Nat.le_of_lt_succ j.isLt) _)
  apply h.trans_eq
  rw [sub_eq_add_neg, Real.rpow_add hH]
  ring

/-- The actual square-integrable material majorant left by a positive
margin between the physical decay and requested weight. -/
def n07aMaterialJetMajorant (T : MaterialData) (γ δ : ℝ) (c : ℕ)
    (p : PolarPoint) : ℝ :=
  T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (δ - γ)

theorem n07aMaterialJetMajorant_nonneg (hT : IsMaterialData D T)
    (γ δ : ℝ) (c : ℕ) (p : PolarPoint) :
    0 ≤ n07aMaterialJetMajorant T γ δ c p := by
  have hp := (hT.2.2.2.2.2.2.2.1 p.1).1
  exact mul_nonneg
    (pow_nonneg (zero_le_one.trans (hT.2.1 _ hp).2.2.2) c)
    (Real.rpow_nonneg (hT.2.1 _ hp).2.1.le _)

theorem n07aMaterialJetMajorant_memLp (hT : IsMaterialData D T)
    {γ δ : ℝ} (hγδ : γ < δ) (c : ℕ) :
    MemLp (n07aMaterialJetMajorant T γ δ c) 2 materialCylinderMeasure := by
  change MemLp (fun p : PolarPoint =>
    T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (δ - γ)) 2 materialCylinderMeasure
  simpa only [Real.rpow_natCast] using
    n07a_materialM_rpow_mul_H_rpow_cylinder_memLp hT (c : ℝ) (sub_pos.mpr hγδ)

theorem n07aWeightedJetTower_memLp
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    {γ δ : ℝ} (hγδ : γ < δ) (a b c k : ℕ) {x : E} (hx : x ∈ U)
    (v : Fin k → E) (B : ℝ)
    (hb : ∀ p, |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
      B * n07aMaterialJetMajorant T γ δ c p) :
    MemLp (fun p => (n07aWeightedJetTower hT hU hf J γ a b c p).D k x v)
      2 materialCylinderMeasure := by
  apply ((n07aMaterialJetMajorant_memLp hT hγδ c).const_mul B).mono'
    (n07aWeightedJetTower_aestronglyMeasurable hT hU hf J γ a b c k hx v)
  exact Filter.Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs] using hb p

section LpTower

variable [FirstCountableTopology E]

private theorem n07aWeightedJetTower_local_majorant
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    {γ δ : ℝ} (hγδ : γ < δ) (a b c : ℕ)
    (G : ∀ k : ℕ, E × (Fin k → E) → ℝ)
    (hG : ∀ k, Continuous (G k))
    (hb : ∀ k x, x ∈ U → ∀ (v : Fin k → E) p,
      |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
        G k (x, v) * n07aMaterialJetMajorant T γ δ c p)
    (k : ℕ) (z : E × (Fin k → E)) (_hz : z.1 ∈ U) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 materialCylinderMeasure ∧
      ∀ᶠ q in 𝓝[U ×ˢ univ] z, ∀ p,
        |(n07aWeightedJetTower hT hU hf J γ a b c p).D k q.1 q.2| ≤ g p := by
  refine ⟨fun p => (G k z + 1) * n07aMaterialJetMajorant T γ δ c p,
    (n07aMaterialJetMajorant_memLp hT hγδ c).const_mul _, ?_⟩
  have hnear : ∀ᶠ q in 𝓝 z, G k q ≤ G k z + 1 :=
    ((hG k).tendsto z).eventually_le_const (lt_add_one _)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqU
  intro p
  exact (hb k q.1 hqU.1 q.2 p).trans
    (mul_le_mul_of_nonneg_right hq (n07aMaterialJetMajorant_nonneg hT γ δ c p))

/-- A continuous numerical parameter factor and the actual physical
decay bound produce a genuine L² tower for the weighted spatial jet. -/
def n07aWeightedJetLpTower
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    {γ δ : ℝ} (hγδ : γ < δ) (a b c : ℕ)
    (G : ∀ k : ℕ, E × (Fin k → E) → ℝ)
    (hG : ∀ k, Continuous (G k))
    (hb : ∀ k x, x ∈ U → ∀ (v : Fin k → E) p,
      |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
        G k (x, v) * n07aMaterialJetMajorant T γ δ c p) :
    SmoothDirections U (fun x =>
      n07aLpJetMultilinear (n07aWeightedJetTower hT hU hf J γ a b c)
        (fun k x hx v => n07aWeightedJetTower_memLp hT hU hf J hγδ a b c k hx v
          (G k (x, v)) (hb k x hx v)) 0 x Fin.elim0) :=
  n07aLpSmoothDirections hU (n07aWeightedJetTower hT hU hf J γ a b c)
    (fun k x hx v => n07aWeightedJetTower_memLp hT hU hf J hγδ a b c k hx v
      (G k (x, v)) (hb k x hx v))
    (n07aWeightedJetTower_local_majorant hT hU hf J hγδ a b c G hG hb)

theorem n07aWeightedJetLpTower_D_ae
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    {γ δ : ℝ} (hγδ : γ < δ) (a b c : ℕ)
    (G : ∀ k : ℕ, E × (Fin k → E) → ℝ)
    (hG : ∀ k, Continuous (G k))
    (hb : ∀ k x, x ∈ U → ∀ (v : Fin k → E) p,
      |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
        G k (x, v) * n07aMaterialJetMajorant T γ δ c p)
    (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    (((n07aWeightedJetLpTower hT hU hf J hγδ a b c G hG hb).D k x v) : PolarPoint → ℝ)
      =ᵐ[materialCylinderMeasure]
        (fun p => (n07aWeightedJetTower hT hU hf J γ a b c p).D k x v) :=
  n07aLpSmoothDirections_D_ae hU _ _ _ k hx v

theorem n07aWeightedJetLpTower_D_norm_le
    (hT : IsMaterialData D T) (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
    (J : ∀ a b (p : annularOpen D),
      SmoothDirections U (fun x => mixedDerivative a b (f x) p.val))
    {γ δ : ℝ} (hγδ : γ < δ) (a b c : ℕ)
    (G : ∀ k : ℕ, E × (Fin k → E) → ℝ)
    (hG : ∀ k, Continuous (G k))
    (hb : ∀ k x, x ∈ U → ∀ (v : Fin k → E) p,
      |(n07aWeightedJetTower hT hU hf J γ a b c p).D k x v| ≤
        G k (x, v) * n07aMaterialJetMajorant T γ δ c p)
    (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) (hG0 : 0 ≤ G k (x, v)) :
    ‖(n07aWeightedJetLpTower hT hU hf J hγδ a b c G hG hb).D k x v‖ ≤
      G k (x, v) * ‖(n07aMaterialJetMajorant_memLp hT hγδ c).toLp
        (n07aMaterialJetMajorant T γ δ c)‖ := by
  let W := (n07aMaterialJetMajorant_memLp hT hγδ c).toLp
    (n07aMaterialJetMajorant T γ δ c)
  calc
    _ ≤ ‖G k (x, v) • W‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [n07aWeightedJetLpTower_D_ae hT hU hf J hγδ a b c G hG hb k hx v,
        Lp.coeFn_smul (G k (x, v)) W,
        (n07aMaterialJetMajorant_memLp hT hγδ c).coeFn_toLp] with p hp hsmul hW
      rw [hp, hsmul, Pi.smul_apply, smul_eq_mul, hW, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg hG0,
        abs_of_nonneg (n07aMaterialJetMajorant_nonneg hT γ δ c p)]
      exact hb k x hx v p
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hG0]

end LpTower

end ContinuousFlexibility.Analysis
