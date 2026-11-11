import ContinuousFlexibility.Analysis.N08ControlSpatialBounds
import ContinuousFlexibility.Analysis.N08MaterialFamilyBounds
import ContinuousFlexibility.Scalar.WeightedWeightShiftJets

/-!
# Decaying material jets of the actual radial family

One fixed positive weight is chosen before all derivative orders. Passing
to the actual material radius preserves ordinary decay, and derivatives of
the normalizing height factor preserve its power. A remaining positive
power absorbs every material-envelope order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

def n08WeakControlWeight : ℝ := 3 / 256

theorem n08WeakControlWeight_pos : 0 < n08WeakControlWeight := by
  norm_num [n08WeakControlWeight]

variable {D : ReferenceData} {T : MaterialData}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ → ℝ}

def n08RadialFamilyField {E : Type*} (F : E → ℝ → ℝ) (u : E) (p : PolarPoint) : ℝ :=
  F u p.1

def n08RadialFamilyPullback (T : MaterialData) {E : Type*}
    (F : E → ℝ → ℝ) (u : E) (x : ℝ) : ℝ :=
  T.H (T.radius x) ^ (-n08WeakControlWeight) * F u (T.radius x)

theorem n08RadialFamily_material_jet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      |iteratedDeriv a (fun t => F u (T.radius t)) x| ≤
        K * ‖u‖ * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) := by
  apply n08_comp_materialRadius_majorant hT
    hF (fun u => norm_nonneg u)
    (fun r hr => mul_nonneg (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
      (zero_le_one.trans (hT.2.1 r hr).2.2.2))
  intro n
  obtain ⟨K, hK, hKb⟩ := hB n
  exact ⟨K, hK, fun u r hr => (hKb u r hr).trans_eq (by ring)⟩

theorem n08RadialFamilyPullback_jet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      |iteratedDeriv a (n08RadialFamilyPullback T F u) x| ≤
        K * ‖u‖ * T.H (T.radius x) ^ n08WeakControlWeight * T.M (T.radius x) := by
  have hinside := hT.2.2.2.2.2.2.2.1
  have hradius := hT.2.2.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ (univ : Set ℝ),
      |iteratedDeriv j (fun t => T.H (T.radius t) ^ (-n08WeakControlWeight)) x| ≤
        K * T.H (T.radius x) ^ (-n08WeakControlWeight) := by
    obtain ⟨K, hK, hKb⟩ := iteratedDeriv_materialH_rpow_bound hT (-n08WeakControlWeight) j
    exact ⟨K, hK, fun x _ => hKb x⟩
  have hbG (j : ℕ) (_ : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      x ∈ (univ : Set ℝ) →
      |iteratedDeriv j (fun t => F u (T.radius t)) x| ≤
        K * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) * ‖u‖ := by
    obtain ⟨K, hK, hKb⟩ := n08RadialFamily_material_jet_bound hT hF hB j
    exact ⟨K, hK, fun u x _ => (hKb u x).trans_eq (by ring)⟩
  obtain ⟨K, hK, hKb⟩ := n08_product_jet_majorant
    (f := fun x => T.H (T.radius x) ^ (-n08WeakControlWeight))
    (g := fun u x => F u (T.radius x))
    (W := fun x => T.H (T.radius x) ^ (-n08WeakControlWeight))
    (V := fun x => T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x))
    (P := fun u : E => ‖u‖) isOpen_univ
    (contDiff_materialH_rpow hT (-n08WeakControlWeight)).contDiffOn
    (fun u => ((hF u).comp_contDiff
      hradius (fun x => (hinside x).1)).contDiffOn)
    (fun x _ => Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
      (zero_le_one.trans (hT.2.1 _ (hinside x).1).2.2.2))
    (fun u => norm_nonneg u) a hbF hbG
  refine ⟨K, hK, fun u x => (hKb u x (mem_univ x)).trans_eq ?_⟩
  have hp := (hT.2.1 _ (hinside x).1).2.1
  have hpow : T.H (T.radius x) ^ (-n08WeakControlWeight) *
      T.H (T.radius x) ^ (3 / 128 : ℝ) = T.H (T.radius x) ^ n08WeakControlWeight := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num [n08WeakControlWeight]
  calc
    _ = K * ‖u‖ * (T.H (T.radius x) ^ (-n08WeakControlWeight) *
        T.H (T.radius x) ^ (3 / 128 : ℝ)) * T.M (T.radius x) := by ring
    _ = _ := by rw [hpow]

theorem n08_mixedDerivative_radial (f : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q.1) p =
      if b = 0 then iteratedDeriv a f p.1 else 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [mixedDerivative, iteratedDeriv_zero, if_pos rfl]
  · have hz : (fun r : ℝ => iteratedDeriv b (fun _ : ℝ => f r) p.2) = (0 : ℝ → ℝ) := by
      funext r
      simp only [iteratedDeriv_const, if_neg hb, Pi.zero_apply]
    change iteratedDeriv a (fun r => iteratedDeriv b (fun _ => f r) p.2) p.1 = _
    rw [hz, iteratedDeriv_const_zero, if_neg hb]

/-- Every actual weighted material jet has one common integrable majorant,
up to a constant depending only on its order and the weak-vector norm. -/
theorem n08RadialFamilyField_weightedJet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * ‖u‖ * T.H r ^ (3 / 128 : ℝ) * T.M r) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ p : PolarPoint,
      |weightedPhysicalJet T n08WeakControlWeight a b c (n08RadialFamilyField F u) p| ≤
        K * ‖u‖ * T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) := by
  obtain ⟨K, hK, hKb⟩ := n08RadialFamilyPullback_jet_bound hT hF hB a
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv ((c + 1 : ℕ) : ℝ)
    (n08WeakControlWeight / 2) (half_pos n08WeakControlWeight_pos)
  refine ⟨K * A, mul_nonneg hK hA.le, fun u p => ?_⟩
  have hp := hpos _ (hinside p.1).1
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans hp.2.2.2
  have hH : 0 < T.H (T.radius p.1) := hp.2.1
  change |T.M (T.radius p.1) ^ c *
    mixedDerivative a b (fun q => n08RadialFamilyPullback T F u q.1) p| ≤ _
  rw [n08_mixedDerivative_radial]
  by_cases hb : b = 0
  · rw [if_pos hb, abs_mul, abs_of_nonneg (pow_nonneg hM _)]
    have hpay : T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) *
        T.M (T.radius p.1) ^ (c + 1) ≤ A := by
      simpa only [Real.rpow_natCast] using hAb _ (hinside p.1).1
    have hpow : T.H (T.radius p.1) ^ n08WeakControlWeight =
        T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) *
          T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) := by
      rw [← Real.rpow_add hH]
      congr 1
      ring
    calc
      _ ≤ T.M (T.radius p.1) ^ c *
          (K * ‖u‖ * T.H (T.radius p.1) ^ n08WeakControlWeight * T.M (T.radius p.1)) :=
        mul_le_mul_of_nonneg_left (hKb u p.1) (pow_nonneg hM _)
      _ = K * ‖u‖ *
          (T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) * T.M (T.radius p.1) ^ (c + 1)) *
          T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) := by rw [hpow, pow_succ]; ring
      _ ≤ K * ‖u‖ * A * T.H (T.radius p.1) ^ (n08WeakControlWeight / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpay (mul_nonneg hK (norm_nonneg _)))
          (Real.rpow_pos_of_pos hH _).le
      _ = _ := by ring
  · rw [if_neg hb, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hA.le) (norm_nonneg _))
      (Real.rpow_pos_of_pos hH _).le

end ContinuousFlexibility.Statements
