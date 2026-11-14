module

public import ContinuousFlexibility.Analysis.CoupledPositiveWeightBounds
public import ContinuousFlexibility.Scalar.WeightedWeightShiftJets

/-!
# Material jets of radial families with a fixed grading loss

A positive ordinary decay power survives composition with the material
radius and the height normalization. The source majorants may grow with
the derivative order; only monotonicity is used, so this applies directly
to the actual state grading.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

def coupledWeakProfileWeight : ℝ := 3 / 256

theorem coupledWeakProfileWeight_pos : 0 < coupledWeakProfileWeight := by
  norm_num [coupledWeakProfileWeight]

def coupledRadialFamilyField {E : Type*} (F : E → ℝ → ℝ) (u : E) (p : PolarPoint) : ℝ :=
  F u p.1

def coupledRadialFamilyPullback (T : MaterialData) {E : Type*}
    (F : E → ℝ → ℝ) (u : E) (x : ℝ) : ℝ :=
  T.H (T.radius x) ^ (-coupledWeakProfileWeight) * F u (T.radius x)

variable {D : ReferenceData} {T : MaterialData} {E : Type*}
  {F : E → ℝ → ℝ} {P : ℕ → E → ℝ}

theorem coupledRadialFamily_material_jet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      |iteratedDeriv a (fun t => F u (T.radius t)) x| ≤
        K * P a u * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) := by
  have hW (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      0 ≤ T.H r ^ (3 / 128 : ℝ) * T.M r :=
    mul_nonneg (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _)
      (zero_le_one.trans (hT.2.1 r hr).2.2.2)
  apply coupled_comp_materialRadius_majorant hT hF (hP a) hW a
  intro n hn
  obtain ⟨K, hK, hKb⟩ := hB n
  refine ⟨K, hK, fun u r hr => ?_⟩
  calc
    _ ≤ K * P n u * T.H r ^ (3 / 128 : ℝ) * T.M r := hKb u r hr
    _ = K * P n u * (T.H r ^ (3 / 128 : ℝ) * T.M r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmono hn u) hK) (hW r hr)

theorem coupledRadialFamilyPullback_jet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      |iteratedDeriv a (coupledRadialFamilyPullback T F u) x| ≤
        K * P a u * T.H (T.radius x) ^ coupledWeakProfileWeight * T.M (T.radius x) := by
  have hinside := hT.2.2.2.2.2.2.2.1
  have hradius := hT.2.2.2.2.2.2.1
  have hbF (j : ℕ) (_ : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ (univ : Set ℝ),
      |iteratedDeriv j (fun t => T.H (T.radius t) ^ (-coupledWeakProfileWeight)) x| ≤
        K * T.H (T.radius x) ^ (-coupledWeakProfileWeight) := by
    obtain ⟨K, hK, hKb⟩ := iteratedDeriv_materialH_rpow_bound hT (-coupledWeakProfileWeight) j
    exact ⟨K, hK, fun x _ => hKb x⟩
  have hbG (j : ℕ) (hj : j ≤ a) : ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ x,
      x ∈ (univ : Set ℝ) →
      |iteratedDeriv j (fun t => F u (T.radius t)) x| ≤
        K * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) * P a u := by
    obtain ⟨K, hK, hKb⟩ := coupledRadialFamily_material_jet_bound hT hF hP hmono hB j
    refine ⟨K, hK, fun u x _ => ?_⟩
    calc
      _ ≤ K * P j u * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) := hKb u x
      _ = K * (T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x)) * P j u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmono hj u)
        (mul_nonneg hK (mul_nonneg
          (Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
          (zero_le_one.trans (hT.2.1 _ (hinside x).1).2.2.2)))
  obtain ⟨K, hK, hKb⟩ := coupled_product_jet_majorant
    (f := fun x => T.H (T.radius x) ^ (-coupledWeakProfileWeight))
    (g := fun u x => F u (T.radius x))
    (W := fun x => T.H (T.radius x) ^ (-coupledWeakProfileWeight))
    (V := fun x => T.H (T.radius x) ^ (3 / 128 : ℝ) * T.M (T.radius x))
    (P := P a) isOpen_univ
    (contDiff_materialH_rpow hT (-coupledWeakProfileWeight)).contDiffOn
    (fun u => ((hF u).comp_contDiff
      hradius (fun x => (hinside x).1)).contDiffOn)
    (fun x _ => Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hT.2.1 _ (hinside x).1).2.1.le _)
      (zero_le_one.trans (hT.2.1 _ (hinside x).1).2.2.2))
    (hP a) a hbF hbG
  refine ⟨K, hK, fun u x => (hKb u x (mem_univ x)).trans_eq ?_⟩
  have hp := (hT.2.1 _ (hinside x).1).2.1
  have hpow : T.H (T.radius x) ^ (-coupledWeakProfileWeight) *
      T.H (T.radius x) ^ (3 / 128 : ℝ) = T.H (T.radius x) ^ coupledWeakProfileWeight := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num [coupledWeakProfileWeight]
  calc
    _ = K * P a u * (T.H (T.radius x) ^ (-coupledWeakProfileWeight) *
        T.H (T.radius x) ^ (3 / 128 : ℝ)) * T.M (T.radius x) := by ring
    _ = _ := by rw [hpow]

theorem coupled_mixedDerivative_radial (f : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q.1) p =
      if b = 0 then iteratedDeriv a f p.1 else 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [mixedDerivative, iteratedDeriv_zero, ite_true]
  · have hz : (fun r : ℝ => iteratedDeriv b (fun _ : ℝ => f r) p.2) = (0 : ℝ → ℝ) := by
      funext r
      simp only [iteratedDeriv_const, if_neg hb, Pi.zero_apply]
    change iteratedDeriv a (fun r => iteratedDeriv b (fun _ => f r) p.2) p.1 = _
    rw [hz, iteratedDeriv_const_zero, if_neg hb]

/-- The remaining positive power absorbs all envelope orders. -/
theorem coupledRadialFamilyField_weightedJet_bound
    (hT : IsMaterialData D T)
    (hF : ∀ u, ContDiffOn ℝ ∞ (F u) (Ioo D.a D.b))
    (hP : ∀ n u, 0 ≤ P n u) (hmono : Monotone P)
    (hB : ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ r ∈ Ioo D.a D.b,
      |iteratedDeriv s (F u) r| ≤ K * P s u * T.H r ^ (3 / 128 : ℝ) * T.M r) (a b c : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : E, ∀ p : PolarPoint,
      |weightedPhysicalJet T coupledWeakProfileWeight a b c (coupledRadialFamilyField F u) p| ≤
        K * P a u * T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) := by
  obtain ⟨K, hK, hKb⟩ := coupledRadialFamilyPullback_jet_bound hT hF hP hmono hB a
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _, _, _, _, henv, _⟩ := hdata
  obtain ⟨A, hA, hAb, _, _⟩ := henv ((c + 1 : ℕ) : ℝ)
    (coupledWeakProfileWeight / 2) (half_pos coupledWeakProfileWeight_pos)
  refine ⟨K * A, mul_nonneg hK hA.le, fun u p => ?_⟩
  have hp := hpos _ (hinside p.1).1
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans hp.2.2.2
  have hH : 0 < T.H (T.radius p.1) := hp.2.1
  change |T.M (T.radius p.1) ^ c *
    mixedDerivative a b (fun q => coupledRadialFamilyPullback T F u q.1) p| ≤ _
  rw [coupled_mixedDerivative_radial]
  by_cases hb : b = 0
  · rw [if_pos hb, abs_mul, abs_of_nonneg (pow_nonneg hM _)]
    have hpay : T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) *
        T.M (T.radius p.1) ^ (c + 1) ≤ A := by
      simpa only [Real.rpow_natCast] using hAb _ (hinside p.1).1
    have hpow : T.H (T.radius p.1) ^ coupledWeakProfileWeight =
        T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) *
          T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) := by
      rw [← Real.rpow_add hH]
      congr 1
      ring
    calc
      _ ≤ T.M (T.radius p.1) ^ c *
          (K * P a u * T.H (T.radius p.1) ^ coupledWeakProfileWeight * T.M (T.radius p.1)) :=
        mul_le_mul_of_nonneg_left (hKb u p.1) (pow_nonneg hM _)
      _ = K * P a u *
          (T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) * T.M (T.radius p.1) ^ (c + 1)) *
          T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) := by rw [hpow, pow_succ]; ring
      _ ≤ K * P a u * A * T.H (T.radius p.1) ^ (coupledWeakProfileWeight / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpay (mul_nonneg hK (hP a u)))
          (Real.rpow_pos_of_pos hH _).le
      _ = _ := by ring
  · rw [if_neg hb, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hA.le) (hP a u))
      (Real.rpow_pos_of_pos hH _).le

end ContinuousFlexibility.Statements
