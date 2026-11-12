import ContinuousFlexibility.Analysis.ReturnChartUniformBounds

/-!
# Uniform angular jets of the actual interpolation inverse

Every interpolation parameter in `[0,1]` shares the same positive
derivative interval and the same finite-order angular bounds. Thus a
radial cutoff can choose its value freely in that interval without
changing these angular estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

theorem returnInterpolation_contDiff {K : ℝ → ℝ}
    (hK : ContDiff ℝ ∞ K) (t : ℝ) : ContDiff ℝ ∞ (returnInterpolation t K) :=
  contDiff_id.add (contDiff_const.mul (hK.sub contDiff_id))

theorem returnInterpolation_deriv_bounds
    {K : ℝ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hbound : ∀ θ, 1 / 12 ≤ deriv K θ ∧ deriv K θ ≤ 12)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    1 / 12 ≤ deriv (returnInterpolation t K) θ ∧
      deriv (returnInterpolation t K) θ ≤ 12 := by
  rw [(returnInterpolation_hasDerivAt ((hK.differentiable (by simp) θ).hasDerivAt)).deriv]
  have hlo := mul_nonneg ht.1 (sub_nonneg.mpr (hbound θ).1)
  have hhi := mul_nonneg ht.1 (sub_nonneg.mpr (hbound θ).2)
  constructor <;> nlinarith only [hlo, hhi, ht.2]

theorem returnInterpolation_positive_jets_uniform
    {ι : Type*} (K : ι → ℝ → ℝ) (hK : ∀ i, ContDiff ℝ ∞ (K i))
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv n (K i) θ| ≤ A) :
    ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ i t, t ∈ Icc (0 : ℝ) 1 → ∀ θ,
        |iteratedDeriv n (returnInterpolation t (K i)) θ| ≤ A := by
  intro n hn
  obtain ⟨A, hA, hb⟩ := hbound n hn
  refine ⟨A + 2, by positivity, fun i t ht θ => ?_⟩
  have hid : |iteratedDeriv n (fun x : ℝ => x) θ| ≤ 1 := by
    rw [iteratedDeriv_fun_id, if_neg (by omega : n ≠ 0)]
    split <;> norm_num
  have heq : returnInterpolation t (K i) = fun x => x + t * (K i x - x) := rfl
  have hsubreg : ContDiffAt ℝ (n : ℕ∞ω) (fun x : ℝ => K i x - x) θ :=
    ((hK i).sub contDiff_id).contDiffAt.of_le (by simp)
  have hmulreg : ContDiffAt ℝ (n : ℕ∞ω) (fun x : ℝ => t * (K i x - x)) θ :=
    contDiffAt_const.mul hsubreg
  rw [heq, iteratedDeriv_fun_add (f := fun x : ℝ => x)
      (g := fun x : ℝ => t * (K i x - x)) (n := n) (x := θ) contDiffAt_id hmulreg,
    iteratedDeriv_const_mul (f := fun x : ℝ => K i x - x) t hsubreg,
    iteratedDeriv_fun_sub (f := K i) (g := fun x : ℝ => x) (n := n) (x := θ)
      ((hK i).contDiffAt.of_le (by simp)) contDiffAt_id]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg ht.1]
  have hsub : |iteratedDeriv n (K i) θ - iteratedDeriv n (fun x : ℝ => x) θ| ≤ A + 1 :=
    (abs_sub _ _).trans (add_le_add (hb i θ) hid)
  have hmul := mul_le_mul ht.2 hsub (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith only [hid, hmul]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem N01Properties.returnInterpolation_inverse_positive_jets_uniform
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1)
    (hKlow : ∀ m θ, 1 / 12 ≤ deriv (returnCorrectionInitialMap S C z m) θ ∧
      deriv (returnCorrectionInitialMap S C z m) θ ≤ 12)
    (hKbound : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv n (returnCorrectionInitialMap S C z m) θ| ≤ A) :
    ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ m t, t ∈ Icc (0 : ℝ) 1 → ∀ θ,
        |iteratedDeriv n
          (Function.invFun (returnInterpolation t (returnCorrectionInitialMap S C z m))) θ| ≤ A := by
  let I := ℕ × {t : ℝ // t ∈ Icc (0 : ℝ) 1}
  let F (i : I) : ℝ → ℝ := returnInterpolation i.2.val (returnCorrectionInitialMap S C z i.1)
  let G (i : I) : ℝ → ℝ := Function.invFun (F i)
  have hK (m : ℕ) := hN.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  have hF (i : I) : ContDiff ℝ ∞ (F i) := returnInterpolation_contDiff (hK i.1) i.2.val
  have hpos (i : I) (θ : ℝ) : 0 < deriv (F i) θ :=
    (by norm_num : (0 : ℝ) < 1 / 12).trans_le
      (returnInterpolation_deriv_bounds (hK i.1) (hKlow i.1) i.2.property θ).1
  have hinj (i : I) : Function.Injective (F i) := (strictMono_of_deriv_pos (hpos i)).injective
  have hsurj (i : I) : Function.Surjective (F i) := returnLift_surjective Real.pi_pos
    (hF i).continuous (returnInterpolation_periodic_lift
      (hN.returnCorrectionInitialMap_add_period hz hsector i.1) i.2.val)
  have hforward (n : ℕ) (hn : 1 ≤ n) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ i θ, |iteratedDeriv n (F i) θ| ≤ A := by
    obtain ⟨A, hA, hb⟩ := returnInterpolation_positive_jets_uniform
      (returnCorrectionInitialMap S C z) hK hKbound n hn
    exact ⟨A, hA, fun i θ => hb i.1 i.2.val i.2.property θ⟩
  intro n hn
  obtain ⟨A, hA, hb⟩ := inverse_iteratedDeriv_uniform_bound F G hF
    (by norm_num : (0 : ℝ) < 1 / 12)
    (fun i θ => (returnInterpolation_deriv_bounds (hK i.1) (hKlow i.1) i.2.property θ).1)
    (fun i θ => Function.leftInverse_invFun (hinj i) θ)
    (fun i θ => Function.rightInverse_invFun (hsurj i) θ) hforward n hn
  exact ⟨A, hA, fun m t ht θ => hb (m, ⟨t, ht⟩) θ⟩

theorem N01Properties.exists_uniform_interpolation_inverse_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
      ∀ m t, t ∈ Icc (0 : ℝ) 1 → ∀ θ,
        |iteratedDeriv n
          (Function.invFun (returnInterpolation t (returnCorrectionInitialMap S C z m))) θ| ≤ A := by
  obtain ⟨base', ε', hb, hε', hεε, hnew, hcharts⟩ :=
    hN.exists_uniform_returnChart_angular_jets hS hT
  refine ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector => ?_⟩
  apply hnew.returnInterpolation_inverse_positive_jets_uniform hS hT hz hsector
    (hcharts z hz hsector).1
  intro n hn
  obtain ⟨A, hA, hbound⟩ := (hcharts z hz hsector).2 n hn
  exact ⟨A, hA, fun m θ => (hbound m θ).2.2⟩

end ContinuousFlexibility.Statements

