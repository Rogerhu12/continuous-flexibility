module

public import ContinuousFlexibility.Analysis.ReturnResidualAngularWeightedBounds
public import ContinuousFlexibility.Analysis.ReturnInterpolationJetBounds
public import ContinuousFlexibility.Analysis.ScalarVelocityWeightedJets

/-!
# Weighted angular jets of the actual independent correction velocity

Both actual inverse coordinates have uniformly bounded positive angular
jets on one N01 neighborhood. Substitution into the actual displacement
and multiplication by the actual flow variation therefore preserve its
height weight. The cutoff derivative remains an explicit scalar factor;
the theorem applies to the same optical cutoffs used for positivity and
source compatibility.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem returnCorrectionDriftSpeedLinear_angular_bound_of_velocity
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (ρ : CircleSpace S)
    (n : ℕ) (m : ℕ) (r θ A : ℝ)
    (hv : ContDiff ℝ ∞ (fun t =>
      returnCorrectionVelocityLinear D S C χ z m (r, t) ρ))
    (hb : ∀ t, |iteratedDeriv n (fun u =>
      returnCorrectionVelocityLinear D S C χ z m (r, u) ρ) t| ≤ A) :
    |iteratedDeriv n (fun t => returnCorrectionDriftLinear D S C χ z m (r, t) ρ) θ| ≤ A ∧
      |iteratedDeriv n (fun t => returnCorrectionSpeedLinear D S C χ z m (r, t) ρ) θ| ≤ A := by
  have hd : (fun t => returnCorrectionDriftLinear D S C χ z m (r, t) ρ) =
      fun t => (returnCorrectionVelocityLinear D S C χ z m (r, t) ρ -
        returnCorrectionVelocityLinear D S C χ z m (r, -t) ρ) / 2 :=
    funext (fun t => returnCorrectionDriftLinear_apply D S C χ z m (r, t) ρ)
  have hs : (fun t => returnCorrectionSpeedLinear D S C χ z m (r, t) ρ) =
      fun t => (-returnCorrectionVelocityLinear D S C χ z m (r, -t) ρ -
        returnCorrectionVelocityLinear D S C χ z m (r, t) ρ) / 2 :=
    funext (fun t => returnCorrectionSpeedLinear_apply D S C χ z m (r, t) ρ)
  rw [hd, hs]
  exact iteratedDeriv_reflected_drift_speed_abs_le hv n hb θ

section ActualVelocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (hflow : ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
    1 / 2 ≤ deriv (C.minusFlow z m r) θ ∧ deriv (C.minusFlow z m r) θ ≤ 3 / 2)
  (hinverse : ∀ n : ℕ, 1 ≤ n → ∃ A : ℝ, 0 ≤ A ∧
    (∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |iteratedDeriv n (Function.invFun (C.minusFlow z m r)) θ| ≤ A) ∧
    (∀ m θ, |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ A))

include hN hS hT hz hsector hflow hinverse

theorem N01Properties.returnCorrectionVelocityLinear_angular_weighted_bounds
    (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) :
    (∀ m r, r ∈ Icc (C.left m) (C.right m) →
      ContDiff ℝ ∞ (fun θ => returnCorrectionVelocityLinear D S C χ z m (r, θ) ρ)) ∧
    ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        |iteratedDeriv n (fun t => returnCorrectionVelocityLinear D S C χ z m (r, t) ρ) θ| ≤
          A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hend (m : ℕ) (θ : ℝ) :
      1 / 2 ≤ deriv (C.minusFlow z m (C.right m)) θ ∧
        deriv (C.minusFlow z m (C.right m)) θ ≤ 3 / 2 :=
    hflow m (C.right m) ⟨(hC.1 m).2.1.le, le_rfl⟩ θ
  have hret (n : ℕ) (hn : 1 ≤ n) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ m θ, |iteratedDeriv n (C.minusReturnInverse z m) θ| ≤ A := by
    obtain ⟨A, hA, _, hb⟩ := hinverse n hn
    exact ⟨A, hA, hb⟩
  have hKlow := hN.returnCorrectionInitialMap_deriv_bounds hz hsector hend
  have hKbound := hN.returnCorrectionInitialMap_positive_jets_uniform
    hS hT hz hsector hend hret
  have hJbound := hN.returnInterpolation_inverse_positive_jets_uniform
    hS hT hz hsector hKlow hKbound
  let I := Σ m : ℕ, {r : ℝ // r ∈ Icc (C.left m) (C.right m)}
  let f (i : I) : ℝ → ℝ := C.minusFlow z i.1 i.2.val
  let a (i : I) : ℝ → ℝ := Function.invFun (f i)
  let J (i : I) : ℝ → ℝ :=
    returnInterpolation (χ i.1 i.2.val) (returnCorrectionInitialMap S C z i.1)
  let b (i : I) : ℝ → ℝ := Function.invFun (J i)
  let d (i : I) : ℝ → ℝ := fun θ => returnCorrectionDisplacementLinear S C z i.1 θ ρ
  let c (i : I) : ℝ := deriv (χ i.1) i.2.val
  let W (i : I) : ℝ := T.H (T.sample i.1) ^ (3 / 4 : ℝ)
  have hH := (material_circle_sample_weights_pos hT hN.1.1).2
  have hW (i : I) : 0 < W i := Real.rpow_pos_of_pos (hH i.1) _
  have hf (i : I) : ContDiff ℝ ∞ (f i) :=
    hN.minusFlow_angular_contDiff hS hT hz hsector i.1 i.2.property
  have hfpos (i : I) (θ : ℝ) : 0 < deriv (f i) θ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (hflow i.1 i.2.val i.2.property θ).1
  have hfi (i : I) : Function.Injective (f i) :=
    (strictMono_of_deriv_pos (hfpos i)).injective
  have hfs (i : I) : Function.Surjective (f i) :=
    returnLift_surjective Real.pi_pos (hf i).continuous
      (hN.minusFlow_add_period hz i.1 i.2.property)
  have ha (i : I) : ContDiff ℝ ∞ (a i) :=
    returnChart_inverse_contDiff (f i) (a i) (hf i) (hfpos i)
      (Function.leftInverse_invFun (hfi i)) (Function.rightInverse_invFun (hfs i))
  have hJ (i : I) : ContDiff ℝ ∞ (J i) :=
    returnInterpolation_contDiff
      (hN.returnCorrectionInitialMap_contDiff hS hT hz hsector i.1) (χ i.1 i.2.val)
  have hJpos (i : I) (θ : ℝ) : 0 < deriv (J i) θ :=
    (by norm_num : (0 : ℝ) < 1 / 12).trans_le
      (returnInterpolation_deriv_bounds
        (hN.returnCorrectionInitialMap_contDiff hS hT hz hsector i.1)
        (hKlow i.1) (hχ i.1 i.2.val i.2.property) θ).1
  have hJi (i : I) : Function.Injective (J i) :=
    (strictMono_of_deriv_pos (hJpos i)).injective
  have hJs (i : I) : Function.Surjective (J i) := returnLift_surjective Real.pi_pos
    (hJ i).continuous (returnInterpolation_periodic_lift
      (hN.returnCorrectionInitialMap_add_period hz hsector i.1) (χ i.1 i.2.val))
  have hb (i : I) : ContDiff ℝ ∞ (b i) :=
    returnChart_inverse_contDiff (J i) (b i) (hJ i) (hJpos i)
      (Function.leftInverse_invFun (hJi i)) (Function.rightInverse_invFun (hJs i))
  have hd (i : I) : ContDiff ℝ ∞ (d i) :=
    hN.returnCorrectionDisplacementLinear_contDiff hS hT hz hsector i.1 ρ
  have hfb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (f i) θ| ≤ A := by
    obtain ⟨A, hA, hb⟩ := hN.minusFlow_angular_iteratedDeriv_uniform_bound hS hT hz hsector k hk
    exact ⟨A, hA, fun i θ => hb i.1 i.2.val i.2.property θ⟩
  have hab (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (a i) θ| ≤ A := by
    obtain ⟨A, hA, hb, _⟩ := hinverse k hk
    exact ⟨A, hA, fun i θ => hb i.1 i.2.val i.2.property θ⟩
  have hbb (k : ℕ) (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (b i) θ| ≤ A := by
    obtain ⟨A, hA, hb⟩ := hJbound k hk
    exact ⟨A, hA, fun i θ => hb i.1 (χ i.1 i.2.val) (hχ i.1 i.2.val i.2.property) θ⟩
  have hdb (k : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
      ∀ i θ, |iteratedDeriv k (d i) θ| ≤ A * W i := by
    obtain ⟨A, hA, hb⟩ := hN.returnCorrectionDisplacementLinear_angular_weighted_bound
      hS hT hz hsector hend hret ρ k
    exact ⟨A, hA, fun i θ => hb i.1 θ⟩
  have hscalar := correctionVelocity_angular_weighted_bound f a b d c W
    hW hf ha hb hd hfb hab hbb hdb
  have heq (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m)) :
      (fun θ => returnCorrectionVelocityLinear D S C χ z m (r, θ) ρ) =
      fun θ => deriv (f ⟨m, ⟨r, hr⟩⟩) (a ⟨m, ⟨r, hr⟩⟩ θ) * c ⟨m, ⟨r, hr⟩⟩ *
        d ⟨m, ⟨r, hr⟩⟩ (b ⟨m, ⟨r, hr⟩⟩ (a ⟨m, ⟨r, hr⟩⟩ θ)) := by
    funext θ
    exact returnCorrectionVelocityLinear_apply D S C χ z m (r, θ) ρ
  refine ⟨fun m r hr => ?_, fun n => ?_⟩
  · rw [heq m r hr]
    exact hscalar.1 ⟨m, ⟨r, hr⟩⟩
  · obtain ⟨A, hA, hb⟩ := hscalar.2 n
    refine ⟨A, hA, fun m r hr θ => ?_⟩
    rw [heq m r hr]
    exact hb ⟨m, ⟨r, hr⟩⟩ θ

theorem N01Properties.returnCorrectionDriftSpeedLinear_angular_weighted_bound
    (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m r, r ∈ Icc (C.left m) (C.right m) → ∀ θ,
      |iteratedDeriv n (fun t => returnCorrectionDriftLinear D S C χ z m (r, t) ρ) θ| ≤
        A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ) ∧
      |iteratedDeriv n (fun t => returnCorrectionSpeedLinear D S C χ z m (r, t) ρ) θ| ≤
        A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  let data := hN.returnCorrectionVelocityLinear_angular_weighted_bounds
    hS hT hz hsector hflow hinverse χ hχ ρ
  let boundData := data.2 n
  let A : ℝ := boundData.choose
  refine ⟨A, boundData.choose_spec.1, fun m r hr θ => ?_⟩
  exact returnCorrectionDriftSpeedLinear_angular_bound_of_velocity D S C χ z ρ n m r θ
    (A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ))
    (data.1 m r hr) (boundData.choose_spec.2 m r hr)

end ActualVelocity

theorem N01Properties.exists_independent_velocity_angular_weighted_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ N01Properties D T S C base' loss ε' ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
      ∀ χ : ℕ → ℝ → ℝ,
        (∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1) →
      ∀ ρ : CircleSpace S, ∀ n : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ m r,
        r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        |iteratedDeriv n (fun t => returnCorrectionDriftLinear D S C χ z m (r, t) ρ) θ| ≤
          A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ) ∧
        |iteratedDeriv n (fun t => returnCorrectionSpeedLinear D S C χ z m (r, t) ρ) θ| ≤
          A * |deriv (χ m) r| * T.H (T.sample m) ^ (3 / 4 : ℝ) := by
  obtain ⟨base', ε', hb, hε', hεε, hnew, hbound⟩ :=
    hN.exists_uniform_inverse_angular_jets hS hT
  exact ⟨base', ε', hb, hε', hεε, hnew, fun z hz hsector χ hχ ρ n =>
    hnew.returnCorrectionDriftSpeedLinear_angular_weighted_bound
      hS hT hz hsector (hbound z hz hsector).1 (hbound z hz hsector).2 χ hχ ρ n⟩

end ContinuousFlexibility.Statements
