import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryPlaneWords
import ContinuousFlexibility.Analysis.N04PositiveGeometrySavedKernelWords
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# The actual finite coefficient packet on the plane

The boundary coefficients are paired with the fixed physical radius.
This operation retains both parameter seminorm boxes and the saved
positive spatial order. A finite kernel can then be applied to this
same genuine packet tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F Z : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem N04BoundaryWordBounds.scalarPi {ι : Type*} [Fintype ι]
    {U : Set E} (hU : IsOpen U) {f : ι → E × ℝ → F}
    (J : ∀ i, SmoothDirections (U ×ˢ univ) (f i))
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hf : ∀ i, N04BoundaryWordBounds (J i) K s d x θ P M H t shift) :
    N04BoundaryWordBounds (smoothDirectionsScalarPi (hU.prod isOpen_univ) J)
      K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _))).mpr
  intro i
  exact hf i n w hk ha v hv hp

def n04PositiveGeometry_coefficientPacketDirections
    {U : Set E} {f : E × ℝ → F} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) f) :
    SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (f (z.1, z.2.2), z.2.1)) := by
  let L : (E × PolarPoint) →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hL (z : E × PolarPoint) : L z = (z.1, z.2.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  let JA : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => f (z.1, z.2.2)) :=
    (J.compLinear L (hU.prod isOpen_univ)
      (fun z hz => by rw [hL]; exact ⟨hz.1, mem_univ _⟩)).congrOn
      (fun z _ => congrArg f (hL z))
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => z.2.1) :=
    (smoothDirectionsLinearOn R (hU.prod isOpen_univ)).congrOn (fun z _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  exact smoothDirectionsProd JA JR

theorem n04PositiveGeometry_coefficientPacket_saved_word_bound
    {U : Set E} {f : E × ℝ → F} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) f)
    (Q : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (f (z.1, z.2.2), z.2.1)))
    (p q : Seminorm ℝ E) {R M H t : ℝ}
    (hR : 0 ≤ R) (hM : 1 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (K s shift : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint)
    (hbound : N04BoundaryWordBounds J K s 1 x y.2
      (fun a => p a ≤ 1 ∧ q a ≤ R) M H t shift)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n)
    (hk : w.stateArity ≤ K) (ha : w.angleArity ≤ s + 1)
    (v : Fin n → E × PolarPoint)
    (hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0)
    (hbox : ∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) :
    ‖Q.D n (x, y) v‖ ≤ M * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  let QA := smoothDirections_postcompCLM Q (ContinuousLinearMap.fst ℝ F ℝ)
  let QR := smoothDirections_postcompCLM Q (ContinuousLinearMap.snd ℝ F ℝ)
  have hb := n04PositiveGeometry_boundaryPlane_saved_word_bound hU J QA p q hR
    (zero_le_one.trans hM) hH ht K s shift x hx y hbound hn w hk ha v hpure hbox
  have hr := n04PositiveGeometry_spatialLinear_saved_word_bound (hU.prod isOpen_univ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) QR hM
    ((ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ).trans hM) hH ht hn w (shift + 1)
    (x, y) ⟨hx, mem_univ _⟩ v (fun i => (hbox i).2.2)
    (fun i hi => by simpa only [hi, if_true] using hpure i)
  exact n04PositiveGeometry_jointPair_word_bound QA QR Q n (x, y)
    ⟨hx, mem_univ _⟩ v hb hr

theorem n04PositiveGeometry_boundaryKernel_plane_saved_bound
    {U : Set E} {V : Set (F × ℝ)} {f : E × ℝ → F} {g : F × ℝ → Z}
    (hU : IsOpen U) (J : SmoothDirections (U ×ˢ univ) f)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo (fun z : E × PolarPoint => (f (z.1, z.2.2), z.2.1)) (U ×ˢ univ) V)
    (Q : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => g (f (z.1, z.2.2), z.2.1)))
    (p q : Seminorm ℝ E) {R A M H t : ℝ}
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hM : 1 ≤ M) (hH : 0 ≤ H) (hHM : H ≤ M) (ht : 1 ≤ t)
    (K s shift : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint)
    (hbound : N04BoundaryWordBounds J K (s + K) 1 x y.2
      (fun a => p a ≤ 1 ∧ q a ≤ R) M H t shift)
    {n : ℕ} (hn : 0 < n) (hns : n ≤ K + s + 1) (w : StateAngleWord n)
    (hk : w.stateArity ≤ K)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f (x, y.2), y.1)‖ ≤ A)
    (v : Fin n → E × PolarPoint)
    (hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0)
    (hbox : ∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) :
    ‖Q.D n (x, y) v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      A * M ^ n * M ^ n * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  let JP := n04PositiveGeometry_coefficientPacketDirections hU J
  apply n04PositiveGeometry_finiteKernel_savedWord_bound JP hV hg hmap Q
    hn w (shift + 1) (Nat.succ_pos shift) (x, y) ⟨hx, mem_univ _⟩ v
    hA hM hH hHM ht houter
  intro π i
  have hk' : (w.restrict (π.emb i)).stateArity ≤ K :=
    ((Finset.single_le_sum (fun j _ => Nat.zero_le
      (w.restrict (π.emb j)).stateArity) (Finset.mem_univ i)).trans_eq
        (w.sum_restrict_stateArity π)).trans hk
  have ha' : (w.restrict (π.emb i)).angleArity ≤ (s + K) + 1 := by
    have hsum := (w.restrict (π.emb i)).arity_sum
    have hpart := π.partSize_le i
    omega
  exact n04PositiveGeometry_coefficientPacket_saved_word_bound hU J JP p q hR hM hH ht
    K (s + K) shift x hx y hbound (π.partSize_pos i) (w.restrict (π.emb i)) hk' ha'
    (v ∘ π.emb i)
    (fun j => by
      simpa only [StateAngleWord.isState_restrict, comp_apply] using hpure (π.emb i j))
    (fun j => hbox (π.emb i j))

end ContinuousFlexibility.Analysis
