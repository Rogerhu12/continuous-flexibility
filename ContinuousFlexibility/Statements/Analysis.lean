import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Analysis.BastianiCurveChain
import ContinuousFlexibility.Analysis.ExponentialSequenceSpace
import ContinuousFlexibility.Analysis.MaterialIntervalWeights
import ContinuousFlexibility.Analysis.TameLinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Precise analysis targets, without proofs of the targets

The six declarations `W01Statement`--`H03Statement` are propositions to be
proved.  The weak graphs below are defined by actual integrals against
smooth tests.  No property named smooth tame, Sobolev, or inverse is left
as an arbitrary predicate supplied by a caller.

Paper correspondence: section 7, lines 22--156; section 8, lines 523--550;
section 9, lines 183--196.  A definition of a target proves no existence.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Pure candidate data. Its asserted properties occur in `IsMaterialData`. -/
structure MaterialData where
  ell : ℝ → ℝ
  H : ℝ → ℝ
  E0 : ℝ → ℝ
  M : ℝ → ℝ
  rho : ℝ → ℝ
  radius : ℝ → ℝ
  sample : ℕ → ℝ

def annularOpen (D : ReferenceData) : Set PolarPoint := Ioo D.a D.b ×ˢ univ

def endpointDistance (D : ReferenceData) (r : ℝ) : ℝ := min (r - D.a) (D.b - r)

def materialDerivative (T : MaterialData) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun r => T.ell r * deriv f r

def materialDerivativeIterate (T : MaterialData) (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (materialDerivative T)^[n] f

def logarithmicDerivativeBounds (D : ReferenceData) (T : MaterialData) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo D.a D.b,
    |materialDerivativeIterate T k (fun t => Real.log (T.H t)) r| ≤ C ∧
    |materialDerivativeIterate T k (fun t => Real.log (T.M t)) r| ≤ C ∧
    |materialDerivativeIterate T k (fun t => Real.log (T.ell t)) r| ≤ C

def RadialMaterialExpansion (D : ReferenceData) (T : MaterialData) : Prop :=
  ∀ n : ℕ, ∃ c : Fin (n + 1) → ℝ → ℝ,
    (∀ j, ContDiffOn ℝ ∞ (c j) (Ioo D.a D.b)) ∧
    (∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ j r, r ∈ Ioo D.a D.b →
      |c j r| ≤ C * T.E0 r ^ A) ∧
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ioo D.a D.b) →
      ∀ r ∈ Ioo D.a D.b,
        iteratedDeriv n f r = ∑ j, c j r * materialDerivativeIterate T j.val f r

/-- The actual endpoint formulas, coordinate, envelopes and discrete-cell comparison. -/
def IsMaterialData (D : ReferenceData) (T : MaterialData) : Prop :=
  (∀ f ∈ ({T.ell, T.H, T.E0, T.M, T.rho} : Set (ℝ → ℝ)),
    ContDiffOn ℝ ∞ f (Ioo D.a D.b)) ∧
  (∀ r ∈ Ioo D.a D.b, 0 < T.ell r ∧ 0 < T.H r ∧ 0 < T.E0 r ∧ 1 ≤ T.M r) ∧
  (∀ r ∈ Ioo D.a D.b, HasDerivAt T.rho (1 / T.ell r) r) ∧
  StrictMonoOn T.rho (Ioo D.a D.b) ∧
  Tendsto T.rho (𝓝[>] D.a) atBot ∧ Tendsto T.rho (𝓝[<] D.b) atTop ∧
  ContDiff ℝ ∞ T.radius ∧
  (∀ x, T.radius x ∈ Ioo D.a D.b ∧ T.rho (T.radius x) = x) ∧
  (∀ r ∈ Ioo D.a D.b, T.radius (T.rho r) = r) ∧
  (∀ x, HasDerivAt T.radius (T.ell (T.radius x)) x) ∧
  (∃ d0 δ : ℝ, 0 < d0 ∧ 0 < δ ∧ δ < min d0 ((D.b - D.a) / 2) ∧
    (∀ r ∈ Ioo D.a (D.a + δ),
      let x := ContinuousFlexibility.Analysis.endpointX d0 (r - D.a)
      T.ell r = (r - D.a) / (1 + x) ∧
      T.H r = ContinuousFlexibility.Analysis.materialH x ∧
      T.E0 r = ContinuousFlexibility.Analysis.materialE0 x ∧
      T.M r = ContinuousFlexibility.Analysis.materialM x) ∧
    (∀ r ∈ Ioo (D.b - δ) D.b,
      let x := ContinuousFlexibility.Analysis.endpointX d0 (D.b - r)
      T.ell r = (D.b - r) / (1 + x) ∧
      T.H r = ContinuousFlexibility.Analysis.materialH x ∧
      T.E0 r = ContinuousFlexibility.Analysis.materialE0 x ∧
      T.M r = ContinuousFlexibility.Analysis.materialM x)) ∧
  (∀ A : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b, T.E0 r ^ A ≤ C * T.M r) ∧
  (∀ A ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    (∀ r ∈ Ioo D.a D.b, T.H r ^ ε * T.M r ^ A ≤ C) ∧
    Tendsto (fun r => T.H r ^ ε * T.M r ^ A) (𝓝[>] D.a) (𝓝 0) ∧
    Tendsto (fun r => T.H r ^ ε * T.M r ^ A) (𝓝[<] D.b) (𝓝 0)) ∧
  logarithmicDerivativeBounds D T ∧ RadialMaterialExpansion D T ∧
  (∀ m, T.sample m ∈ D.cells m) ∧
  (∃ widths : ℕ → ℝ, ∃ K : ℝ, 0 < K ∧
    (∀ m, 0 < widths m ∧
      K⁻¹ * T.E0 (T.sample m) ^ (-K) ≤ widths m ∧
      Icc (T.sample m - widths m) (T.sample m + widths m) ⊆ D.cells m) ∧
    Pairwise (fun m n => Disjoint
      (Ioo (T.sample m - widths m) (T.sample m + widths m))
      (Ioo (T.sample n - widths n) (T.sample n + widths n)))) ∧
  (∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ m r, r ∈ D.cells m →
    |ContinuousFlexibility.Analysis.endpointX 1 (endpointDistance D r) - D.cellIndex m| ≤ C ∧
    (T.H (T.sample m) / T.H r) ≤ C * T.E0 r ^ A ∧
    (T.H r / T.H (T.sample m)) ≤ C * T.E0 r ^ A)

/-- W01: section 7, physical weights and material coordinate, lines 22--59. -/
def W01Statement : Prop :=
  ∀ D : ReferenceData, IsAccumulatingProfile D → ∃ T : MaterialData, IsMaterialData D T

/-! ## Concrete physical and circle norms and their weak graphs -/

def materialCylinderMeasure : Measure PolarPoint :=
  volume.restrict ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) Real.pi)

def angleMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) Real.pi)

abbrev CylinderL2 := Lp ℝ 2 materialCylinderMeasure
abbrev AngleL2 := Lp ℝ 2 angleMeasure

def mixedDerivative (a b : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  iteratedDeriv a (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) p.1

def materialPullback (T : MaterialData) (γ : ℝ) (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => T.H (T.radius p.1) ^ (-γ) * f (T.radius p.1, p.2)

def weightedPhysicalJet (T : MaterialData) (γ : ℝ) (a b c : ℕ)
    (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => T.M (T.radius p.1) ^ c * mixedDerivative a b (materialPullback T γ f) p

def HeightMember (D : ReferenceData) (T : MaterialData) (γ : ℝ)
    (f : PolarPoint → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (annularOpen D) ∧
  (∀ r θ, f (r, -θ) = f (r, θ)) ∧ Function.Periodic f (0, Real.pi) ∧
  (∀ p, p ∉ annularOpen D → f p = 0) ∧
  ∀ a b c : ℕ, MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure

def JetIndex (s : ℕ) :=
  {j : Fin 3 → Fin (s + 1) // (j 0).val + (j 1).val + (j 2).val ≤ s}

instance (s : ℕ) : Fintype (JetIndex s) := by
  classical
  unfold JetIndex
  infer_instance

def zeroJetIndex (s : ℕ) : JetIndex s := ⟨fun _ => 0, by simp⟩

abbrev PhysicalJetHilbert (s : ℕ) := PiLp 2 (fun _ : JetIndex s => CylinderL2)

def physicalNorm (T : MaterialData) (γ : ℝ) (s : ℕ) (f : PolarPoint → ℝ) : ℝ :=
  Real.sqrt ((∑ j : JetIndex s,
    eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
      2 materialCylinderMeasure ^ 2).toReal)

def IsCylinderTest (φ : PolarPoint → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.Periodic φ (0, Real.pi) ∧
  ∃ R : ℝ, 0 < R ∧ ∀ p, R ≤ |p.1| → φ p = 0

def HasWeakMixedDerivative (f g : CylinderL2) (a b : ℕ) : Prop :=
  ∀ φ : PolarPoint → ℝ, IsCylinderTest φ →
    (∫ p, g p * φ p ∂materialCylinderMeasure) =
      (-1 : ℝ) ^ (a + b) * ∫ p, f p * mixedDerivative a b φ p ∂materialCylinderMeasure

def physicalJetGraph (T : MaterialData) (s : ℕ) : Set (PhysicalJetHilbert s) :=
  {z | ((fun p : PolarPoint => z (zeroJetIndex s) (p.1, Real.pi - p.2))
      =ᵐ[materialCylinderMeasure] (z (zeroJetIndex s) : PolarPoint → ℝ)) ∧
    ∀ j : JetIndex s, ∃ d : CylinderL2,
    HasWeakMixedDerivative (z (zeroJetIndex s)) d (j.val 0).val (j.val 1).val ∧
    (z j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => T.M (T.radius p.1) ^ (j.val 2).val * d p)}

/-- Candidate realization data only. Closedness and exact weak-graph identification
are separate, explicit obligations in `IsSobolevModel`. -/
structure SobolevModelData where
  level : ∀ s, Submodule ℝ (PhysicalJetHilbert s)
  bond : ∀ s, level (s + 1) →L[ℝ] level s
  decode : ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => level s) bond →ₗ[ℝ]
    (PolarPoint → ℝ)

abbrev SobolevModelData.Space (S : SobolevModelData) :=
  ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond

instance (S : SobolevModelData) : AddCommGroup S.Space :=
  inferInstanceAs (AddCommGroup
    (ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond))

instance (S : SobolevModelData) : Module ℝ S.Space :=
  inferInstanceAs (Module ℝ
    (ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond))

def SobolevModelData.grading (S : SobolevModelData) : ℕ → Seminorm ℝ S.Space :=
  ContinuousFlexibility.Analysis.gradedSeminorm (fun s => S.level s) S.bond

def IsSobolevModel (D : ReferenceData) (T : MaterialData) (γ : ℝ)
    (S : SobolevModelData) : Prop :=
  (∀ s, (S.level s : Set (PhysicalJetHilbert s)) = physicalJetGraph T s) ∧
  (∀ s, IsClosed (S.level s : Set (PhysicalJetHilbert s))) ∧
  Continuous S.decode ∧
  (∀ u : S.Space, HeightMember D T γ (S.decode u)) ∧
  (∀ f, HeightMember D T γ f → ∃ u : S.Space, S.decode u = f) ∧
  Function.Injective S.decode ∧
  (∀ u : S.Space, ∀ s,
    (((u.val s).val (zeroJetIndex s)) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      materialPullback T γ (S.decode u)) ∧
  (∀ u : S.Space, ∀ s, ‖u.val s‖ = physicalNorm T γ s (S.decode u))

def angularMean (f : ℝ → ℝ) : ℝ := (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, f θ

def physicalSourceIntegral (D : ReferenceData) (f : PolarPoint → ℝ) : ℝ :=
  ∫ r in D.a..D.b, angularMean (fun θ => f (r, θ))

def HasCompactRadialSupport (D : ReferenceData) (f : PolarPoint → ℝ) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo D.a D.b ∧ ∀ r, r ∉ K → ∀ θ, f (r, θ) = 0

def CircleJetIndex (s : ℕ) := {j : Fin 2 → Fin (s + 1) // (j 0).val + (j 1).val ≤ s}

instance (s : ℕ) : Fintype (CircleJetIndex s) := by
  classical
  unfold CircleJetIndex
  infer_instance

def zeroCircleJetIndex (s : ℕ) : CircleJetIndex s := ⟨fun _ => 0, by simp⟩

abbrev CircleJetHilbert (s : ℕ) :=
  lp (fun _ : ℕ => PiLp 2 (fun _ : CircleJetIndex s => AngleL2)) 2

def circleNorm (T : MaterialData) (γ : ℝ) (s : ℕ) (u : ℕ → ℝ → ℝ) : ℝ :=
  Real.sqrt ((∑' m : ℕ, ∑ j : CircleJetIndex s,
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2).toReal)

def CircleMember (T : MaterialData) (γ : ℝ) (u : ℕ → ℝ → ℝ) : Prop :=
  (∀ m, ContDiff ℝ ∞ (u m) ∧ Function.Periodic (u m) Real.pi) ∧
  (∀ m b, MemLp (iteratedDeriv b (u m)) 2 angleMeasure) ∧
  (∀ s : ℕ, (∑' m : ℕ, ∑ j : CircleJetIndex s,
    ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
      T.H (T.sample m) ^ (-γ)) ^ 2) *
      eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2) < (∞ : ℝ≥0∞))

def HasWeakAngularDerivative (f g : AngleL2) (b : ℕ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ Real.pi →
    (∫ θ, g θ * φ θ ∂angleMeasure) =
      (-1 : ℝ) ^ b * ∫ θ, f θ * iteratedDeriv b φ θ ∂angleMeasure

def circleJetGraph (T : MaterialData) (s : ℕ) : Set (CircleJetHilbert s) :=
  {z | ∀ m j, ∃ d : AngleL2,
    HasWeakAngularDerivative (z m (zeroCircleJetIndex s)) d (j.val 0).val ∧
    (z m j : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => T.M (T.sample m) ^ (j.val 1).val * d θ)}

structure CircleModelData where
  level : ∀ s, Submodule ℝ (CircleJetHilbert s)
  bond : ∀ s, level (s + 1) →L[ℝ] level s
  decode : ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => level s) bond →ₗ[ℝ]
    (ℕ → ℝ → ℝ)

abbrev CircleModelData.Space (S : CircleModelData) :=
  ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond

instance (S : CircleModelData) : AddCommGroup S.Space :=
  inferInstanceAs (AddCommGroup
    (ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond))

instance (S : CircleModelData) : Module ℝ S.Space :=
  inferInstanceAs (Module ℝ
    (ContinuousFlexibility.Analysis.ProjectiveLimit (fun s => S.level s) S.bond))

def CircleModelData.grading (S : CircleModelData) : ℕ → Seminorm ℝ S.Space :=
  ContinuousFlexibility.Analysis.gradedSeminorm (fun s => S.level s) S.bond

def IsCircleModel (T : MaterialData) (γ : ℝ) (S : CircleModelData) : Prop :=
  (∀ s, (S.level s : Set (CircleJetHilbert s)) = circleJetGraph T s) ∧
  (∀ s, IsClosed (S.level s : Set (CircleJetHilbert s))) ∧
  Continuous S.decode ∧
  (∀ u : S.Space, CircleMember T γ (S.decode u)) ∧
  (∀ f, CircleMember T γ f → ∃ u : S.Space, S.decode u = f) ∧
  Function.Injective S.decode ∧
  (∀ u : S.Space, ∀ s m,
    ((((u.val s).val m) (zeroCircleJetIndex s)) : ℝ → ℝ) =ᵐ[angleMeasure]
      (fun θ => T.H (T.sample m) ^ (-γ) * S.decode u m θ)) ∧
  (∀ u : S.Space, ∀ s, ‖u.val s‖ = circleNorm T γ s (S.decode u))

/-! ## Actual smooth directional towers and fixed-loss tame estimates -/

section TameDefinitions

variable {E F G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

def pairGrading (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    ℕ → Seminorm ℝ (E × F) :=
  fun n => (p n).comp (LinearMap.fst ℝ E F) + (q n).comp (LinearMap.snd ℝ E F)

def realGrading : ℕ → Seminorm ℝ ℝ := fun _ => normSeminorm ℝ ℝ

/-- A tower of genuine topological directional derivatives. -/
structure SmoothDirections (U : Set E) (f : E → F) where
  open_domain : IsOpen U
  D : ∀ n : ℕ, E → E [×n]→L[ℝ] F
  zero : ∀ x ∈ U, D 0 x Fin.elim0 = f x
  continuous : ∀ n, ContinuousOn (fun p : E × (Fin n → E) => D n p.1 p.2) (U ×ˢ univ)
  derivative : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
    ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
      (fun y => D n y v) (D (n + 1) x (Fin.cons w v)) x w

def SmoothTameOn (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (U : Set E) (f : E → F) : Prop :=
  ∃ J : SmoothDirections U f, ∀ k : ℕ, ∀ x0 ∈ U,
    ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
    ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
      p base (x - x0) < ε → ∀ v : Fin k → E,
      q s (J.D k x v) ≤ C *
        ((1 + p (s + loss) x) * ∏ i, p base (v i) +
          ∑ i : Fin k, p (s + loss) (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j))

def LinearFamilyTame (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (r : ℕ → Seminorm ℝ G) (U : Set E) (V : E → G →ₗ[ℝ] F) : Prop :=
  ∃ loss base : ℕ, ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ U, ∀ y : G,
      q s (V x y) ≤ C * (r (s + loss) y + (1 + p (s + loss) x) * r base y)

def HasSmoothing (p : ℕ → Seminorm ℝ E) : Prop :=
  ∃ base loss : ℕ, ∃ S : ℕ → E →L[ℝ] E,
    (∀ m n : ℕ, base ≤ m → m ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ N x,
      p n (S N x) ≤ C * Real.exp (((n : ℝ) - m + loss) * N) * p m x) ∧
    (∀ m n : ℕ, base ≤ m → m ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ N x,
      p m (x - S N x) ≤ C * Real.exp (-((n : ℝ) - m - loss) * N) * p n x) ∧
    (∀ x, Tendsto (fun N => S N x) atTop (𝓝 x))

def HasInterpolation (p : ℕ → Seminorm ℝ E) : Prop :=
  ∃ base loss : ℕ, ∀ a b c : ℕ, base ≤ a → a < b → b + loss < c →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      p b x ≤ C * (p a x) ^ (((c : ℝ) - b - loss) / (c - a)) *
        (p c x) ^ (((b : ℝ) - a + loss) / (c - a))

def TameRetraction (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) : Prop :=
  ∃ J : E →L[ℝ] F, ∃ P : F →L[ℝ] E,
    (∀ x, P (J x) = x) ∧
    (∃ r b, ContinuousFlexibility.Analysis.IsTameLinear p q J.toLinearMap r b) ∧
    (∃ r b, ContinuousFlexibility.Analysis.IsTameLinear q p P.toLinearMap r b)

end TameDefinitions

abbrev PhysicalModelBanach := lp (fun _ : ℕ => CylinderL2) 2

def modelGrading : ℕ → Seminorm ℝ
    (ContinuousFlexibility.Analysis.ExponentialSequenceSpace PhysicalModelBanach) :=
  ContinuousFlexibility.Analysis.exponentialSequenceSeminorm PhysicalModelBanach

def CutoffConditions (D : ReferenceData) (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧
  (∃ δ : ℝ, 0 < δ ∧ δ < D.b - D.a ∧
    (∀ r, r ≤ D.a + δ → χ r = 1) ∧ (∀ r, D.b - δ ≤ r → χ r = 0)) ∧
  ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo D.a D.b ∧
    (∀ r ∈ K, 0 < deriv D.w r) ∧ (∀ r, r ∉ K → deriv χ r = 0)

structure PhysicalSpacesData where
  height : ℝ → SobolevModelData
  circle : ℝ → CircleModelData
  chiLeft : ℝ → ℝ
  Q : (height (3 / 4 : ℝ)).Space →L[ℝ] ℝ
  psi : (height (3 / 4 : ℝ)).Space

abbrev PhysicalSpacesData.Source (S : PhysicalSpacesData) := S.Q.toLinearMap.ker

instance (S : PhysicalSpacesData) : AddCommGroup S.Source :=
  Submodule.addCommGroup S.Q.toLinearMap.ker

instance (S : PhysicalSpacesData) : Module ℝ S.Source :=
  Submodule.module S.Q.toLinearMap.ker

def PhysicalSpacesData.sourceGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ S.Source :=
  fun n => ((S.height (3 / 4 : ℝ)).grading n).comp S.Q.toLinearMap.ker.subtype

set_option maxHeartbeats 1000000 in
def evenCircleSubmoduleAt (S : PhysicalSpacesData) (γ : ℝ) :
    Submodule ℝ (S.circle γ).Space where
  carrier := {u | ∀ m θ, (S.circle γ).decode u m (-θ) = (S.circle γ).decode u m θ}
  zero_mem' := by
    intro m θ
    simp only [map_zero, Pi.zero_apply]
  add_mem' := by
    intro x y hx hy m θ
    simp only [map_add, Pi.add_apply]
    rw [hx m θ, hy m θ]
  smul_mem' := by
    intro a x hx m θ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hx m θ]

abbrev EvenCircleAt (S : PhysicalSpacesData) (γ : ℝ) := evenCircleSubmoduleAt S γ

def evenCircleGradingAt (S : PhysicalSpacesData) (γ : ℝ) :
    ℕ → Seminorm ℝ (EvenCircleAt S γ) :=
  fun n => ((S.circle γ).grading n).comp (evenCircleSubmoduleAt S γ).subtype

def IsPhysicalSpaces (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData) : Prop :=
  (∀ γ, IsSobolevModel D T γ (S.height γ)) ∧
  (∀ γ, IsCircleModel T γ (S.circle γ)) ∧ CutoffConditions D S.chiLeft ∧
  (∀ γ, TameRetraction (S.height γ).grading modelGrading ∧
    HasSmoothing (S.height γ).grading ∧ HasInterpolation (S.height γ).grading) ∧
  (∀ γ, TameRetraction (S.circle γ).grading modelGrading ∧
    HasSmoothing (S.circle γ).grading ∧ HasInterpolation (S.circle γ).grading) ∧
  (∀ γ δ, ∃ mul : (S.height γ).Space × (S.height δ).Space → (S.height (γ + δ)).Space,
    (∀ u v p, (S.height (γ + δ)).decode (mul (u, v)) p =
      (S.height γ).decode u p * (S.height δ).decode v p) ∧
    SmoothTameOn (pairGrading (S.height γ).grading (S.height δ).grading)
      (S.height (γ + δ)).grading univ mul) ∧
  (∀ γ, ∃ trace : (S.height γ).Space →L[ℝ] EvenCircleAt S γ,
    (∀ u m θ, (S.circle γ).decode (trace u).val m θ = (S.height γ).decode u (T.sample m, θ)) ∧
    (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
      (S.height γ).grading (evenCircleGradingAt S γ) trace.toLinearMap loss base) ∧
    ∃ extend : EvenCircleAt S γ →L[ℝ] (S.height γ).Space,
      (∀ u, trace (extend u) = u) ∧
      (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
        (evenCircleGradingAt S γ) (S.height γ).grading extend.toLinearMap loss base)) ∧
  (∀ f, S.Q f = physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode f)) ∧
  HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode S.psi) ∧ S.Q S.psi = 1 ∧
  (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
    (S.height (3 / 4 : ℝ)).grading realGrading S.Q.toLinearMap loss base) ∧
  (∃ P : (S.height (3 / 4 : ℝ)).Space →L[ℝ] (S.height (3 / 4 : ℝ)).Space,
    (∀ f, P f = f - S.Q f • S.psi) ∧ (∀ f, S.Q (P f) = 0) ∧
    (∀ f, S.Q f = 0 → P f = f) ∧
    (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
      (S.height (3 / 4 : ℝ)).grading (S.height (3 / 4 : ℝ)).grading
      P.toLinearMap loss base)) ∧
  (∀ γ : ℝ, 0 < γ → ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧
    ∃ inv : (S.height γ).Space → (S.height γ).Space,
      (∀ u, (S.height γ).grading base u < ε → ∀ p ∈ annularOpen D,
        1 / 2 < 1 + (S.height γ).decode u p ∧
        (S.height γ).decode (inv u) p = 1 / (1 + (S.height γ).decode u p) - 1) ∧
      SmoothTameOn (S.height γ).grading (S.height γ).grading
        {u | (S.height γ).grading base u < ε} inv) ∧
  (∀ γ : ℝ, 0 < γ → ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → F 0 = 0 →
    ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ comp : (S.height γ).Space → (S.height γ).Space,
        (∀ u, (S.height γ).grading base u < ε → ∀ p,
          (S.height γ).decode (comp u) p = F ((S.height γ).decode u p)) ∧
        SmoothTameOn (S.height γ).grading (S.height γ).grading
          {u | (S.height γ).grading base u < ε} comp) ∧
  (∀ γ, ∃ even odd : (S.circle γ).Space →L[ℝ] (S.circle γ).Space,
    (∀ u m θ, (S.circle γ).decode (even u) m θ =
      ((S.circle γ).decode u m θ + (S.circle γ).decode u m (-θ)) / 2) ∧
    (∀ u m θ, (S.circle γ).decode (odd u) m θ =
      ((S.circle γ).decode u m θ - (S.circle γ).decode u m (-θ)) / 2) ∧
    (∀ u, even (even u) = even u ∧ odd (odd u) = odd u) ∧
    (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
      (S.circle γ).grading (S.circle γ).grading even.toLinearMap loss base) ∧
    (∃ loss base, ContinuousFlexibility.Analysis.IsTameLinear
      (S.circle γ).grading (S.circle γ).grading odd.toLinearMap loss base))

/-- W02: actual spaces, completeness through closed weak graphs, retractions,
product/trace estimates and the physical compatibility functional; section 7,
lines 72--150. -/
def W02Statement : Prop :=
  ∀ D T, IsAccumulatingProfile D → IsMaterialData D T →
    ∃ S : PhysicalSpacesData, IsPhysicalSpaces D T S

def UniformFlatJets (D : ReferenceData) (f : PolarPoint → ℝ) : Prop :=
  ∀ a b k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ r θ, r ∈ Ioo D.a D.b → θ ∈ Icc (0 : ℝ) Real.pi →
      endpointDistance D r < δ →
      |endpointDistance D r ^ (-(k : ℤ)) * mixedDerivative a b f (r, θ)| < ε

/-- W03: all ordinary mixed jets, unequal endpoint constants and one common
parameter interval; section 7, lines 102--156. -/
def W03Statement : Prop :=
  ∀ D T S, IsAccumulatingProfile D → IsMaterialData D T → IsPhysicalSpaces D T S →
    (∀ γ : ℝ, 0 < γ → ∀ u : (S.height γ).Space,
      ContDiff ℝ ∞ ((S.height γ).decode u) ∧ UniformFlatJets D ((S.height γ).decode u)) ∧
    (∀ γ : ℝ, 0 < γ → ∀ u : (S.height γ).Space, ∀ c : ℝ,
      ContDiff ℝ ∞ (fun p : PolarPoint => (S.height γ).decode u p + c * S.chiLeft p.1)) ∧
    (∀ γ q0 : ℝ, 0 < γ → 0 < q0 →
      ∀ c : ℝ → (S.height γ).Space × ℝ,
      SmoothTameOn realGrading (pairGrading (S.height γ).grading realGrading)
        (Ioo (-q0) q0) c →
      ContDiffOn ℝ ∞ (fun p : PolarPoint × ℝ =>
        (S.height γ).decode (c p.2).1 p.1 + (c p.2).2 * S.chiLeft p.1.1)
        (univ ×ˢ Ioo (-q0) q0))

/-! ## General calculus and inverse/existence targets on actual projective spaces -/

section GeneralTargets

variable {E F G : ℕ → Type}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]

def TameCalculusTarget
    (e : ∀ n, E (n + 1) →L[ℝ] E n)
    (f : ∀ n, F (n + 1) →L[ℝ] F n)
    (g : ∀ n, G (n + 1) →L[ℝ] G n) : Prop :=
  let X := ContinuousFlexibility.Analysis.ProjectiveLimit E e
  let Y := ContinuousFlexibility.Analysis.ProjectiveLimit F f
  let Z := ContinuousFlexibility.Analysis.ProjectiveLimit G g
  let p := ContinuousFlexibility.Analysis.gradedSeminorm E e
  let q := ContinuousFlexibility.Analysis.gradedSeminorm F f
  let r := ContinuousFlexibility.Analysis.gradedSeminorm G g
  (∀ L : X →L[ℝ] Y, (∃ loss base,
    ContinuousFlexibility.Analysis.IsTameLinear p q L.toLinearMap loss base) →
    SmoothTameOn p q univ L) ∧
  (∀ (U : Set X) (V : Set Y), IsOpen U → IsOpen V →
    ∀ (u : X → Y) (v : Y → Z), MapsTo u U V →
      SmoothTameOn p q U u → SmoothTameOn q r V v →
      SmoothTameOn p r U (v ∘ u)) ∧
  (∀ (U : Set X) (u v : X → Y),
    SmoothTameOn p q U u → SmoothTameOn p q U v →
    SmoothTameOn p q U (fun x => u x + v x)) ∧
  (HasSmoothing p → HasInterpolation p) ∧
  (TameRetraction p q → HasSmoothing q → HasSmoothing p) ∧
  (∀ B : X →L[ℝ] Y →L[ℝ] Z,
    (∃ loss base : ℕ, ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      r s (B x y) ≤ C * (p (s + loss) x * q base y + p base x * q (s + loss) y)) →
    SmoothTameOn (pairGrading p q) r univ (fun z : X × Y => B z.1 z.2))

def InverseFamilyTarget
    (e : ∀ n, E (n + 1) →L[ℝ] E n)
    (f : ∀ n, F (n + 1) →L[ℝ] F n)
    (g : ∀ n, G (n + 1) →L[ℝ] G n) : Prop :=
  let X := ContinuousFlexibility.Analysis.ProjectiveLimit E e
  let Y := ContinuousFlexibility.Analysis.ProjectiveLimit F f
  let Z := ContinuousFlexibility.Analysis.ProjectiveLimit G g
  let p := ContinuousFlexibility.Analysis.gradedSeminorm E e
  let q := ContinuousFlexibility.Analysis.gradedSeminorm F f
  let r := ContinuousFlexibility.Analysis.gradedSeminorm G g
  ∀ U : Set X, IsOpen U →
    ∀ (L : X → Y →L[ℝ] Z) (V : X → Z →ₗ[ℝ] Y),
      SmoothTameOn (pairGrading p q) r (U ×ˢ univ) (fun z : X × Y => L z.1 z.2) →
      (∀ x ∈ U, ∀ y, V x (L x y) = y) →
      (∀ x ∈ U, ∀ y, L x (V x y) = y) →
      ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) →
      LinearFamilyTame p q r U V →
      SmoothTameOn (pairGrading p r) q (U ×ˢ univ) (fun z : X × Z => V z.1 z.2)

def NashMoserTarget
    (e : ∀ n, E (n + 1) →L[ℝ] E n)
    (f : ∀ n, F (n + 1) →L[ℝ] F n) : Prop :=
  let X := ContinuousFlexibility.Analysis.ProjectiveLimit E e
  let Y := ContinuousFlexibility.Analysis.ProjectiveLimit F f
  let p := ContinuousFlexibility.Analysis.gradedSeminorm E e
  let q := ContinuousFlexibility.Analysis.gradedSeminorm F f
  HasSmoothing p → HasSmoothing q →
    ∀ (x0 : X) (base : ℕ) (ε : ℝ), 0 < ε →
      let U : Set (X × ℝ) := {z | p base (z.1 - x0) < ε ∧ |z.2| < ε}
      ∀ (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
        (Q : X × ℝ → Y →ₗ[ℝ] Y →ₗ[ℝ] Y),
        SmoothTameOn (pairGrading p realGrading) q U R →
        SmoothTameOn (pairGrading (pairGrading p realGrading) q) p (U ×ˢ univ)
          (fun z : (X × ℝ) × Y => V z.1 z.2) →
        SmoothTameOn (pairGrading (pairGrading (pairGrading p realGrading) q) q) q
          ((U ×ˢ univ) ×ˢ univ)
          (fun z : ((X × ℝ) × Y) × Y => Q z.1.1 z.1.2 z.2) →
        R (x0, 0) = 0 →
        (∀ z ∈ U, ∀ y : Y,
          ContinuousFlexibility.Analysis.HasProjectiveLineDerivAt
            (fun x => R (x, z.2)) (y + Q z (R z) y) z.1 (V z y)) →
        ∃ q0 : ℝ, 0 < q0 ∧ ∃ x : ℝ → X,
          x 0 = x0 ∧
          (∀ t, |t| < q0 → (x t, t) ∈ U ∧ R (x t, t) = 0) ∧
          SmoothTameOn realGrading p (Ioo (-q0) q0) x ∧
          (∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |t| < q0 →
            p s (x t - x0) ≤ C * |t|)

end GeneralTargets

/-- H01: actual projective spaces and explicitly defined directional/tame
calculus, not an arbitrary black-box property; section 7, lines 102--150. -/
def H01Statement : Prop :=
  (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B],
    HasSmoothing (ContinuousFlexibility.Analysis.exponentialSequenceSeminorm B)) ∧
  ∀ (E F G : ℕ → Type)
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)] [∀ n, CompleteSpace (G n)]
    (e : ∀ n, E (n + 1) →L[ℝ] E n) (f : ∀ n, F (n + 1) →L[ℝ] F n)
    (g : ∀ n, G (n + 1) →L[ℝ] G n), TameCalculusTarget e f g

/-- H02: Hamilton's inverse-family target, with actual continuity and tame
hypotheses written out; section 8, lines 523--550. -/
def H02Statement : Prop :=
  ∀ (E F G : ℕ → Type)
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
    [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)] [∀ n, CompleteSpace (G n)]
    (e : ∀ n, E (n + 1) →L[ℝ] E n) (f : ∀ n, F (n + 1) →L[ℝ] F n)
    (g : ∀ n, G (n + 1) →L[ℝ] G n), InverseFamilyTarget e f g

/-- H03: genuine quadratic-error Nash--Moser existence, with one common q0;
section 9, lines 183--196. It is a target, not an assumed theorem. -/
def H03Statement : Prop :=
  ∀ (E F : ℕ → Type)
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
    (e : ∀ n, E (n + 1) →L[ℝ] E n) (f : ∀ n, F (n + 1) →L[ℝ] F n), NashMoserTarget e f

end ContinuousFlexibility.Statements
