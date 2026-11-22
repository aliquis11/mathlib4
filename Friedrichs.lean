/-
Copyright (c) 2026 Lukas Schimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Schimmer
-/

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open scoped ComplexConjugate


namespace Submodule

variable {R M : Type*} [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M]

-- Temporary copy pending integration into mathlib (PR #45828).

/-- `Submodule.inclusion` as a `ContinuousLinearMap`. -/
def inclusionL {p q : Submodule R M} (h : p ≤ q) : p →L[R] q where
  toLinearMap := Submodule.inclusion h
  cont := continuous_inclusion h

end Submodule

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

-- Temporary copy pending integration into mathlib (PR #45828).

/-- A vector `y` belongs to the domain of the adjoint if and only if the
functional `x ↦ ⟪y, T x⟫` on `T.domain` can be represented as an inner product with
a vector of `E`. -/
theorem mem_adjoint_domain_iff_exists {T : E →ₗ.[𝕜] F} (y : F) :
    y ∈ T.adjoint.domain ↔ ∃ w : E, ∀ x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫ := by
  constructor
  · intro hy
    let ℓ := T.adjointDomainMkCLM ⟨y, hy⟩
    let D := T.domain.topologicalClosure
    let i := Submodule.inclusionL T.domain.le_topologicalClosure
    let ℓExt := ℓ.extend i
    use ((InnerProductSpace.toDual 𝕜 D).symm ℓExt : E)
    intro x
    change ⟪(InnerProductSpace.toDual 𝕜 D).symm ℓExt, i x⟫ = ℓ x
    rw [InnerProductSpace.toDual_symm_apply]
    apply ContinuousLinearMap.extend_eq
    · apply (denseRange_inclusion_iff T.domain.le_topologicalClosure).2
      simp
    · exact (isUniformEmbedding_set_inclusion T.domain.le_topologicalClosure).isUniformInducing
  · exact LinearPMap.mem_adjoint_domain_of_exists y

/-- A densely defined symmtric operator that is surjective,
is also self-adjoint. -/
theorem isSelfAdjoint_of_surjective
    {A : E →ₗ.[𝕜] E}
    (hA_dense : Dense (A.domain : Set E))
    (hA_symm : A.IsFormalAdjoint A)
    (hA_surj : Function.Surjective (fun x : A.domain => A x)) :
    IsSelfAdjoint A := by
  ext x
  constructor
  · intro hx
    change x ∈ A.adjoint.domain at hx
    rw [LinearPMap.mem_adjoint_domain_iff_exists x] at hx
    rcases hx with ⟨f, hpair⟩
    rcases hA_surj f with ⟨x', hx'⟩
    dsimp at hx'
    have hinner (y : A.domain) :
        ⟪(x' : E), A y⟫ = ⟪x, A y⟫ := by
      rw [← hA_symm x' y]
      rw [hx']
      apply hpair y
    have hxx': x = (x' : E) := by
      apply ext_inner_right 𝕜
      intro y
      rcases hA_surj y with ⟨z, hz⟩
      rw [← hz, hinner z]
    simp [hxx']

  · intro hx
    exact (hA_symm.le_adjoint hA_dense).1 hx
  · symm
    apply (hA_symm.le_adjoint hA_dense).2
    simp

end LinearPMap

namespace Friedrichs

variable {𝕜 H : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable
  (S : H →ₗ.[𝕜] H)
  (hsym : S.IsFormalAdjoint S)
  (hpos : ∀ u : S.domain, u ≠ 0 → 0 < RCLike.re (inner 𝕜 (u : H) (S u)))

/- Define the form domain. The proofs of symmetry and positivity
are in the space's parameters. -/
def FormSpace
    (S : H →ₗ.[𝕜] H)
    (_hsym : S.IsFormalAdjoint S)
    (_hpos : ∀ u : S.domain, u ≠ 0 → 0 < RCLike.re (⟪(u : H), S u⟫)) :
    Type _ := S.domain

instance :
    AddCommGroup (FormSpace S hsym hpos) :=
  inferInstanceAs (AddCommGroup S.domain)

instance :
    Module 𝕜 (FormSpace S hsym hpos) :=
  inferInstanceAs (Module 𝕜 S.domain)

-- Define the form space with inner product
@[instance_reducible]
def InnerProductFormSpace :
    InnerProductSpace.Core 𝕜 (FormSpace S hsym hpos) := by
  refine
    { inner := fun (u v : S.domain) =>
        ⟪(u : H), S v⟫
      conj_inner_symm := by
        intro u v
        simp [← hsym u v]
      re_inner_nonneg := by
        intro u
        by_cases hu: u=0
        · rw [hu]
          change 0 ≤ RCLike.re (⟪(0 : H), S 0⟫)
          simp
        · bound [hpos u hu]
      add_left := by
        intro u v w
        apply inner_add_left
      smul_left := by
        intro u v w
        apply inner_smul_left
      definite := by
        intro u huinnerzero
        by_contra hu
        have hposu := hpos u hu
        simp [huinnerzero] at hposu }

instance FormInnerProductSpaceCore :
    InnerProductSpace.Core 𝕜 (FormSpace S hsym hpos) :=
  InnerProductFormSpace S hsym hpos

instance FormNormedAddCommGroup :
    NormedAddCommGroup (FormSpace S hsym hpos) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := 𝕜)
    (cd := InnerProductFormSpace S hsym hpos)

instance FormInnerProductSpace :
    InnerProductSpace 𝕜 (FormSpace S hsym hpos) :=
  InnerProductSpace.ofCore
    (InnerProductFormSpace S hsym hpos).toCore

variable
  (c : ℝ) (hc : 0 < c)
  (hbound : ∀ u : S.domain,
  c * ‖(u : H)‖ ^ 2 ≤
    RCLike.re (inner 𝕜 (u : H) (S u)))

instance : CoeOut (FormSpace S hsym hpos) H :=
  ⟨fun u => u.val⟩

/-- The completion of the form domian with respect to the inner product from the positive operator form
is injectively embedded in `E`-/
theorem exists_positiveFormCompletion_inclusion
    [CompleteSpace H]
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤
        RCLike.re (⟪(u : H), S u⟫) ):
    ∃ J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H,
      Function.Injective J ∧
      (∀ u : FormSpace S hsym hpos,
        J (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
          (u : H) )∧
      ∀ w : UniformSpace.Completion (FormSpace S hsym hpos),
        c * ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    let j : FormSpace S hsym hpos →ₗ[𝕜] H :={
    toFun u := (u : H)
    map_add':= by
      intro u v
      rfl
    map_smul' := by
      intro a u
      rfl
    }
    have jbound : ∀ u : FormSpace S hsym hpos,
      ‖(u : H)‖  ≤ 1/Real.sqrt c * ‖u‖:= by
      intro u
      rw [← mul_le_mul_iff_right₀ (Real.sqrt_pos.2 hc),← mul_assoc]
      field_simp
      rw [← sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg (u : H)))
      (norm_nonneg u),mul_pow]
      rw [Real.sq_sqrt hc.le]
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜) u]
      exact hbound u
    let jContinuous : FormSpace S hsym hpos →L[𝕜] H :=
      j.mkContinuous (1 / Real.sqrt c) jbound
    let J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H :=
      jContinuous.fromCompletion
    use J
    constructor
    · intro v₁ v₂ hv
      rw [← sub_eq_zero]

      have hInnerOnCompletion : ∀ (u : FormSpace S hsym hpos)
          (v : UniformSpace.Completion (FormSpace S hsym hpos)),
          ⟪v, (u : UniformSpace.Completion (FormSpace S hsym hpos))⟫ =
          ⟪J v, S (u : S.domain)⟫  := by
        intro u v
        apply UniformSpace.Completion.ext'
            (f := fun w => ⟪w,  (u : UniformSpace.Completion (FormSpace S hsym hpos))⟫)
            (g := fun w => ⟪ (J w), (S (u : S.domain))⟫)
        · exact Continuous.inner (continuous_id) (continuous_const)
        · exact Continuous.inner (J.continuous) (continuous_const)
        · intro w
          rw[UniformSpace.Completion.inner_coe, ContinuousLinearMap.fromCompletion_apply_coe]
          rfl

      have hOrthogonalToFormSpace: ∀ u : FormSpace S hsym hpos,
          ⟪(J (v₁-v₂) : H), S u⟫ = 0  := by
        intro u
        rw [J.map_sub,hv,sub_self]
        simp

      have hFormSpaceDense : DenseRange
        (fun u : FormSpace S hsym hpos =>
        (u : UniformSpace.Completion (FormSpace S hsym hpos))) :=
        UniformSpace.Completion.denseRange_coe

      apply hFormSpaceDense.eq_zero_of_inner_left 𝕜
      intro u
      rw [hInnerOnCompletion u (v₁ - v₂)]
      exact hOrthogonalToFormSpace u
    · constructor
      · intro u
        rw [ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      · intro w
        apply UniformSpace.Completion.induction_on w
            (p := fun w => c* ‖J w‖^2 ≤ ‖w‖^2)
        · apply isClosed_le
          · exact (continuous_const.mul (J.continuous.norm.pow 2))
          · exact (continuous_norm.pow 2)
        · intro a
          rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
          change c * ‖(a : H)‖^2 ≤ ‖a‖^2
          rw [norm_sq_eq_re_inner (𝕜 := 𝕜) a]
          exact hbound a


/--For every `f` in `H` there is a unique `w` in the completed form domain,
such that `⟪w, v⟫ = ⟪f, J v⟫` for all `v` in the completed form domain.-/
theorem exists_unique_form_representative
    [CompleteSpace H]
    (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
    (f : H) :
    ∃! w : UniformSpace.Completion (FormSpace S hsym hpos),
      ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
        ⟪w, v⟫ = ⟪f, J v⟫ := by
  have hex := (InnerProductSpace.toDual 𝕜
    (UniformSpace.Completion (FormSpace S hsym hpos))).bijective.existsUnique
    ((innerSL 𝕜 f).comp J)

  convert hex
  simp[ContinuousLinearMap.ext_iff]

/-- Map every `f` in `H` to the unique `w` in the completed form domain,
such that `⟪w, v⟫ = ⟪f, J v⟫` for all `v` in the completed form domain.-/
def RieszRepresentative
    (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
    (f : H) :=
  (InnerProductSpace.toDual 𝕜
    (UniformSpace.Completion (FormSpace S hsym hpos))).symm
    ((innerSL 𝕜 f).comp J)

section PositiveFriedrichsTheorems

variable
  [CompleteSpace H]
  (hS_dense : Dense (S.domain : Set H))
  (c : ℝ) (hc : 0 < c)
  (hbound : ∀ u : S.domain,
    c * ‖(u : H)‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (u : H) (S u)))
  (J : UniformSpace.Completion (FormSpace S hsym hpos) →L[𝕜] H)
  (hJ_injective : Function.Injective J)
  (hJ_agrees : ∀ u : FormSpace S hsym hpos,
    J (u : UniformSpace.Completion (FormSpace S hsym hpos)) =
      (u : H))
  (hJ_dense : DenseRange J)
  (hJ_bound : ∀ w : UniformSpace.Completion (FormSpace S hsym hpos),
    c * ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2)

omit [CompleteSpace H] in
include hJ_agrees in
/--For every `u` in the operator domain and every `v` in the completed
form domain the identity  `⟪v, u⟫ = ⟪J v, Su⟫` holds.-/
theorem inner_formCompletion
    (u : FormSpace S hsym hpos)
    (v : UniformSpace.Completion (FormSpace S hsym hpos)) :
    ⟪v, (u : UniformSpace.Completion (FormSpace S hsym hpos))⟫ =
      ⟪J v,  S (u : S.domain)⟫ := by
  apply UniformSpace.Completion.ext'
      (f := fun w => ⟪w, (u : UniformSpace.Completion (FormSpace S hsym hpos))⟫)
      (g := fun w => ⟪J w, (S (u : S.domain))⟫)
  · exact Continuous.inner continuous_id continuous_const
  · exact Continuous.inner J.continuous continuous_const
  · intro w
    rw [UniformSpace.Completion.inner_coe, hJ_agrees w]
    rfl

-- Construct an extension, including its lower bound.
include hS_dense hJ_injective hJ_agrees hJ_dense hJ_bound in
theorem positive_friedrichs_exists :
    ∃ A : H →ₗ.[𝕜] H,
      S ≤ A ∧
      IsSelfAdjoint A ∧
      (∀ x : A.domain,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
          J w = (x : H)) ∧
      (∀ x : A.domain,
        c * ‖(x : H)‖ ^ 2 ≤
          RCLike.re (⟪(x : H), A x⟫)) := by
  let D : Submodule 𝕜 H :=
    { carrier :=
        {x | ∃ f : H,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = x ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
        ⟪w, v⟫ = ⟪f, J v⟫
        }
      zero_mem' := by
        use 0
        use 0
        simp
      add_mem' := by
        rintro x₁ x₂ ⟨f₁, w₁, hw₁, hinner₁⟩ ⟨f₂, w₂, hw₂, hinner₂⟩
        use f₁ + f₂
        use w₁ + w₂
        constructor
        · simp [hw₁, hw₂]
        · intro v
          simp [inner_add_left, hinner₁ v, hinner₂ v]
      smul_mem' := by
        rintro a x ⟨f, w, hw, hinner⟩
        use a • f
        use a • w
        constructor
        · simp [hw]
        · intro v
          simp [inner_smul_left, hinner v]
    }
  have output_unique (x f g : H)
    (hf : ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
      J w = x ∧ ∀ v, ⟪w, v⟫ = ⟪f, J v⟫)
    (hg : ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
      J w = x ∧ ∀ v, ⟪w, v⟫ = ⟪g, J v⟫) :
    f = g := by
    rcases hf with ⟨w₁, hw₁, hp₁⟩
    rcases hg with ⟨w₂, hw₂, hp₂⟩
    have hw : w₁ = w₂ := by
      apply hJ_injective
      rw [hw₁,hw₂]
    apply hJ_dense.eq_of_inner_left 𝕜
    intro v
    rw [← hp₁ v, ← hp₂ v, hw]

  let A : H →ₗ.[𝕜] H :=
    { domain := D
      toFun :=
        { toFun := fun x => Classical.choose x.property
          map_add' := by
            intro x₁ x₂
            apply output_unique ((x₁ + x₂ : D) : H)
            · exact Classical.choose_spec (x₁ + x₂).property
            · rcases Classical.choose_spec x₁.property with ⟨w₁, hw₁, hpair₁⟩
              rcases Classical.choose_spec x₂.property with ⟨w₂, hw₂, hpair₂⟩
              use (w₁+w₂)
              constructor
              · simp [hw₁, hw₂]
              · intro v
                simp [inner_add_left, hpair₁ v, hpair₂ v]
          map_smul' := by
            rintro a x
            rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
            apply output_unique ((a • x : D) : H)
            · exact Classical.choose_spec (a • x).property
            · rcases Classical.choose_spec (a • x).property with ⟨aw, haw, hapair⟩
              use (a • w)
              constructor
              · simp [hw]
              · intro v
                simp [inner_smul_left, hpair v]
          }
    }
  use A
  have A_apply_iff (x : A.domain) (f : H) :
    A x = f ↔
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H) ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
          ⟪w, v⟫ = ⟪f, J v⟫ := by
    constructor
    · intro h
      rw[← h]
      exact Classical.choose_spec x.property
    · intro h
      rcases h with ⟨w, hw, hpair⟩
      apply output_unique (x : H) (A x) f
      · exact Classical.choose_spec x.property
      · use w

  have hSA : S ≤ A := by
    constructor
    · intro x hx
      use S ⟨x,hx⟩
      let x' : FormSpace S hsym hpos := ⟨x, hx⟩
      use (x' : UniformSpace.Completion (FormSpace S hsym hpos))
      constructor
      · rw [hJ_agrees x']
      · intro v
        rw [← inner_conj_symm (𝕜 := 𝕜) (↑x') v,
             ← inner_conj_symm (𝕜 := 𝕜) (S ⟨x, hx⟩) (J v)]
        rw [inner_formCompletion S hsym hpos J hJ_agrees x' v]
    · intro x₁ x₂ hx₁₂
      symm
      rw [A_apply_iff x₂ (S x₁)]
      rw [← hx₁₂]
      let x' : FormSpace S hsym hpos := x₁
      use (x' : UniformSpace.Completion (FormSpace S hsym hpos))
      constructor
      · apply hJ_agrees x'
      · intro v
        rw [← inner_conj_symm (𝕜 := 𝕜) (↑x') v,
             ← inner_conj_symm (𝕜 := 𝕜) (S x₁) (J v)]
        rw [inner_formCompletion S hsym hpos J hJ_agrees x' v]

  have hA_dense : Dense (A.domain : Set H) :=
      hS_dense.mono hSA.1

  have hA_surj : ∀ f : H, ∃ z : A.domain, A z = f := by
      intro f
      have h := exists_unique_form_representative S hsym hpos J f
      rcases h with ⟨w, hpair, hw_unique⟩
      have hz : J w ∈ A.domain := by
        use f
        use w
      use ⟨J w, hz⟩
      rw [A_apply_iff]
      use w

  have hA_symm : A.IsFormalAdjoint A := by
    intro x₁ x₂
    rcases Classical.choose_spec x₁.property with ⟨w₁, hw₁, hpair₁⟩
    rcases Classical.choose_spec x₂.property with ⟨w₂, hw₂, hpair₂⟩
    change ∀ v, ⟪w₁, v⟫ = ⟪A x₁, J v⟫ at hpair₁
    change ∀ v, ⟪w₂, v⟫ = ⟪A x₂, J v⟫ at hpair₂
    rw [← hw₂, ← hpair₁ w₂]
    rw [← hw₁,← inner_conj_symm (𝕜 := 𝕜) (J w₁) (A x₂), ← hpair₂ w₁,
        ← inner_conj_symm (𝕜 := 𝕜) w₁ w₂]

  constructor
  · exact hSA
  · constructor
    · exact LinearPMap.isSelfAdjoint_of_surjective hA_dense hA_symm hA_surj
    · constructor
      · intro x
        rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
        use w
      · intro x
        rcases Classical.choose_spec x.property with ⟨w, hw, hpair⟩
        change ∀ v, ⟪w, v⟫ = ⟪A x, J v⟫ at hpair
        rw [← hw, inner_re_symm (𝕜 := 𝕜) (J w) (A x)]
        rw [← hpair (w : UniformSpace.Completion (FormSpace S hsym hpos))]
        simp
        exact hJ_bound w

-- Characterise any such extension by the inner product identity.
include  hJ_agrees in
theorem positive_friedrichs_pairing_iff
    {A : H →ₗ.[𝕜] H}
    (hSA : S ≤ A)
    (hA : IsSelfAdjoint A)
    (hA_domain : ∀ x : A.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H))
    (x f : H) :
    (∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = f) ↔
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = x ∧
        ∀ v : UniformSpace.Completion (FormSpace S hsym hpos),
          ⟪w, v⟫ = ⟪f, J v⟫ := by

  have hA_Adj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hA_symm : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rw [hA_Adj] at h
    exact h
  have hA_inner :
    ∀ x : A.domain,
      ∃ v : UniformSpace.Completion (FormSpace S hsym hpos),
        J v = (x : H) ∧
        ∀ u : UniformSpace.Completion (FormSpace S hsym hpos),
          ⟪v, u⟫ = ⟪A x, J u⟫ := by
    rintro x
    rcases hA_domain x  with ⟨w,hw⟩
    use w
    constructor
    · exact hw
    · apply UniformSpace.Completion.ext'
        (f := fun u => ⟪w,  u ⟫)
        (g := fun u => ⟪ A x, (J u)⟫)
      · exact Continuous.inner continuous_const continuous_id
      · exact Continuous.inner continuous_const J.continuous
      · intro v
        rw [hJ_agrees v]
        let vA : A.domain :=
          Submodule.inclusion hSA.1 (v : S.domain)
        change  ⟪w, v⟫ = ⟪A x, vA⟫
        rw [hA_symm x vA]
        have hAv : S (v : S.domain) = A vA := by
          apply hSA.2
          rfl
        rw [← hAv, ← hw]
        rw [inner_formCompletion S hsym hpos J hJ_agrees]

  constructor
  · rintro ⟨hx,hf⟩
    rw[← hf]
    exact hA_inner ⟨x, hx⟩
  · rintro ⟨w, hw, hw_inner⟩
    have hf_inner : ∀ y : A.domain, ⟪f, (y : H)⟫ = ⟪x, A y⟫ := by
      intro y
      rcases hA_inner y with ⟨v, hv, hv_inner⟩
      rw [← hv, ← hw,← inner_conj_symm (𝕜 := 𝕜) (J w) (A y) ]
      rw [← hv_inner,inner_conj_symm (𝕜 := 𝕜) w v ]
      rw [hw_inner v]
    have hx_Adj : x ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists x ⟨f, hf_inner⟩
    have hf_Adj : A.adjoint ⟨x, hx_Adj⟩ = f := by
      apply LinearPMap.adjoint_apply_eq hA.dense_domain
      exact hf_inner
    rw[← hA_Adj]
    exact ⟨hx_Adj,hf_Adj⟩

-- Inlcusion in completion of the form domain charaterises the extension uniquely.
include hJ_agrees in
theorem positive_friedrichs_unique
    {A B : H →ₗ.[𝕜] H}
    (hSA : S ≤ A)
    (hSB : S ≤ B)
    (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B)
    (hA_domain : ∀ x : A.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H))
    (hB_domain : ∀ x : B.domain,
      ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
        J w = (x : H)) :
    A = B := by
  have hAB (x : A.domain) :
    ∃ hxB : (x : H) ∈ B.domain, B ⟨(x : H), hxB⟩ = A x := by
    have hA_pair := positive_friedrichs_pairing_iff S hsym hpos J hJ_agrees
        hSA hA hA_domain x (A x)
    have hB_pair := positive_friedrichs_pairing_iff S hsym hpos J hJ_agrees
        hSB hB hB_domain x (A x)
    have hA_inner := hA_pair.mp ⟨x.property,rfl⟩
    rcases hB_pair.mpr hA_inner with ⟨hxB,hBx⟩
    use hxB
  have hBA (x : B.domain) :
    ∃ hxA : (x : H) ∈ A.domain, A ⟨(x : H), hxA⟩ = B x := by
    have hB_pair := positive_friedrichs_pairing_iff S hsym hpos J hJ_agrees
        hSB hB hB_domain x (B x)
    have hA_pair := positive_friedrichs_pairing_iff S hsym hpos J hJ_agrees
        hSA hA hA_domain x (B x)
    have hB_inner := hB_pair.mp ⟨x.property,rfl⟩
    rcases hA_pair.mpr hB_inner with ⟨hxA,hAx⟩
    use hxA
  apply le_antisymm
  · constructor
    · intro x hx
      rcases hAB ⟨x, hx⟩ with ⟨hxB, _⟩
      exact hxB
    · intro x y hxy
      rcases hAB x with ⟨hxB, hBx⟩
      rw [← hBx]
      simp only [hxy]
  · constructor
    · intro x hx
      rcases hBA ⟨x, hx⟩ with ⟨hxA, _⟩
      exact hxA
    · intro x y hxy
      rcases hBA x with ⟨hxA, hAx⟩
      rw [← hAx]
      simp only [hxy]

-- Combine existence and uniqueness.
include hS_dense hJ_injective hJ_agrees hJ_dense hJ_bound in
theorem exists_unique_positive_friedrichs_extension :
    ∃! A : H →ₗ.[𝕜] H,
      S ≤ A ∧
      IsSelfAdjoint A ∧
      ∀ x : A.domain,
        ∃ w : UniformSpace.Completion (FormSpace S hsym hpos),
          J w = (x : H) := by
  rcases positive_friedrichs_exists S hsym hpos hS_dense c J
      hJ_injective hJ_agrees hJ_dense hJ_bound with
    ⟨A, hSA, hA, hA_domain, hA_bound⟩
  use A
  constructor
  · exact ⟨hSA, hA, hA_domain⟩
  · rintro B ⟨hSB, hB, hB_domain⟩
    symm
    exact positive_friedrichs_unique S hsym hpos J hJ_agrees
        hSA hSB hA hB hA_domain hB_domain


end PositiveFriedrichsTheorems
/--The shifted operator `S + m` for an operator `S` and a real number `m`-/
def shiftedOperator (S : H →ₗ.[𝕜] H) (m : ℝ) : H →ₗ.[𝕜] H where
  domain := S.domain
  toFun :=
    S.toFun + (m : 𝕜) • S.domain.subtype

/--For symmetric `S` and real `m` the shifted operator `S + m` is symmetric-/
theorem shiftedOperator_isFormalAdjoint
    {S : H →ₗ.[𝕜] H} (m : ℝ)
    (hsym : S.IsFormalAdjoint S) :
    (shiftedOperator S m).IsFormalAdjoint (shiftedOperator S m) := by
  intro u v
  change ⟪S u + (m: 𝕜) • (u : H), (v : H)⟫ = ⟪(u : H), S v + (m : 𝕜) • (v : H)⟫
  rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal]
  rw [inner_add_right, inner_smul_right, add_right_cancel_iff]
  exact hsym u v

/--For desnely defined `S` and real `m` the shifted operator `S + m` is
densely defined-/
theorem shiftedOperator_dense_domain
    {S : H →ₗ.[𝕜] H} (m : ℝ)
    (hS_dense : Dense (S.domain : Set H)) :
    Dense ((shiftedOperator S m).domain : Set H) := hS_dense

/-- For `S` with lower bound `c` and real `m` the shifted operator `S + m`
has lower bound `c + m`. -/
theorem shiftedOperator_lower_bound
    {S : H →ₗ.[𝕜] H} (c m : ℝ)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), S u⟫) :
    ∀ u : (shiftedOperator S m).domain,
     (c + m) * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), shiftedOperator S m u⟫ := by
  intro u
  change (c + m) * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), S u + (m : 𝕜) • (u : H)⟫
  rw [inner_add_right, inner_smul_right, map_add]
  simp [RCLike.mul_re]
  linarith [hbound u]

/-- For `S` with lower bound `c` and `m` with `c + m > 0` the shifted operator `S + m`
is strictly positive. -/
theorem shiftedOperator_positive
    {S : H →ₗ.[𝕜] H} (c m : ℝ) (hcm: 0 < c + m)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), S u⟫) :
    ∀ u : (shiftedOperator S m).domain,
      u ≠ 0 → 0 < RCLike.re ⟪(u : H), shiftedOperator S m u⟫ := by
  intro u hu
  apply lt_of_lt_of_le
  · exact mul_pos hcm (sq_pos_of_pos (norm_pos_iff.mpr hu))
  · exact shiftedOperator_lower_bound c m hbound u

/-- For `S ≤ A` and real `m` the shifted operators satisfy `S + m ≤ A + m`.-/
theorem shiftedOperator_mono
    {S A : H →ₗ.[𝕜] H} (m : ℝ) (hSA : S ≤ A) :
    shiftedOperator S m ≤ shiftedOperator A m := by
  constructor
  · exact hSA.1
  · intro x y hxy
    change S x + (m : 𝕜) • (x : H) = A y + (m : 𝕜) • (y : H)
    rw [hSA.2 hxy, hxy]

/--For densely defined symmetric `S` and real `m` the shifted operator `S + m`
is symmetric.-/
theorem shiftedOperator_adjoint
    [CompleteSpace H]
    {S: H →ₗ.[𝕜] H} (m : ℝ)
    (hS_dense : Dense (S.domain : Set H)) :
    (shiftedOperator S m).adjoint =
      shiftedOperator S.adjoint m := by
    ext u hu hu'
    change u ∈ (shiftedOperator S m).adjoint.domain ↔ u ∈ S.adjoint.domain
    rw [LinearPMap.mem_adjoint_domain_iff_exists]
    rw [LinearPMap.mem_adjoint_domain_iff_exists]
    constructor
    · rintro ⟨w, hw⟩
      use (w - (m : 𝕜) • u)
      intro v
      specialize hw v
      change ⟪w, v⟫ = ⟪u, S v + (m : 𝕜) • v ⟫ at hw
      rw [inner_add_right, inner_smul_right] at hw
      rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal]
      simp [hw]
    · rintro ⟨w, hw⟩
      use (w + (m : 𝕜) • u)
      intro v
      specialize hw v
      change ⟪w + (m : 𝕜) • u, v⟫ = ⟪u, S v + (m : 𝕜) • v⟫
      rw [inner_add_right, inner_smul_right]
      rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal]
      simp [hw]
    · change (shiftedOperator S m).adjoint ⟨u, hu⟩ =
          S.adjoint ⟨u, hu'⟩ + (m : 𝕜) • u
      apply LinearPMap.adjoint_apply_eq (T := shiftedOperator S m) hS_dense
      intro v
      change ⟪S.adjoint ⟨u, hu'⟩ + (m : 𝕜) • u, v⟫ =
        ⟪u, S v + (m : 𝕜) • v⟫
      rw [inner_add_left, inner_smul_left, RCLike.conj_ofReal]
      rw [inner_add_right, inner_smul_right]
      rw [LinearPMap.adjoint_isFormalAdjoint hS_dense ⟨u, hu'⟩ v]

/--For densely defined symmetric `S` and real `m` the shifted operator `S + m`
is symmetric.-/
theorem shiftedOperator_inverse
    (S : H →ₗ.[𝕜] H) (m : ℝ):
    shiftedOperator (shiftedOperator S m) (-m) = S := by
  ext u huS' huS
  · rfl
  · change (S ⟨u, huS'⟩ + (m : 𝕜) • u) + ((-m : ℝ) : 𝕜) • u = S ⟨u, huS⟩
    simp

/--For self-adjoint `A` and real `m` the shifted operator `A + m` is self-adjoint.-/
theorem shiftedOperator_isSelfAdjoint
    [CompleteSpace H]
    {A : H →ₗ.[𝕜] H} (m : ℝ)
    (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (shiftedOperator A m) := by
  rw [LinearPMap.isSelfAdjoint_def, shiftedOperator_adjoint m hA.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp hA]

-- Construct the form space with inner product shifted by `m` with `c + m > 0`.
abbrev SemiboundedFormSpace
    (S : H →ₗ.[𝕜] H) (c m : ℝ) (hcm: 0 < c + m)
    (hsym : S.IsFormalAdjoint S)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), S u⟫) :=
  FormSpace (shiftedOperator S m)
    (shiftedOperator_isFormalAdjoint m hsym)
    (shiftedOperator_positive c m hcm hbound)

/-- The completion of the form domian with respect to the inner product from the shifted operator form
is injectively embedded in `E`-/
theorem exists_semiboundedFormCompletion_inclusion
    [CompleteSpace H]
    (S : H →ₗ.[𝕜] H) (c m : ℝ) (hcm: c + m > 0)
    (hsym : S.IsFormalAdjoint S)
    (hbound : ∀ u : S.domain,
      c * ‖(u : H)‖ ^ 2 ≤ RCLike.re ⟪(u : H), S u⟫) :
    ∃ J : UniformSpace.Completion
        (SemiboundedFormSpace S c m hcm hsym hbound) →L[𝕜] H,
      Function.Injective J ∧
      (∀ u : SemiboundedFormSpace S c m hcm hsym hbound,
        J (u : UniformSpace.Completion
          (SemiboundedFormSpace S c m hcm hsym hbound)) = (u : H)) ∧
      (∀ w : UniformSpace.Completion
          (SemiboundedFormSpace S c m hcm hsym hbound),
        (c + m) * ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2) :=
  exists_positiveFormCompletion_inclusion
    (shiftedOperator S m)
    (shiftedOperator_isFormalAdjoint m hsym)
    (shiftedOperator_positive c m hcm hbound)
    (c + m) hcm
    (shiftedOperator_lower_bound c m hbound)


section SemiboundedFriedrichsTheroems

variable
  [CompleteSpace H]
  (c : ℝ)
  (hcm : 0 < c + (1 - c))
  (hS_dense : Dense (S.domain : Set H))
  (hbound : ∀ u : S.domain,
    c * ‖(u : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (u : H) (S u)))
  (J : UniformSpace.Completion
    (SemiboundedFormSpace S c (1 - c) hcm hsym hbound) →L[𝕜] H)
  (hJ_injective : Function.Injective J)
  (hJ_agrees : ∀ u : SemiboundedFormSpace S c (1 - c) hcm hsym hbound,
    J (u : UniformSpace.Completion
      (SemiboundedFormSpace S c (1 - c) hcm hsym hbound)) = (u : H))
  (hJ_dense : DenseRange J)
  (hJ_bound : ∀ w : UniformSpace.Completion
      (SemiboundedFormSpace S c (1 - c) hcm hsym hbound),
    ‖J w‖ ^ 2 ≤ ‖w‖ ^ 2)

-- Construct an extension using the shift `m = 1 -c`, including its lower bound.
include hS_dense hJ_injective hJ_agrees hJ_dense hJ_bound in
theorem semibounded_friedrichs_exists :
    ∃ A : H →ₗ.[𝕜] H,
      S ≤ A ∧
      IsSelfAdjoint A ∧
      (∀ x : A.domain,
        ∃ w : UniformSpace.Completion
            (SemiboundedFormSpace S c (1 - c) hcm hsym hbound),
          J w = (x : H)) ∧
      (∀ x : A.domain,
        c * ‖(x : H)‖ ^ 2 ≤
          RCLike.re ⟪(x : H), A x⟫) := by
  let m := 1 - c
  rcases positive_friedrichs_exists
      (shiftedOperator S m)
      (shiftedOperator_isFormalAdjoint m hsym)
      (shiftedOperator_positive c m hcm hbound)
      (shiftedOperator_dense_domain m hS_dense)
      1 J hJ_injective hJ_agrees hJ_dense
      (by simpa only [one_mul] using hJ_bound)
    with ⟨A, hSmA, hA, hA_domain, hA_bound⟩
  use shiftedOperator A (-m)
  constructor
  · rw [← shiftedOperator_inverse S m]
    exact shiftedOperator_mono (-m) hSmA
  · constructor
    · exact shiftedOperator_isSelfAdjoint (-m) hA
    · constructor
      · exact hA_domain
      · rw [← show 1+(-m)=c by linarith]
        exact shiftedOperator_lower_bound 1 (-m) hA_bound


end SemiboundedFriedrichsTheroems
end Friedrichs
