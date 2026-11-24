# Friedrichs extension in Lean

This project formalises the Friedrichs extension of a densely defined, semibounded symmetric operator on a real or complex Hilbert space, using Lean 4 and mathlib.

The development is in [Friedrichs.lean](Friedrichs.lean). It is work in progress, with the aim of contributing reusable definitions and results to mathlib.

## Current progress

The existence argument for the strictly positive case has been formalised through:

- Equipping the original operator domain with the form inner product.
- Completing this space and constructing a continuous, injective embedding into the original Hilbert space.
- Using Riesz representation to define the associated operator and transferring it to the original Hilbert space.
- Proving that this operator is self-adjoint, extends the original operator, and preserves the given positive lower bound.

The uniqueness characterisation of the Friedrichs extension in the strictly positive case has been formalised through:

- Establishing that any self-adjoint extension with domain contained in the completed form domain satisfies the inner product identity that defines the Friedrichs extension.
- Proving that any two self-adjoint extensions with domains contained in the completed form domain must coincide.

The existence argument for the semibounded case has been formalised through:

- Establishing elementary results for operators shifted by a real number.
- Shifting the original operator by 1-c to obtain a strictly positive operator.
- Applying the result in the positive case.
- Shifting the resulting extension back, preserving self-adjointness and recovering the original lower bound.

The uniqueness characterisation of the Friedrichs extension in the semibounded case has been formalised through:
- Establishing that any self-adjoint extension with domain contained in the completed form domain (using a shift of 1-c) satisfies the inner product identity that defines the Friedrichs extension.
- Proving that any two self-adjoint extensions with domains contained in the completed form (using a shift of 1-c) domain must coincide.

## Remaining work

- In the semibounded case, establish the independence of the construction on the shift provided the resulting operator is strictly positive.
- Define a named Friedrichs extension with its characterising properties.

## Integration into mathlib

Supporting results are being prepared as separate contributions:

- Characterise membership in the adjoint domain through an inner-product
  representation in `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`: ([PR #45828](https://github.com/leanprover-community/mathlib4/pull/45828)).
- Define the inlcusion map between two nested subspaces as a bundled continuous map in `Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`: ([PR #45828](https://github.com/leanprover-community/mathlib4/pull/45828)).
- Introduce `LinearPMap.IsSymmetric` with basic lemmas.
- Include the result that a densely defined, symmetric, surjective operator is self-adjoint in `LinearPMap.IsSymmetric`.
- Possibly extract the representation theorem for densely defined, closed,
  semibounded Hermitian form in a separate file.


