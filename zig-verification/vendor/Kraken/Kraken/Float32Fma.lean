module

/-!
# Fused multiply-add on `Float32`

Core gives `Float32` a logical model: `Float32.Model` unpacks to
`Float.Model.UnpackedFloat`, and each operation computes the exact result there
and rounds it once. Core has no fused multiply-add. `Kraken.Float32.fma a b c`
is `a * b + c` rounded once, built from the model's own parts: the product is
kept exact, and the model's addition rounds the exact sum.

It is a plain definition, with no `extern`, so the compiled test runner
executes the model too, and the hardware tests
(`Kraken/X64/Test/asm/test_avx_fma.S`) check it against the processor.
-/

namespace Kraken.Float32

open Float.Model

/-- The exact product of two unpacked floats: the model's multiplication
without its final rounding. It is meant only as an intermediate. -/
def mulExact : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity s₁, .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity s₁, .finite s₂ .. => .infinity (s₁ * s₂)
  | .finite s₁ .., .infinity s₂ => .infinity (s₁ * s₂)
  | .infinity _, .zero _ => .notANumber
  | .zero _, .infinity _ => .notANumber
  | .finite s₁ .., .zero s₂ => .zero (s₁ * s₂)
  | .zero s₁, .finite s₂ .. => .zero (s₁ * s₂)
  | .zero s₁, .zero s₂ => .zero (s₁ * s₂)
  | .finite s₁ m₁ e₁ h₁, .finite s₂ m₂ e₂ h₂ =>
    .finite (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) (Nat.mul_pos h₁ h₂)

/-- `a * b + c`, rounded once to `spec`. The model's addition returns a nonzero
operand unchanged when the other one is zero. That is right for a rounded
operand but not for the exact product, so this case rounds the product
itself. -/
def fmaUnpacked (spec : Format) (a b c : UnpackedFloat) : UnpackedFloat :=
  match mulExact a b, c with
  | .finite s m e _, .zero _ => UnpackedFloat.round spec s m e
  | p, c => UnpackedFloat.add spec p c

/-- Fused multiply-add: `a * b + c` with a single rounding (to nearest, ties to
even), as the x86 `vfmadd` instructions compute it. As with the other
`Float32` operations, a NaN result is the model's canonical NaN, while the
processor returns its own default NaN or propagates a payload. -/
public def fma (a b c : _root_.Float32) : _root_.Float32 :=
  .ofModel (_root_.Float32.Model.pack
    (fmaUnpacked Format.binary32 a.toModel.unpack b.toModel.unpack c.toModel.unpack))

end Kraken.Float32
